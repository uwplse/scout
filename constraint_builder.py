from z3 import *
import shapes
import math
import time
import smtlib_builder as cb
import columnizer as columnizer
import size_constraint_helpers 

CANVAS_HEIGHT = 640
CANVAS_WIDTH = 360
IGNORED_VALUE_CONSTRAINTS = ["baseline", "canvas_alignment", "extra_in_first", "size_combo", "grid_layout", "size_factor",
							 "outside_padding"]
IGNORED_PREVIOUS_SOLUTION_CONSTRAINTS = ["baseline", "extra_in_first", "size_combo", "grid_layout", "canvas_alignment"]

def abs(x):
	return If(x>=0,x,-x)

class ConstraintBuilder(object):
	def __init__(self, solver): 
		# So we can override the add method for debugging
		""" Class to build up set of constraints for HLC and basic design quality.

			Attributes: 
				solver: Solver instance object
				constraints: String that will be built up to pass to the solver containing SMT lib constraint expressions
				decl_constraints: String that will contain the variable declarations 
		"""
		self.solver = solver
		self.constraints = "(set-info :source | Python ftw |)\n"
		self.decl_constraints = ""

	def load_constraints(self): 
		""" Loads the set of constraints into a set of assertions into the solver """ 
		const = self.decl_constraints + self.constraints
		self.solver.load_constraints(const)		

	def declare_variables(self, shapes): 
		""" Create variable declaration statements for each of the variables on each shape """ 
		for shape in shapes.values(): 
			for key, val in shape.variables.items():
				self.decl_constraints += cb.declare(val.id, val.type)

	def init_previous_solution_constraints(self, previous_solutions, shapes): 
		""" Create statements for negating the value combinations for each of the previous solutions """ 
		# Saved solutions should not appear again in the results
		for solution in previous_solutions:
			elements = solution["elements"]
			if (not "added" in solution and not "removed" in solution) or (not len(solution["added"]) and not len(solution["removed"])):
				self.get_previous_solution_constraints_from_elements(shapes, elements, solution["id"])

	def get_solution_variable_declarations(self, element_tree, shapes):
		""" Build varaible declaration statements for each shape """
		declarations = ""
		element_id = element_tree['name']

		# Get the shape corresponding to the element name
		shape = shapes[element_id]
		variables = shape.variables.toDict()
		for variable_key in variables.keys(): 
			variable = variables[variable_key]
			declarations += cb.declare(variable.id, variable.type)

		if 'children' in element_tree: 
			for child in element_tree['children']: 
				declarations += self.get_solution_variable_declarations(child, shapes)

		return declarations

	def get_previous_solution_variable_values(self, element_tree, shapes, value_constraints=[]):
		""" Get the previous solution value constraints used for preventing a previous solution from appearing again in the set """
		element_id = element_tree['name']

		# Get the shape corresponding to the element name
		shape = shapes[element_id]
		variables = shape.variables.toDict()
		if shape.type == "leaf":
			for variable_key in variables.keys():
				variable = variables[variable_key]
				if variable.name not in IGNORED_PREVIOUS_SOLUTION_CONSTRAINTS:
					variable_value = variable.get_value_from_element(element_tree)
					value_constraints.append(cb.eq(variable.id,
											str(variable_value)))
		if 'children' in element_tree:
			for child in element_tree['children']:
				self.get_previous_solution_variable_values(child, shapes, value_constraints)


	def get_previous_solution_constraints_from_elements(self, shapes, element_tree, solutionID):
		""" Get the previous solution value constraint to prevent this solution from appearing again """
		value_constraints = []
		self.get_previous_solution_variable_values(element_tree, shapes, value_constraints)

		# Prevent the exact same set of values from being produced again (Not an And on all of the constraints)
		self.constraints += cb.assert_expr(cb.not_expr(cb.and_expr(value_constraints)),
			"prevent_previous_solution_" + solutionID + "_values")

	def get_variable_value_constraints(self, element_tree, shapes, value_constraints):
		""" Get the value constraints for a given element tree """
		element_id = element_tree['name']

		# Get the shape corresponding to the element name
		shape = shapes[element_id]

		variables = shape.variables.toDict()
		for variable_key in variables.keys(): 
			variable = variables[variable_key]
			self.decl_constraints += cb.declare(variable.id, variable.type)
			if variable.name not in IGNORED_VALUE_CONSTRAINTS:
				variable_value = variable.get_value_from_element(element_tree)
				if variable_value != None: 
					value_constraints.append(cb.eq(variable.id, 
						str(variable_value)))

		if 'children' in element_tree: 
			for child in element_tree['children']:
				self.get_variable_value_constraints(child, shapes, value_constraints)

	def init_solution_constraints(self, shapes, element_tree, solutionID):
		""" Initialize the constraints for a given solution """
		value_constraints = []
		self.get_variable_value_constraints(element_tree, shapes, value_constraints)
		constraints = cb.assert_expr(cb.and_expr(value_constraints), "fix_solution_" + solutionID + "_values")

		# Return the declarations and constraints so they can be loaded in after the intial initialization of the base constraints
		declarations = self.get_solution_variable_declarations(element_tree, shapes)
		return declarations + constraints

	def init_shape_baseline(self, shape): 
		""" Initialize the baseline constraint for a shape """ 
		if shape.has_baseline:
			self.constraints += cb.eq(shape.variables.baseline.id, 
				cb.add(shape.variables.y.id, shape.orig_baseline), "baseline_" + shape.shape_id)

	def init_shape_alternate(self, shape): 	
		""" Initialize the alternate constraints for a shape """	
		if shape.is_alternate: 
			alternate_values = []
			alternate = shape.variables.alternate
			for alt_value in shape.variables.alternate.domain:
				alternate_values.append(cb.eq(alternate.id, '"' + alt_value + '"'))

			self.constraints += cb.assert_expr(cb.or_expr(alternate_values), "container_"
				+ shape.shape_id + "_alternate_in_domain")

	def init_shape_bounds(self, shape):
		""" Create constraints that keep a shape inside the bounds of the canvas """ 
		self.constraints += cb.assert_expr(cb.gte(shape.variables.x.id, "0"), "shape_" + shape.shape_id + "_x_gt_zero")
		self.constraints += cb.assert_expr(cb.lte(cb.add(shape.variables.x.id, str(shape.computed_width())), 
			str(CANVAS_WIDTH)), "shape_" + shape.shape_id + "_right_lt_width")
		self.constraints += cb.assert_expr(cb.gte(shape.variables.y.id, "0"), "shape_" + shape.shape_id + "_y_gt_zero")
		self.constraints += cb.assert_expr(cb.lte(cb.add(shape.variables.y.id, str(shape.computed_height())), 
			str(CANVAS_HEIGHT)), "shape_" + shape.shape_id + "_bottom_lt_height")

	def init_high_emphasis(self, shape, shapes):
		""" Create constraints for high emphasis behavior """
		for other_shape in shapes: 
			if shape.shape_id != other_shape.shape_id and other_shape.shape_id != "canvas":
				# Emphasis shape has lower y coordinate, unless the other shape also has high emphasis 
				if other_shape.importance != "high" and other_shape.type == "leaf": 
					lower_y = cb.lte(shape.variables.y.id, other_shape.variables.y.id)
					# self.constraints += cb.assert_expr(lower_y, "shape_" + shape.shape_id + "_high_emphasis_leq_y_" + other_shape.shape_id)	

					shp_height = str(shape.computed_height())
					other_shp_height = str(other_shape.computed_height())

					shp_width = str(shape.computed_width())
					other_shp_width = str(other_shape.computed_width())

					wider = cb.gte(shp_width, other_shp_width)
					taller = cb.gte(shp_height, other_shp_height)

					all_emph_cons = [wider, taller]
					self.constraints += cb.assert_expr(cb.or_expr(all_emph_cons), "shape_" + shape.shape_id 
						+ "_other_shape_" + other_shape.shape_id + "_high_emphasis")

					# Shoudl appear before another shape if the other shep has a larger area 
					shp_area = cb.mult(shp_height, shp_width)
					other_shp_area = cb.mult(other_shp_height, other_shp_width)

					appear_before_smaller_area = cb.ite(cb.lte(shp_area, other_shp_area), lower_y, "true")
					self.constraints += cb.assert_expr(appear_before_smaller_area, "shape_" + shape.shape_id + 
						"_other_shape_" + other_shape.shape_id + "_appear_before_shape_if_smaller_area")

	def init_low_emphasis(self, shape, shapes): 
		""" Create constraints for low emphasis behavior """
		for other_shape in shapes: 
			if shape.shape_id != other_shape.shape_id and other_shape.shape_id != "canvas":
				# Emphasis shape has lower y coordinate, unless the other shape also has low emphasis 
				if other_shape.importance != "low" and other_shape.type == "leaf": 
					shp_height = str(shape.computed_height())
					other_shp_height = str(shape.computed_height())

					shp_width = str(shape.computed_width())
					other_shp_width = str(other_shape.computed_width())

					skinnier = cb.lte(shp_width, other_shp_width)
					shorter = cb.lte(shp_height, other_shp_height)

					higher_y = cb.gte(cb.add(shape.variables.y.id, shp_height), cb.add(other_shape.variables.y.id, other_shp_height))
					all_emph_cons = [skinnier, shorter]
					self.constraints += cb.assert_expr(cb.or_expr(all_emph_cons), "shape_" + shape.shape_id + "_other_shape_" 
						+ other_shape.shape_id + "_low_emphasis")				

					# Shoudl appear before another shape if the other shep has a larger area 
					shp_area = cb.mult(shp_height, shp_width)
					other_shp_area = cb.mult(other_shp_height, other_shp_width)

					appear_after_smaller_area = cb.ite(cb.gte(shp_area, other_shp_area), higher_y, "true")
					self.constraints += cb.assert_expr(appear_after_smaller_area, "shape_" + shape.shape_id + 
						"_other_shape_" + other_shape.shape_id + "_appear_after_shape_if_smaller_area")

	def init_canvas_constraints(self, canvas): 
		""" create canvas constraints, such as layout grid, alignment, padding, baseline grid and order """
		canvas_x = canvas.variables.x
		canvas_y = canvas.variables.y
		margin = canvas.variables.margin

		# Fix the canvas X,Y to their original valuess
		self.constraints += cb.assert_expr(cb.eq(canvas_x.id, str(canvas.x)), 'canvas_orig_x')
		self.constraints += cb.assert_expr(cb.eq(canvas_y.id, str(canvas.y)), 'canvas_orig_y')

		# Enforce children constraints for direct children of the canvas. 
		child_shapes = canvas.children
		if len(child_shapes): 
			for s_index in range(0, len(child_shapes)): 
				shape1 = child_shapes[s_index]
				shape1_x = shape1.variables.x.id
				shape1_y = shape1.variables.y.id
				shape1_width = str(shape1.computed_width())
				shape1_height = str(shape1.computed_height())

				# Text shapes have a baseline, so place the bottom axis as their baseline so they sit on the grid line. 
				bottom_axis = shape1.variables.baseline.id if shape1.has_baseline else cb.add(shape1_y, shape1_height)

				# Shapes cannot exceed the bounds of the canvas. 
				self.constraints += cb.assert_expr(cb.gte(shape1_x, cb.add(canvas_x.id, margin.id)),
					"child_shape_" + shape1.shape_id + "_within_parent_container_" + canvas.shape_id + "_left")
				self.constraints += cb.assert_expr(cb.gte(shape1_y, cb.add(canvas_y.id, margin.id)),
					"child_shape_" + shape1.shape_id + "_within_parent_container_" + canvas.shape_id + "_top")
				
				self.constraints += cb.assert_expr(cb.lte(cb.add(shape1_x, shape1_width),
					cb.add(canvas_x.id, cb.sub(str(canvas.computed_width()), margin.id))),
					"child_shape_" + shape1.shape_id + "_lt_parent_width")
				self.constraints += cb.assert_expr(cb.lte(bottom_axis,
					cb.add(canvas_y.id, cb.sub(str(canvas.computed_height()), margin.id))),
					"child_shape_" + shape1.shape_id + "_lt_parent_height")

				# Initialize size constraints 
				if shape1.type == "leaf":
					self.init_size(shape1, canvas)

		# Other remaining constraints 
		self.init_layout_grid(canvas)
		self.align_canvas_layout_grid(canvas)
		self.init_baseline_grid(canvas)
		self.layout_canvas_baseline_grid(canvas)
		self.canvas_padding(canvas)
		self.canvas_order(canvas)

	def layout_canvas_baseline_grid(self, canvas): 
		""" Create baseline grid constraints for the canvas object """
		canvas_baseline_grid = canvas.variables.baseline_grid

		# Enforce children constraints
		child_shapes = canvas.children
		if len(child_shapes): 
			for child_index in range(0, len(child_shapes)): 
				child = child_shapes[child_index]

				child_y = child.variables.y 
				vertical_pos = child.variables.baseline if child.has_baseline else child_y

				# Enforce that the child position (baseline or y) is a multiple of the baseline grid constaint
				self.constraints += cb.assert_expr(cb.eq(cb.mod(vertical_pos.id, canvas_baseline_grid.id), "0"), 
					"canvas_child_" + child.shape_id + "_y_position_mult_baseline_grid") 

				# Enforce that the child height is a multiple of the baseline grid variable
				# child_height = child.variables.height
				# self.constraints += cb.assert_expr(cb.eq(cb.mod(child_height.id, canvas_baseline_grid.id), "0"), 
				# 	"canvas_child_" + child.shape_id + "_height_mult_baseline_grid")

	def init_layout_grid(self, canvas): 
		""" Constraints to set the domain of layout grid variables on the canvas """ 
		columns = canvas.variables.columns
		gutter_width = canvas.variables.gutter_width
		column_width = canvas.variables.column_width
		margin = canvas.variables.margin

		grid_values = []
		num_values = len(columns.domain)
		for i in range(0, num_values): 
			col_value = columns.domain[i]
			gutter_value = gutter_width.domain[i]
			column_width_value = column_width.domain[i]
			marg_value = margin.domain[i]

			and_all = cb.and_expr([cb.eq(columns.id, str(col_value)), cb.eq(gutter_width.id, str(gutter_value)),
				cb.eq(column_width.id, str(column_width_value)), cb.eq(margin.id, str(marg_value))])
			grid_values.append(and_all)

		const = cb.or_expr(grid_values) if len(grid_values) > 1 else grid_values[0]

		self.constraints += cb.assert_expr(const, "canvas_layout_grid_variables_in_domain")

	def init_baseline_grid(self, canvas): 
		""" Constraints to set the domain of the baseline grid variables on the canvas """ 
		grid = canvas.variables.baseline_grid
		grid_values = []
		for grid_value in grid.domain:
			grid_values.append(cb.eq(grid.id, str(grid_value)))

		const = cb.or_expr(grid_values) if len(grid_values) > 1 else grid_values[0]
		self.constraints += cb.assert_expr(const, "canvas_baseline_grid_in_domain")

	def init_container_constraints(self, container, shapes, canvas):
		""" Constraints for a container on the canvas (group of elements) 
	
			Parameters: 
				container: The ContainerShape object 
				shapes: List of all shapes on canvas 
				canvas: The CanvasShape object 
		""" 
		arrangement = container.variables.arrangement.id
		alignment = container.variables.alignment.id
		group_alignment = container.variables.group_alignment.id
		padding = container.variables.padding.id
		container_x = container.variables.x.id
		container_y = container.variables.y.id

		# Limit domains to the set of variable values
		self.constraints += cb.assert_expr(cb.gte(arrangement, "0"), "container_" + container.shape_id + "_arrangement_gt_0")
		self.constraints += cb.assert_expr(cb.lt(arrangement, str(len(container.variables.arrangement.domain))),
			"container_" + container.shape_id + "_arrangement_lt_domain" )
		self.constraints += cb.assert_expr(cb.gte(alignment, "0"), "container_" + container.shape_id + "_alignment_gt_0")
		self.constraints += cb.assert_expr(cb.lt(alignment, str(len(container.variables.alignment.domain))),
			"container_" + container.shape_id + "_alignment_lt_domain")
		self.constraints += cb.assert_expr(cb.gte(group_alignment, "0"), "container_" + container.shape_id + "_group_alignment_gt_0")
		self.constraints += cb.assert_expr(cb.lt(group_alignment, str(len(container.variables.group_alignment.domain))))

		# These two variables do not have variable values that correspond to an index 
		# so create an OR constraint instead
		padding_values = []
		for pad_value in container.variables.padding.domain:
			padding_values.append(cb.eq(padding, str(pad_value)))

		self.constraints += cb.assert_expr(cb.or_expr(padding_values), "container_"
			+ container.shape_id + "_padding_in_domain")

		# Outside padding variable should be >= 0 
		if container.at_root: 
			outside_padding = container.variables.outside_padding.id
			canvas_width = str(canvas.computed_width())
			self.constraints += cb.assert_expr(cb.gte(outside_padding, "0"), "container_" + container.shape_id + "_outside_padding_gt_0")
			self.constraints += cb.assert_expr(cb.lte(outside_padding, canvas_width), "container_" + container.shape_id + "_outside_padding_lt_canvas_width")

		# Enforce children constraints
		child_shapes = container.children
		if len(child_shapes): 
			has_group = False
			for s_index in range(0, len(child_shapes)): 
				shape1 = child_shapes[s_index]
				if shape1.type == "container": 
					# Enforce that the child container padding value is smaller than the padding of the parent container
					# Of the parent container so that they are more likely to appear as a cohesive element
					self.constraints += cb.assert_expr(cb.lt(shape1.variables.padding.id, container.variables.padding.id), 
						"child_shape_" + shape1.shape_id + "_padding_wt_group_lt_parent_padding_" + container.shape_id)

				shape1_x = shape1.variables.x.id
				shape1_y = shape1.variables.y.id
				shape1_width = str(shape1.computed_width())
				shape1_height = str(shape1.computed_height())

				bottom_axis = shape1.variables.baseline.id if shape1.has_baseline else cb.add(shape1_y, shape1_height)

				# Shapes cannot exceed the bounds of their parent containers
				self.constraints += cb.assert_expr(cb.gte(shape1_x, container_x), 
					"child_shape_" + shape1.shape_id + "_within_parent_container_" + container.shape_id + "_left")
				self.constraints += cb.assert_expr(cb.gte(shape1_y, container_y), 
					"child_shape_" + shape1.shape_id + "_within_parent_container_" + container.shape_id + "_top")

				self.constraints += cb.assert_expr(cb.lte(cb.add(shape1_x, shape1_width), 
					cb.add(container_x, str(container.computed_width()))),
					"child_shape_" + shape1.shape_id + "_lt_parent_width")
				self.constraints += cb.assert_expr(cb.lte(bottom_axis, 
					cb.add(container_y, str(container.computed_height()))),
					"child_shape_" + shape1.shape_id + "_lt_parent_height")

				# Create importance level constraints
				if shape1.type == "leaf": 
					self.init_size(shape1, container)

			spacing = container.variables.padding.id
			# Remaining constraints for arrangment, alignment, non-overlapping, and size change within a container. 
			self.arrange_container(container, spacing)
			self.align_container(container, spacing)
			self.non_overlapping(container, spacing)
			self.same_size_change(container)

			if container.typed: ## Repeat group corresponds to 'typed'
				# If this is a typed container, enforce all variables on child containers to be the same
				self.init_repeat_group(container, shapes)

	def init_size(self, shape, container): 
		""" Initialize domain of size constraints on an element. Sizes have already been precomputed 
			When shapes get initialized """ 
		size_factors = shape.variables.size_factor.domain
		size_combos = []
		for i in range(0, len(size_factors)):
			height = cb.eq(shape.variables.height.id, str(shape.variables.height.domain[i]))
			width = cb.eq(shape.variables.width.id, str(shape.variables.width.domain[i]))
			factor = cb.eq(shape.variables.size_factor.id, str(size_factors[i]))
			size_combos.append(cb.and_expr([height, width, factor]))

		const = cb.or_expr(size_combos) if len(size_combos) else "false"
		self.constraints += cb.assert_expr(const, "shape_" + shape.shape_id + "_size_domains")

	def init_repeat_group(self, container, shapes): 
		""" Create constraints for a repeat group (container.typed = True) """
		subgroups = container.children
		all_same_values = []

		for i in range(0, len(subgroups)): 
			if i < len(subgroups) - 1: 
				group1 = subgroups[i]
				group2 = subgroups[i+1]
				
				group1_variables = group1.variables.toDict()
				group2_variables = group2.variables.toDict()

				group1_keys = list(group1_variables.keys())
				group2_keys = list(group2_variables.keys())

				for j in range(0, len(group1_keys)): 
					group1_key = group1_keys[j]
					group2_key = group2_keys[j]
					group1_variable = group1_variables[group1_key]
					group2_variable = group2_variables[group2_key]

					groups_same = cb.eq(group1_variable.id, group2_variable.id)

					if group1_key != "x" and group1_key != "y" and group1_key != "width" and group1_key != "height": 
						if j < len(all_same_values): 
							all_same_values[j].append(groups_same)
						else: 
							all_same_values.append([groups_same])

		for i in range(len(all_same_values)): 
			all_same_variables = all_same_values[i] 
			# For each collection of child variable values for a variable
			# Enforce all values for that variable to be thes ame 
			self.constraints += cb.assert_expr(cb.and_expr(all_same_variables), 
				"repeat_group_variables_all_same_" + str(i))

		# Corresponding elements within subgroups should have the same size decrease or increase. 
		for group in subgroups: 
			group_children = group.children 
			for i in range(0, len(group_children)): 
				child = group_children[i]

				for j in range(0, len(child.correspondingIDs)): 
					child_corrID = child.correspondingIDs[j]
					child_corr_shape = shapes[child_corrID]

					# Keep size factors equal. 
					self.constraints += cb.assert_expr(cb.eq(child.variables.size_factor.id,
															 child_corr_shape.variables.size_factor.id),
						"repeat_group_child_" + child.shape_id + "_and_child_" + child_corr_shape.shape_id + "_size_factor_equal")

					# Keep the alternate representation the same, if the two children are both alternate groups
					if child.is_alternate and child_corr_shape.is_alternate:
						self.constraints += cb.assert_expr(cb.eq(child.variables.alternate.id,
																 child_corr_shape.variables.alternate.id),
														   "repeat_group_child_" + child.shape_id + "_and_child_"
														   + child_corr_shape.shape_id + "_alternate_representation_equal")


		# The order of the elements within the groups should be uniform
		for group in subgroups:
			group_children = group.children
			for i in range(0, len(group_children)):
				for j in range(0, len(group_children)): 
					if i != j:
						child1 = group_children[i]
						child2 = group_children[j]
						child1_left = cb.lt(cb.add(child1.variables.x.id, str(child1.computed_width())), 
							child2.variables.x.id)
						child1_above = cb.lt(cb.add(child1.variables.y.id, str(child1.computed_height())), 
						 	child2.variables.y.id)
						child1_left_or_above = cb.or_expr([child1_left, child1_above])
				
						for k in range(0, len(child1.correspondingIDs)):
							child1_corrID = child1.correspondingIDs[k]
							child2_corrID = child2.correspondingIDs[k]
							child1_corr_shape = shapes[child1_corrID]
							child2_corr_shape = shapes[child2_corrID]
				
							child1_corr_left = cb.lt(cb.add(child1_corr_shape.variables.x.id, str(child1_corr_shape.computed_width())),
								child2_corr_shape.variables.x.id)
							child1_corr_above = cb.lt(cb.add(child1_corr_shape.variables.y.id, str(child1_corr_shape.computed_height())), 
								child2_corr_shape.variables.y.id)
							child1_corr_left_or_above = cb.or_expr([child1_corr_left, child1_corr_above])

							child2_corr_left = cb.lt(cb.add(child2_corr_shape.variables.x.id, str(child2_corr_shape.computed_width())),
								child1_corr_shape.variables.x.id)
							child2_corr_above = cb.lt(cb.add(child2_corr_shape.variables.y.id, str(child2_corr_shape.computed_height())), 
								child1_corr_shape.variables.y.id)
							child2_corr_left_or_above = cb.or_expr([child2_corr_left, child2_corr_above])

							order_pair = cb.ite(child1_left_or_above, child1_corr_left_or_above, child2_corr_left_or_above)
							self.constraints += cb.assert_expr(order_pair, 
								"container_" + container.shape_id + "_group_" + group.shape_id + "_enforce_subgroup_order")

	def init_locks(self, shape): 
		# Add constraints for all of the locked properties to set those values to a fixed value. 
		if shape.locks is not None: 
			for lock in shape.locks:
				exprs = []
				for value in shape.keep_values[lock]: 
					value = str(value)
					if shape.variables[lock].type == "String": 
						value = "\"" + value + "\""

					exprs.append(cb.eq(shape.variables[lock].id, value))

				if len(exprs) > 1: 
					self.constraints += cb.assert_expr(cb.or_expr(exprs),
						"lock_" + shape.shape_id + "_" + shape.variables[lock].name + "_" + str(shape.keep_values[lock])) 				
				elif len(exprs) == 1: 
					expr = exprs[0] 
					self.constraints += cb.assert_expr(expr,
						"lock_" + shape.shape_id + "_" + shape.variables[lock].name + "_" + str(shape.keep_values[lock])) 	

	def init_prevents(self, shape): 
		# Add constraints for all of the locked properties to prevent those values from being assigned. 
		if shape.prevents is not None: 
			for prevent in shape.prevents:
				exprs = []
				for value in shape.prevent_values[prevent]: 
					value = str(value)
					if shape.variables[prevent].type == "String": 
						value = "\"" + value + "\""

					exprs.append(cb.neq(shape.variables[prevent].id, value))

				if len(exprs) > 1: 
					self.constraints += cb.assert_expr(cb.and_expr(exprs),
						"prevent_" + shape.shape_id + "_" + shape.variables[prevent].name + "_" + str(shape.prevent_values[prevent])) 				
				elif len(exprs) == 1: 
					expr = exprs[0] 
					self.constraints += cb.assert_expr(expr,
						"prevent_" + shape.shape_id + "_" + shape.variables[prevent].name + "_" + str(shape.prevent_values[prevent])) 

	def non_overlapping(self, container, spacing): 
		""" Prevent overlap within a container. 

			Parameters: 
				container: A ContainerShape object 
				spacing: An int value for the amount of space between elements in addition to non-overlapping (margin)
		"""
		child_shapes = container.children 
		for i in range(0, len(child_shapes)):
			for j in range(0, len(child_shapes)): 
				if i != j: 
					shape1 = child_shapes[i]
					shape2 = child_shapes[j]
					shape1_x = shape1.variables.x.id
					shape1_y = shape1.variables.y.id
					shape2_x = shape2.variables.x.id
					shape2_y = shape2.variables.y.id
					shape1_width = str(shape1.computed_width())
					shape1_height = str(shape1.computed_height())
					shape2_width = str(shape2.computed_width())
					shape2_height = str(shape2.computed_height())

					# Non-overlapping
					left = cb.lte(cb.add(shape1_x, cb.add(shape1_width, spacing)), shape2_x)
					right = cb.lte(cb.add(cb.add(shape2_x, shape2_width),  spacing), shape1_x)
					top = cb.lte(cb.add(cb.add(shape1_y, shape1_height), spacing), shape2_y)
					bottom = cb.lte(cb.add(cb.add(shape2_y, shape2_height), spacing), shape1_y)
					self.constraints += cb.assert_expr(cb.or_expr([left,right,top,bottom]), 
						"non_overlapping_shapes_" + shape1.shape_id + "_" + shape2.shape_id)


	def bottom_edge_above(self, shape1_y, shape1_height, shape2_y, shape2_height): 
		""" Create constraint that bottom edge of shape 1 should be above bottom edge of shape 2. """
		bedge1 = cb.add(shape1_y, shape1_height) 
		bedge2 = cb.add(shape2_y, shape2_height)
		return cb.lt(bedge1, bedge2)

	def canvas_order(self, canvas): 
		""" Create ordering constraints for the canvas if the order is important. 

			Additionally set the 'first' and 'last' element constraints if they have been set. 

		"""
		child_shapes = canvas.children 
		num_shapes = len(child_shapes)
		for i in range(0, num_shapes-1):
			shape1 = child_shapes[i]
			shape2 = child_shapes[i+1]
			shape1_y = shape1.variables.y.id
			shape2_y = shape2.variables.y.id
			shape1_height = str(shape1.computed_height())
			shape2_height = str(shape2.computed_height())
			
			# Enforce that the element are kept in the specified order on the canvas 
			# If the order is important, shape2 should have its bottom edge lower than shape1
			if canvas.container_order == "important": 
				bedge_lower = self.bottom_edge_above(shape1_y, shape1_height, shape2_y, shape2_height)
				self.constraints += cb.assert_expr(bedge_lower, 
					"canvas_order_important_" + shape2.shape_id + "_right_or_bottom_to_" + shape1.shape_id)


		for i in range(0, num_shapes):
			last_in_order = []
			first_in_order = []
			for j in range(0, num_shapes):
				if j != i: 
					shape1 = child_shapes[i]
					shape2 = child_shapes[j]
					shape1_y = shape1.variables.y.id
					shape2_y = shape2.variables.y.id
					shape1_height = str(shape1.computed_height())
					shape2_height = str(shape2.computed_height())

					if i == 0 and shape1.order == 0: 
						# Enforce that all j shapes have a bottom edge lower
						bedge_above = self.bottom_edge_above(shape1_y, shape1_height, shape2_y, shape2_height)
						first_in_order.append(bedge_above)
					if i == (num_shapes - 1) and shape1.order == (num_shapes-1): 
						# Enforce that all j shapes have a higher bottom edge
						bedge_below = self.bottom_edge_above(shape2_y, shape2_height, shape1_y, shape1_height)
						last_in_order.append(bedge_below)

			if len(first_in_order): 
				self.constraints += cb.assert_expr(cb.and_expr(first_in_order), 
					"canvas_order_first_" + shape1.shape_id + "_is_first")

			if len(last_in_order): 
				self.constraints += cb.assert_expr(cb.and_expr(last_in_order), 
					"canvas_order_last_" + shape1.shape_id + "_is_last")

	def canvas_padding(self, canvas): 
		# Enforce padding between elements that is greater than the padding inside the groups on the canvas. 
		child_shapes = canvas.children 
		for i in range(0, len(child_shapes)):
			for j in range(0, len(child_shapes)): 
				if i != j: 
					shape1 = child_shapes[i]
					shape2 = child_shapes[j]
					shape1_x = shape1.variables.x.id
					shape1_y = shape1.variables.y.id
					shape2_x = shape2.variables.x.id
					shape2_y = shape2.variables.y.id
					shape1_width = str(shape1.computed_width())
					shape1_height = str(shape1.computed_height())
					shape2_width = str(shape2.computed_width())
					shape2_height = str(shape2.computed_height())

					# Enforce that the padding used for spacing the elements on the canvas is greater than 
					# the minimum or greater than the padding in the groups that are being spaced to maintain
					# visual separation. /
					spacing = canvas.min_spacing
					if shape1.is_container and shape2.is_container: 
						spacing = cb.ite(cb.gt(shape1.variables.padding.id, shape2.variables.padding.id), 
							shape1.variables.padding.id, shape2.variables.padding.id)
						spacing = cb.mult("2", spacing)
					elif shape1.is_container: 
						spacing = shape1.variables.padding.id
						spacing = cb.mult("2", spacing)
					elif shape2.is_container: 
						spacing = shape2.variables.padding.id
						spacing = cb.mult("2", spacing)

					# Non-overlapping
					left = cb.lt(cb.add(shape1_x, cb.add(shape1_width, spacing)), shape2_x)
					right = cb.lt(cb.add(cb.add(shape2_x, shape2_width),  spacing), shape1_x)
					top = cb.lt(cb.add(cb.add(shape1_y, shape1_height), spacing), shape2_y)
					bottom = cb.lt(cb.add(cb.add(shape2_y, shape2_height), spacing), shape1_y)
					self.constraints += cb.assert_expr(cb.or_expr([left,right,top,bottom]), 
						"non_overlapping_shapes_" + shape1.shape_id + "_" + shape2.shape_id)

	def same_size_change(self, container):
		""" if shapes are the same time within a container, they must increase or decrease by the same amount in size. """
		size_equals = [] 
		child_shapes = container.children 
		for i in range(0, len(child_shapes)):
			for j in range(0, len(child_shapes)): 
				if i != j: 
					shape1 = child_shapes[i]
					shape2 = child_shapes[j]
					# Shapes must increase or decrease inside a group by the same amount
					# If they are the same shape type. 
					if shape1.type == "leaf" and shape2.type == "leaf" and shape1.semantic_type == shape2.semantic_type:
						size_eq = cb.eq(shape1.variables.size_factor.id, shape2.variables.size_factor.id)
						size_equals.append(size_eq)

		if len(size_equals):
			self.constraints += cb.assert_expr(cb.and_expr(size_equals),
				"container_" + container.shape_id + "_size_factor_children_equal")

	def align_canvas_layout_grid(self, canvas):
		""" Create alignment constraints for the canvas child elements to align elements to right columns """
		layout_columns = canvas.variables.columns
		gutter_width = canvas.variables.gutter_width
		column_width = canvas.variables.column_width
		margin = canvas.variables.margin
		canvas_x = canvas.variables.x
		canvas_width = str(canvas.computed_width())

		# Enforce children constraints
		child_shapes = canvas.children
		if len(child_shapes): 
			for child_index in range(0, len(child_shapes)): 
				child = child_shapes[child_index]
				
				child_left_column = child.variables.left_column
				child_right_column = child.variables.right_column 
				child_canvas_alignment = child.variables.canvas_alignment

				# Enforce the child column domain values
				left_column_values = []
				for col_value in child_left_column.domain: 
					col_eq = cb.eq(child_left_column.id, str(col_value))
					left_column_values.append(col_eq)
				self.constraints += cb.assert_expr(cb.or_expr(left_column_values),
					"shape_" + child.shape_id + "_left_layout_column_value")

				right_column_values = []
				for col_value in child_right_column.domain: 
					col_eq = cb.eq(child_right_column.id, str(col_value))
					right_column_values.append(col_eq)
				self.constraints += cb.assert_expr(cb.or_expr(right_column_values),
					"shape_" + child.shape_id + "_right_layout_column_value")

				canvas_alignment_values = []
				self.constraints += cb.assert_expr(cb.gte(child_canvas_alignment.id, "0"), "shape_" + child.shape_id + "_canvas_alignment_gt_0")
				self.constraints += cb.assert_expr(cb.lt(child_canvas_alignment.id, str(len(child_canvas_alignment.domain))),
					"shape_" + child.shape_id + "_canvas_alignemnt_lt_domain" )

				# Enforce that the child column value is less than the canvas column amount
				left_column_lt_parent = cb.lte(child_left_column.id, layout_columns.id)
				self.constraints += cb.assert_expr(left_column_lt_parent, "child_" + child.shape_id + "_left_column_lt_layout_columns")

				right_column_lt_parent = cb.lte(child_right_column.id, layout_columns.id)
				self.constraints += cb.assert_expr(right_column_lt_parent, "child_" + child.shape_id + "_right_column_lt_layout_columns")

				# Left column should be less than or equal to right column 
				left_column_lt_right = cb.lte(child_left_column.id, child_right_column.id)
				self.constraints += cb.assert_expr(left_column_lt_right, "child_" + child.shape_id + "_left_column_lt_right_column")

				# Enforce that the x position of the child falls to the left edge of a column
				left_column_mult = cb.sub(child_left_column.id, "1")
				left_columns_spacing = cb.mult(column_width.id, left_column_mult)
				left_gutter_spacing = cb.mult(gutter_width.id, left_column_mult)
				child_x_position = cb.add(left_columns_spacing, cb.add(left_gutter_spacing, margin.id))

				self.constraints += cb.assert_expr(cb.eq(child.variables.x.id, child_x_position),
												   "child_" + child.shape_id + "_x_position_left_column")

				right_columns_spacing = cb.mult(column_width.id, child_right_column.id)
				right_gutter_spacing = cb.mult(gutter_width.id, cb.sub(child_right_column.id, "1"))
				child_right_position = cb.add(right_columns_spacing, cb.add(right_gutter_spacing, margin.id))

				self.constraints += cb.assert_expr(cb.eq(cb.add(child.variables.x.id, child.variables.width.id), child_right_position),
												   "child_" + child.shape_id + "_right_position_right_column")

				# Canvas alignment values 
				child_width = str(child.computed_width())
				l_index = child_canvas_alignment.domain.index("left")
				is_left = cb.eq(child_canvas_alignment.id, str(l_index))

				c_index = child_canvas_alignment.domain.index("center")
				is_center = cb.eq(child_canvas_alignment.id, str(c_index))
				
				r_index = child_canvas_alignment.domain.index("right")
				is_right = cb.eq(child_canvas_alignment.id, str(r_index))

				o_index = child_canvas_alignment.domain.index("other")
				is_other = cb.eq(child_canvas_alignment.id, str(o_index))
				
				aligned_left = cb.eq(child.variables.x.id, margin.id)
				aligned_center = cb.eq(cb.add(child.variables.x.id, cb.div(child_width, "2")), cb.div(canvas_width, "2"))
				aligned_right = cb.eq(cb.add(child.variables.x.id, child.variables.width.id), cb.sub(canvas_width, margin.id)) 
				aligned_other =	cb.and_expr([cb.not_expr(aligned_left), cb.not_expr(aligned_center), cb.not_expr(aligned_right)])

				self.constraints += cb.assert_expr(cb.ite(is_left,aligned_left,"true"), "child_" + child.shape_id + "_canvas_alignment_left")
				self.constraints += cb.assert_expr(cb.ite(is_right,aligned_right,"true"), "child_" + child.shape_id + "canvas_alignment_right")
				self.constraints += cb.assert_expr(cb.ite(is_center,aligned_center,"true"), "child_" + child.shape_id + "_canvas_alignment_center")
				self.constraints += cb.assert_expr(cb.ite(is_other,aligned_other,"true"), "child_" + child.shape_id + "_canvas_alignment_other")

	# Sets up the arrangment constrains for a given container
	def arrange_container(self, container, spacing): 
		""" Create arrangement constraints for a container including arrangement and padding """ 
		arrangement = container.variables.arrangement
		group_alignment = container.variables.group_alignment
		container_x = container.variables.x
		container_y = container.variables.y
		outside_padding = container.variables.outside_padding.id if container.at_root else "0"

		# ====== Arrangement constraints =======
		# Vertical and horizontal arrangments
		# In order that elements were defined
		v_index = arrangement.domain.index("vertical")
		is_vertical = cb.eq(arrangement.id, str(v_index))

		h_index = arrangement.domain.index("horizontal")
		is_horizontal = cb.eq(arrangement.id, str(h_index))

		rows_index = arrangement.domain.index("rows")
		is_rows = cb.eq(arrangement.id, str(rows_index))
		columns_index = arrangement.domain.index("columns")
		is_columns = cb.eq(arrangement.id, str(columns_index))

		# Group alignment
		left_index = group_alignment.domain.index("left")
		center_index = group_alignment.domain.index("center")
		is_left = cb.eq(group_alignment.id, str(left_index))
		is_center = cb.eq(group_alignment.id, str(center_index))

		if container.container_order == "important": 
			# When container order is important, we set explicit ordering on neighboring eelements based on the arrangement value.
			vertical_pairs = []
			horizontal_pairs = []
			child_shapes = container.children
			for s_index in range(0, len(child_shapes)-1): 
				shape1 = child_shapes[s_index]
				shape1_x = shape1.variables.x.id
				shape1_y = shape1.variables.y.id

				shape2 = child_shapes[s_index+1]
				shape2_x = shape2.variables.x.id
				shape2_y = shape2.variables.y.id

				shape1_height = str(shape1.computed_height())
				vertical_pair_y = cb.eq(cb.add(cb.add(shape1_y, shape1_height), spacing), shape2_y)
				vertical_pairs.append(vertical_pair_y)

				shape1_width = str(shape1.computed_width())
				horizontal_pair_x = cb.eq(cb.add(cb.add(shape1_x, shape1_width), spacing), shape2_x)
				horizontal_pairs.append(horizontal_pair_x)

			if len(child_shapes) > 1: 
				vertical_arrange = cb.and_expr(vertical_pairs)
				horizontal_arrange = cb.and_expr(horizontal_pairs)

				self.constraints += cb.assert_expr(cb.ite(is_vertical, vertical_arrange, "true"),
					"container_" + container.shape_id + "_vertical_arrangement")
				self.constraints += cb.assert_expr(cb.ite(is_horizontal, horizontal_arrange, "true"), 
					"container_" + container.shape_id + "_horizontal_arrangement")
				
		# Sum up the widths and heights
		child_widths = ""
		child_heights = ""
		child_shapes = container.children
		last_child_index = len(child_shapes) - 1

		left_padding = cb.ite(is_left, "0", cb.ite(is_center, outside_padding, cb.mult(outside_padding, "2")))
		right_padding = cb.ite(is_left, cb.mult(outside_padding, "2"), cb.ite(is_center, outside_padding, "0"))

		# Enforce a max width or height of the container for horizontal or vertical groups 
		# When order is not important, the width or height in addition to constraints on spacing
		# Will keep the elements inside the group, but allow them to change order. 
		for child_i in range(0, len(child_shapes)): 
			child = child_shapes[child_i]
			child_x = child.variables.x.id
			child_y = child.variables.y.id

			add_spacing = 0 if child_i == (len(child_shapes) - 1) else spacing
			child_widths = cb.add(child_widths, cb.add(str(child.computed_width()), str(add_spacing)))
			child_heights = cb.add(child_heights, cb.add(str(child.computed_height()), str(add_spacing)))

			if child.order == last_child_index: 
				# The bottom of the shape is the bottom of the container
				is_bottom = cb.eq(cb.add(child_y, str(child.computed_height())), cb.add(container_y.id,  str(container.computed_height())))
				is_right = cb.eq(cb.add(child_x, str(child.computed_width())), cb.sub(cb.add(container_x.id, str(container.computed_width())), right_padding))
				self.constraints += cb.assert_expr(cb.ite(is_vertical, is_bottom, "true"), "container_" + container.shape_id + "_vertical_order_last_child")
				self.constraints += cb.assert_expr(cb.ite(is_horizontal, is_right, "true"), "container_" + container.shape_id + "_horizontal_order_last_child")

			if child.order == 0:
				is_top = cb.eq(child_y, container_y.id)
				is_left = cb.eq(child_x, cb.add(container_x.id, left_padding))
				self.constraints += cb.assert_expr(cb.ite(is_vertical, is_top, "true"), child.shape_id + "_" + container.shape_id + "_first_order_top")
				self.constraints += cb.assert_expr(cb.ite(is_horizontal, is_left, "true"), child.shape_id + "_" + container.shape_id + "_first_order_left")


			# Every child should be inside the bounds of the container, including the space left for the outside_padding 
			self.constraints += cb.assert_expr(cb.gte(child_x, cb.add(container_x.id, left_padding)), "container_" + container.shape_id + "_shape_" + child.shape_id + "_x_gt_left")
			self.constraints += cb.assert_expr(cb.lte(cb.add(child_x, str(child.computed_width())), 
				cb.sub(cb.add(container_x.id, str(container.computed_width())), right_padding)), "container_" + container.shape_id + "_shape_" + child.shape_id + "_right_lt_width")

		# Enforce width and height of the container based on the arrangement axis and the total 
		# sum of the child heights or widths. 
		self.constraints += cb.assert_expr(cb.ite(is_vertical, cb.eq(str(container.computed_height()), child_heights), "true"), 
			"container_" + container.shape_id + "_child_heights_vertical")
		self.constraints += cb.assert_expr(cb.ite(is_horizontal, cb.eq(str(container.computed_width()), cb.add(cb.mult("2", outside_padding), child_widths)), "true"), 
			"container_" + container.shape_id + "_child_widths_horizontal")

		# Enforce that the height of the container should be equal to the height of the tallest child, if horizontal
		# Enforce that the width of the container should be equal to the width of the widest child, if vertical 
		m_w_constraint = cb.eq(str(container.computed_width()), cb.add(cb.mult("2", outside_padding), size_constraint_helpers.get_max_width_constraint(1,0,child_shapes)))
		m_h_constraint = cb.eq(str(container.computed_height()), (size_constraint_helpers.get_max_height_constraint(1,0,child_shapes)))
		self.constraints += cb.assert_expr(cb.ite(is_vertical, m_w_constraint, "true"), 
			"container_" + container.shape_id + "_max_width_vertical")

		self.constraints += cb.assert_expr(cb.ite(is_horizontal, m_h_constraint, "true"), 
			"container_" + container.shape_id + "_max_height_horizontal")

		# Enforce that the padding used by the container is no taller or wider than the smallest width or height element
		# The above is for visual hierarchy maintenance. 
		shapes_no_seps = [shp for shp in child_shapes if shp.semantic_type != "separator"]
		min_w_constraint = size_constraint_helpers.get_min_width_constraint(1,0,shapes_no_seps)
		min_h_constraint = size_constraint_helpers.get_min_height_constraint(1,0,shapes_no_seps)
		self.constraints += cb.assert_expr(cb.ite(cb.or_expr([is_vertical, is_columns]), cb.lt(container.variables.padding.id, min_h_constraint), "true"),
			"container_" + container.shape_id + "_padding_lt_shortest_child")
		self.constraints += cb.assert_expr(cb.ite(cb.or_expr([is_horizontal, is_rows]), cb.lt(container.variables.padding.id, min_w_constraint), "true"),
			"container_" + container.shape_id + "_padding_lt_thinnest_child")

		# Constraints for when the arrangemnet is rows or columns. 
		columnizer.balanced_row_column_arrangement(is_rows, is_columns, container, rows_index, columns_index, spacing)
		self.constraints += columnizer.constraints

	def align_container(self, container, spacing):
		""" Alignement constraints for a container to align elements inside a container to one of 6 possible axes """
		alignment = container.variables.alignment
		arrangement = container.variables.arrangement
		container_x = container.variables.x
		container_y = container.variables.y
		outside_padding = container.variables.outside_padding.id if container.at_root else "0"

		l_index = alignment.domain.index("left")
		c_index = alignment.domain.index("center")
		is_left = cb.eq(alignment.id, str(l_index))
		is_center = cb.eq(alignment.id, str(c_index))
		v_index = arrangement.domain.index("vertical")
		is_vertical = cb.eq(arrangement.id, str(v_index))
		h_index = arrangement.domain.index("horizontal")
		is_horizontal = cb.eq(arrangement.id, str(h_index))

		# Alignment
		# Adjust the axis of alignment depending on whether the container is horizontal or vertical 
		# within columns will be handled separately 
		child_shapes = container.children
		container_width = str(container.computed_width())
		container_height = str(container.computed_height())
		for child in child_shapes:
			child_x = child.variables.x.id
			child_y = child.variables.y.id

			child_width = str(child.computed_width())
			child_height = str(child.computed_height())

			bottom_axis = child.variables.baseline.id if child.has_baseline else cb.add(child_y, child_height)

			left_aligned = cb.eq(child_x, cb.add(outside_padding, container_x.id))
			right_aligned = cb.eq(cb.add(child_x, child_width), cb.sub(cb.add(container_x.id, container_width), outside_padding))
			h_center_aligned = cb.eq(cb.add(child_x, cb.div(child_width, "2")),
				cb.add(container_x.id, cb.div(container_width, "2")))
			top_aligned = cb.eq(child_y, container_y.id)
			bottom_aligned = cb.eq((bottom_axis), cb.add(container_y.id, container_height))
			v_center_aligned = cb.eq(cb.add(child_y, cb.div(child_height, "2")),
				cb.add(container_y.id, cb.div(container_height, "2")))
			horizontal = cb.ite(is_left, top_aligned, cb.ite(is_center, v_center_aligned, bottom_aligned))
			vertical = cb.ite(is_left, left_aligned, cb.ite(is_center, h_center_aligned, right_aligned))
			
			self.constraints += cb.assert_expr(cb.ite(is_vertical, vertical, "true"), 
				"container_" + container.shape_id + "_" + child.shape_id + "_vertical_alignment")
			self.constraints += cb.assert_expr(cb.ite(is_horizontal, horizontal, "true"), 
				"container_" + container.shape_id + "_" + child.shape_id + "_horizontal_alignment") 
