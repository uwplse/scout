from z3 import *
import shapes
import math
import time
import smtlib_builder as cb

CANVAS_HEIGHT = 667
CANVAS_WIDTH = 375

def abs(x):
	return If(x>=0,x,-x)

class ConstraintBuilder(object):
	def __init__(self, solver): 
		# So we can override the add method for debugging
		self.solver = solver
		self.constraints = "(set-info :source | Python ftw |)\n"
		self.decl_constraints = ""

	def load_constraints(self): 
		# Parse the constraints into a set of assertions
		const = self.decl_constraints + self.constraints
		self.solver.load_constraints(const)		

	def declare_variables(self, shapes): 
		for shape in shapes.values(): 
			for key, val in shape.variables.items():
				self.decl_constraints += cb.declare(val.id, val.type)

	def init_previous_solution_constraints(self, previous_solutions, shapes): 
		# Saved solutions should not appear again in the results
		declared = False
		for solution in previous_solutions: 
			elements = solution["elements"]
			if (not "added" in solution and not "removed" in solution) or (not len(solution["added"]) and not len(solution["removed"])):
				self.get_previous_solution_constraints_from_elements(shapes, elements, solution["id"])


	def get_solution_variable_declarations(self, shapes, elements): 
		declarations = ""
		for elementID in elements:
			element = elements[elementID]

			# Get the shape corresponding to the element name
			shape = shapes[elementID]
			variables = shape.variables.toDict()
			for variable_key in variables.keys(): 
				variable = variables[variable_key]
				declarations += cb.declare(variable.id, variable.type)

		return declarations

	def get_previous_solution_constraints_from_elements(self, shapes, elements, solutionID):
		all_values = []
		for elementID in elements:
			element = elements[elementID]

			# Get the shape corresponding to the element name
			shape = shapes[elementID]
			variables = shape.variables.toDict()
			if shape.type == "leaf":
				for variable_key in variables.keys(): 
					variable = variables[variable_key]
					variable_value = variable.get_value_from_element(element)
					all_values.append(cb.eq(variable.id, 
						str(variable_value)))

		# Prevent the exact same set of values from being produced again (Not an And on all of the constraints)
		self.constraints += cb.assert_expr(cb.not_expr(cb.and_expr(all_values)), 
			"prevent_previous_solution_" + solutionID + "_values")

	def init_solution_constraints(self, shapes, elements, solutionID):
		all_values = []
		for elementID in elements:
			element = elements[elementID]

			# Get the shape corresponding to the element name
			shape = shapes[elementID]

			variables = shape.variables.toDict()
			for variable_key in variables.keys(): 
				variable = variables[variable_key]
				self.decl_constraints += cb.declare(variable.id, variable.type)
				if variable.name != "baseline":
					all_values.append(cb.eq(variable.id, 
						str(variable.get_value_from_element(element))))

		# Return the constraints so they can be loaded in after the intial initialization of the base constraints
		declarations = self.get_solution_variable_declarations(shapes, elements)
		constraints = cb.assert_expr(cb.and_expr(all_values), "fix_solution_" + solutionID + "_values")
		return declarations + constraints

	def init_shape_baseline(self, shape): 
		if shape.has_baseline:
			self.constraints += cb.eq(shape.variables.baseline.id, 
				cb.add(shape.variables.y.id, shape.orig_baseline), "baseine_" + shape.shape_id)

	# def init_shape_bounds(self, shape):
	# 	self.constraints += cb.assert_expr(cb.gte(shape.variables.x.id, "0"), "shape_" + shape.shape_id + "_x_gt_zero")
	# 	self.constraints += cb.assert_expr(cb.lte(cb.add(shape.variables.x.id, str(shape.computed_width())), 
	# 		str(CANVAS_WIDTH)), "shape_" + shape.shape_id + "_right_lt_width")
	# 	self.constraints += cb.assert_expr(cb.gte(shape.variables.y.id, "0"), "shape_" + shape.shape_id + "_y_gt_zero")
	# 	self.constraints += cb.assert_expr(cb.lte(cb.add(shape.variables.y.id, str(shape.computed_height())), 
	# 		str(CANVAS_HEIGHT)), "shape_" + shape.shape_id + "_bottom_lt_height")

	def init_canvas_constraints(self, canvas): 
		canvas_x = canvas.variables.x
		canvas_y = canvas.variables.y
		margin = canvas.variables.margin

		# Fix the canvas X,Y to their original valuess
		self.constraints += cb.assert_expr(cb.eq(canvas_x.id, str(canvas.x)), 'canvas_orig_x')
		self.constraints += cb.assert_expr(cb.eq(canvas_y.id, str(canvas.y)), 'canvas_orig_y')

		# Enforce children constraints
		child_shapes = canvas.children
		if len(child_shapes): 
			for s_index in range(0, len(child_shapes)): 
				shape1 = child_shapes[s_index]
				shape1_x = shape1.variables.x.id
				shape1_y = shape1.variables.y.id
				shape1_width = str(shape1.computed_width())
				shape1_height = str(shape1.computed_height())

				bottom_axis = shape1.variables.baseline.id if shape1.has_baseline else cb.add(shape1_y, shape1_height)

				# Shapes cannot exceed the bounds of their parent containers
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

				# Create importance level constraints
				if shape1.type == "leaf": 
					self.init_size(shape1, canvas)

		self.init_layout_grid(canvas)
		self.align_canvas_layout_grid(canvas)
		self.init_baseline_grid(canvas)
		self.layout_canvas_baseline_grid(canvas)
		self.canvas_padding(canvas)
		self.canvas_order(canvas)

	def layout_canvas_baseline_grid(self, canvas): 
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
				child_height = child.variables.height
				self.constraints += cb.assert_expr(cb.eq(cb.mod(child_height.id, canvas_baseline_grid.id), "0"), 
					"canvas_child_" + child.shape_id + "_height_mult_baseline_grid")

	def init_layout_grid(self, canvas): 
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

		self.constraints += cb.assert_expr(cb.or_expr(grid_values),
			"canvas_layout_grid_variables_in_domain")

	def init_baseline_grid(self, canvas): 
		grid = canvas.variables.baseline_grid
		grid_values = []
		for grid_value in grid.domain:
			grid_values.append(cb.eq(grid.id, str(grid_value)))
		self.constraints += cb.assert_expr(cb.or_expr(grid_values), "canvas_baseline_grid_in_domain")

	def init_container_constraints(self, container, shapes):
		arrangement = container.variables.arrangement.id
		alignment = container.variables.alignment.id
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

		# These two variables do not have variable values that correspond to an index 
		# so create an OR constraint instead
		padding_values = []
		for pad_value in container.variables.padding.domain:
			padding_values.append(cb.eq(padding, str(pad_value)))

		self.constraints += cb.assert_expr(cb.or_expr(padding_values), "container_"
			+ container.shape_id + "_padding_in_domain")

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
			self.arrange_container(container, spacing)
			self.align_container(container, spacing)
			self.non_overlapping(container, spacing)
			self.same_size_change(container)

			if container.typed: 
				# If this is a typed container, enforce all variables on child containers to be the same
				self.init_repeat_group(container, shapes)

	def init_size(self, shape, container): 
		size_factors = shape.variables.size_factor.domain
		size_combos = []
		for i in range(0, len(size_factors)):
			height = cb.eq(shape.variables.height.id, str(shape.variables.height.domain[i]))
			width = cb.eq(shape.variables.width.id, str(shape.variables.width.domain[i]))
			factor = cb.eq(shape.variables.size_factor.id, str(size_factors[i]))
			size_combos.append(cb.and_expr([height, width, factor]))

		self.constraints += cb.assert_expr(cb.or_expr(size_combos), 
			"shape_" + shape.shape_id + "_size_domains")

	def init_repeat_group(self, container, shapes): 
		subgroups = container.children
		all_same_values = []
		all_same_heights = []
		all_same_widths = []

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
			# Enforce all values of that collection to be thes ame 
			self.constraints += cb.assert_expr(cb.and_expr(all_same_variables), 
				"repeat_group_variables_all_same_" + str(i))


		# the size increase/decrease of corresponding elements should the same. 
		for group in subgroups: 
			group_children = group.children 
			for i in range(0, len(group_children)): 
				child = group_children[i]

				for j in range(0, len(child.correspondingIDs)): 
					child_corrID = child.correspondingIDs[j]
					child_corr_shape = shapes[child_corrID]

					self.constraints += cb.assert_expr(cb.eq(child.variables.size_factor.id,
															 child_corr_shape.variables.size_factor.id),
						"repeat_group_child_" + child.shape_id + "_and_child_" + child_corr_shape.shape_id + "_size_factor_equal")

		# The order of the elements within the groups should be uniform
		for group in subgroups:
			group_children = group.children
			for i in range(0, len(group_children)-1):
				child1 = group_children[i]
				child2 = group_children[i+1]
				child1_left = cb.lt(cb.add(child1.variables.x.id, str(child1.computed_width())), 
					child2.variables.x.id)
				child1_above = cb.lt(cb.add(child1.variables.y.id, str(child1.computed_height())), 
				 	child2.variables.y.id)
				child1_left_or_above = cb.or_expr([child1_left, child1_above])
		
				for j in range(0, len(child1.correspondingIDs)):
					child1_corrID = child1.correspondingIDs[j]
					child2_corrID = child2.correspondingIDs[j]
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
		# Add constraints for all of the locked properties
		if shape.locks is not None: 
			for lock in shape.locks:
				value = str(shape.variable_values[lock])
				if shape.variables[lock].type == "String": 
					value = "\"" + shape.variable_values[lock] + "\""

				self.constraints += cb.assert_expr(cb.eq(shape.variables[lock].id, value),
					"lock_" + shape.shape_id + "_" + shape.variables[lock].name + "_" + str(shape.variable_values[lock])) 

	def non_overlapping(self, container, spacing): 
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
		bedge1 = cb.add(shape1_y, shape1_height) 
		bedge2 = cb.add(shape2_y, shape2_height)
		return cb.lt(bedge1, bedge2)

	def canvas_order(self, canvas): 
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
		# Enforce padding between elements that is greater than the padding inside the groups 
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
					# visual separation. 
					spacing = canvas.min_spacing
					if shape1.is_container and shape2.is_container: 
						spacing = cb.ite(cb.gt(shape1.variables.padding.id, shape2.variables.padding.id), 
							shape1.variables.padding.id, shape2.variables.padding.id)
					elif shape1.is_container: 
						spacing = shape1.variables.padding.id
					elif shape2.is_container: 
						spacing = shape2.variables.padding.id

					# Non-overlapping
					left = cb.lte(cb.add(shape1_x, cb.add(shape1_width, spacing)), shape2_x)
					right = cb.lte(cb.add(cb.add(shape2_x, shape2_width),  spacing), shape1_x)
					top = cb.lte(cb.add(cb.add(shape1_y, shape1_height), spacing), shape2_y)
					bottom = cb.lte(cb.add(cb.add(shape2_y, shape2_height), spacing), shape1_y)
					self.constraints += cb.assert_expr(cb.or_expr([left,right,top,bottom]), 
						"non_overlapping_shapes_" + shape1.shape_id + "_" + shape2.shape_id)

	def same_size_change(self, container):
		size_equals = [] 
		child_shapes = container.children 
		for i in range(0, len(child_shapes)):
			for j in range(0, len(child_shapes)): 
				if i != j: 
					shape1 = child_shapes[i]
					shape2 = child_shapes[j]
					if shape1.type == "leaf" and shape2.type == "leaf":
						size_eq = cb.eq(shape1.variables.size_factor.id, shape2.variables.size_factor.id)
						size_equals.append(size_eq)

		if len(size_equals):
			self.constraints += cb.assert_expr(cb.and_expr(size_equals),
				"container_" + container.shape_id + "_size_factor_children_equal")

	def get_row_width(self, row, spacing):
		width = ""
		for i in range(0, len(row)):
			if i < len(row) - 1:
				if len(width): 
					width = cb.add(width, cb.add(str(row[i].computed_width()), str(spacing)))
				else: 
					width = cb.add(str(row[i].computed_width()), str(spacing))
			else:
				if len(width): 
					width = cb.add(width, str(row[i].computed_width()))
				else: 
					width = str(row[i].computed_width())
		return width

	def get_column_height(self, column, spacing):
		height = ""
		for i in range(0, len(column)):
			if i < len(column) - 1:
				if len(height): 
					height = cb.add(height, cb.add(str(column[i].computed_height()), str(spacing)))
				else: 
					height = cb.add(str(column[i].computed_height()), str(spacing))
			else:
				if len(height): 
					height = cb.add(height, str(column[i].computed_height()))
				else: 
					height = str(column[i].computed_height())
		return height

	def get_widest_row_constraint(self, row_i, widest_i, rows, spacing):
		widest_row = rows[widest_i]
		widest_row_width = self.get_row_width(widest_row, spacing)

		if row_i < len(rows):
			next_row = rows[row_i]
			next_row_width = self.get_row_width(next_row, spacing)
			return cb.ite(cb.gt(widest_row_width, next_row_width), 
				self.get_widest_row_constraint(row_i+1, widest_i, rows, spacing), 
				self.get_widest_row_constraint(row_i+1, row_i, rows, spacing))
		else:
			return widest_row_width

	def get_tallest_column_constraint(self, column_i, tallest_i, columns, spacing):
		tallest_column = columns[tallest_i]
		tallest_column_height = self.get_column_height(tallest_column, spacing)
		if column_i < len(columns):
			next_column = columns[column_i]
			next_column_height = self.get_column_height(next_column, spacing)
			return cb.ite(cb.gt(tallest_column_height, next_column_height), 
				self.get_tallest_column_constraint(column_i+1, tallest_i, columns, spacing), 
				self.get_tallest_column_constraint(column_i+1, column_i, columns, spacing))
		else:
			return tallest_column_height

	def get_max_width_constraint(self, child_i, widest_i, child_shapes): 
		if child_i < len(child_shapes): 
			widest_child = child_shapes[widest_i]
			widest_child_width = str(widest_child.computed_width())

			next_child = child_shapes[child_i]
			next_child_width = str(next_child.computed_width())
			return cb.ite(cb.gt(widest_child_width, next_child_width),
				self.get_max_width_constraint(child_i+1, widest_i, child_shapes), 
				self.get_max_width_constraint(child_i+1, child_i, child_shapes))
		else: 
			child_shape_width = str(child_shapes[widest_i].computed_width())
			return child_shape_width

	def get_min_width_constraint(self, child_i, thinnest_i, child_shapes): 
		if child_i < len(child_shapes): 
			thinnest_child = child_shapes[thinnest_i]
			thinnest_child_width = str(thinnest_child.computed_width())

			next_child = child_shapes[child_i]
			next_child_width = str(next_child.computed_width())
			return cb.ite(cb.lt(thinnest_child_width, next_child_width),
				self.get_min_width_constraint(child_i+1, thinnest_i, child_shapes), 
				self.get_max_width_constraint(child_i+1, child_i, child_shapes))
		else: 
			child_shape_width = str(child_shapes[widest_i].computed_width())
			return child_shape_width

	def get_max_height_constraint(self, child_i, tallest_i, child_shapes): 
		if child_i < len(child_shapes): 
			tallest_child = child_shapes[tallest_i]
			tallest_child_height = str(tallest_child.computed_height())

			next_child = child_shapes[child_i]
			next_child_height = str(next_child.computed_height())
			return cb.ite(cb.gt(tallest_child_height, next_child_height),
				self.get_max_height_constraint(child_i+1, tallest_i, child_shapes), 
				self.get_max_height_constraint(child_i+1, child_i, child_shapes))
		else: 
			child_shape_height = str(child_shapes[tallest_i].computed_height())
			return child_shape_height

	def get_min_height_constraint(self, child_i, shortest_i, child_shapes): 
		if child_i < len(child_shapes): 
			shortest_child = child_shapes[shortest_i]
			shortest_child_height = str(shortest_child.computed_height())

			next_child = child_shapes[child_i]
			next_child_height = str(next_child.computed_height())
			return cb.ite(cb.lt(shortest_child_height, next_child_height),
				self.get_max_height_constraint(child_i+1, shortest_i, child_shapes), 
				self.get_max_height_constraint(child_i+1, child_i, child_shapes))
		else: 
			child_shape_height = str(child_shapes[tallest_i].computed_height())
			return child_shape_height

	def align_canvas_layout_grid(self, canvas):
		layout_columns = canvas.variables.columns
		gutter_width = canvas.variables.gutter_width
		column_width = canvas.variables.column_width
		margin = canvas.variables.margin
		canvas_x = canvas.variables.x
		canvas_width = canvas.computed_width()

		# Enforce children constraints
		child_shapes = canvas.children
		if len(child_shapes): 
			for child_index in range(0, len(child_shapes)): 
				child = child_shapes[child_index]
				child_column = child.variables.column
				# Enforce the child column domain values
				column_values = []
				for col_value in child_column.domain: 
					col_eq = cb.eq(child_column.id, str(col_value))
					column_values.append(col_eq)
				self.constraints += cb.assert_expr(cb.or_expr(column_values),
					"shape_" + child.shape_id + "_layout_column_value")

				# Enforce that the child column value is less than the canvas column amount
				column_lt_parent = cb.lt(child_column.id, layout_columns.id)
				self.constraints += cb.assert_expr(column_lt_parent, "child_" + child.shape_id + "_column_lt_layout_columns")

				# Enforce that the x position of the child falls to the left edge of a column 
				columns_mult = cb.sub(child_column.id, "1")
				columns_spacing = cb.mult(column_width.id, columns_mult)
				gutter_spacing = cb.mult(gutter_width.id, columns_mult)
				child_x_position = cb.add(columns_spacing, cb.add(gutter_spacing, margin.id))
				self.constraints += cb.assert_expr(cb.eq(child.variables.x.id, child_x_position),
												   "child_" + child.shape_id + "_x_position_column")

	def align_rows_or_columns(self, container, padding, rows, column_or_row,
							  aligned_axis, aligned_axis_size, layout_axis, layout_axis_size):
		constraints = []
		l_index = container.variables.alignment.domain.index("left")
		c_index = container.variables.alignment.domain.index("center")
		is_left = cb.eq(container.variables.alignment.id, str(l_index))
		is_center = cb.eq(container.variables.alignment.id, str(c_index))
		for row in rows: 
			for i in range(len(row)-1): 
				shape1 = row[i]
				shape2 = row[i+1]

				aligned_axis_size_value = str(shape1.computed_width()) if aligned_axis_size == "width" else str(shape1.computed_height())
				aligned_axis_size_value2 = str(shape2.computed_width()) if aligned_axis_size == "width" else str(shape2.computed_height())

				left_top_aligned = cb.eq(shape1.variables[aligned_axis].id, shape2.variables[aligned_axis].id)
				right_bottom_aligned = cb.eq(cb.add(shape1.variables[aligned_axis].id, aligned_axis_size_value), 
					cb.add(shape2.variables[aligned_axis].id, aligned_axis_size_value2))
				center_aligned = cb.eq(cb.add(shape1.variables[aligned_axis].id, cb.div(aligned_axis_size_value, "2")), 
					cb.add(shape2.variables[aligned_axis].id, cb.div(aligned_axis_size_value2, "2")))

				constraints.append(cb.ite(is_left, left_top_aligned, 
					cb.ite(is_center, center_aligned, right_bottom_aligned)))

				# Shape 2 is exactly to the right of shape 1 or to the bottom if in a column 
				layout_axis_size_value = str(shape1.computed_width()) if layout_axis_size == "width" else str(shape1.computed_height())
				constraints.append(cb.eq(cb.add(shape1.variables[layout_axis].id, cb.add(layout_axis_size_value, padding)), 
					shape2.variables[layout_axis].id))

		if len(constraints):
			return cb.and_expr(constraints)
		return True

	def align_left_or_top(self, rows, padding, column_or_row, aligned_axis, below_or_right_axis, width_or_height):
		constraints = []
		for i in range(0, len(rows)-1):
			row1 = rows[i] 
			row2 = rows[i+1]
			if len(row1) > 0 and len(row2) > 0: 
				shape1 = row1[0]
				shape2 = row2[0]

				# Width or height of shape1 
				w_or_h = str(shape1.computed_width()) if width_or_height == "width" else str(shape1.computed_height())

				# Shape1 row is left or top aligned to shape2 row
				constraints.append(cb.eq(shape1.variables[aligned_axis].id, shape2.variables[aligned_axis].id))

				# shape2 row is below or to the right of shape1 row
				constraints.append(cb.lte(cb.add(shape1.variables[below_or_right_axis].id, cb.add(w_or_h, padding)), shape2.variables[below_or_right_axis].id))
		if len(constraints):
			return cb.and_expr(constraints)
		return True

	def set_container_size_main_axis(self, container, padding, rows_or_columns, width_or_height):
		size = ""
		num_rows_or_columns = len(rows_or_columns)
		for i in range(0, num_rows_or_columns):
			row_or_column = rows_or_columns[i]
			if len(row_or_column):
				spacing = padding if i < num_rows_or_columns - 1 else 0
				m_height_or_width = None
				if width_or_height == "width": 
					m_height_or_width = self.get_max_width_constraint(1,0,row_or_column)
				else: 
					m_height_or_width = self.get_max_height_constraint(1,0,row_or_column)
				
				if len(size): 
					size = cb.add(size, cb.add(m_height_or_width, str(spacing)))
				else: 
					size = cb.add(m_height_or_width, str(spacing))

		container_size = str(container.computed_width()) if width_or_height == "width" else str(container.computed_height())
		return cb.eq(container_size, size)

	def set_container_size_cross_axis(self, container, padding, rows_or_columns, width_or_height):
		size = self.get_widest_row_constraint(1, 0, rows_or_columns, padding) if width_or_height == "width" else self.get_tallest_column_constraint(1, 0, rows_or_columns, padding)
		container_size = str(container.computed_width()) if width_or_height == "width" else str(container.computed_height())
		return cb.eq(container_size, size)

	def split_children_into_groups(self, container):  
		# I hate. this algorithm
		num_rows = container.num_rows_or_columns()
		child_shapes = container.children
		num_in_first = math.floor(len(child_shapes)/2)
		num_in_second = math.ceil(len(child_shapes)/2)
		rows = []
		num_in_row = 0
		child_index = 0
		first_row = []
		while num_in_row < num_in_first: 
			first_row.append(child_shapes[child_index])
			num_in_row += 1
			child_index += 1

		second_row = []
		num_in_row = 0
		while num_in_row < num_in_second:
			second_row.append(child_shapes[child_index])
			num_in_row += 1
			child_index += 1
		rows.append(first_row)
		rows.append(second_row)
		return rows

	# Sets up the arrangment constrains for a given container
	def arrange_container(self, container, spacing): 
		arrangement = container.variables.arrangement
		container_x = container.variables.x
		container_y = container.variables.y

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

		if container.container_order == "important": 
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

		# Enforce a max width or height of the container for horizontal or vertical
		for child_i in range(0, len(child_shapes)): 
			child = child_shapes[child_i]
			child_x = child.variables.x.id
			child_y = child.variables.y.id

			add_spacing = 0 if child_i == (len(child_shapes) - 1) else spacing
			child_widths = cb.add(child_widths, cb.add(str(child.computed_width()), str(add_spacing)))
			child_heights = cb.add(child_heights, cb.add(str(child.computed_height()), str(add_spacing)))

			if child.order == last_child_index: 
				# The bottom of the shape is the bottom of the container
				is_bottom = cb.eq(cb.add(child_y, str(child.computed_height())), cb.add(container_y,  str(container.computed_height())))
				is_right = cb.eq(cb.add(child_x, str(child.computed_width())), cb.add(container_x, str(container.computed_width())))
				self.constraints += cb.assert_expr(cb.ite(is_vertical, is_bottom, "true"), "container_" + container.shape_id + "_vertical_order_last_child")
				self.constraints += cb.assert_expr(cb.ite(is_horizontal, is_right, "true"), "container_" + container.shape_id + "_horizontal_order_last_child")

			if child.order == 0:
				is_top = cb.eq(child_y, container_y)
				is_left = cb.eq(child_x, container_x)
				self.constraints += cb.assert_expr(cb.ite(is_vertical, is_top, "true"), child.shape_id + "_" + container.shape_id + "_first_order_top")
				self.constraints += cb.assert_expr(cb.ite(is_horizontal, is_left, "true"), child.shape_id + "_" + container.shape_id + "_first_order_left")

		# Enforce width and height of the container based on the arrangement axis and the total 
		# sum of the child heights or widths. 
		self.constraints += cb.assert_expr(cb.ite(is_vertical, cb.eq(str(container.computed_height()), child_heights), "true"), 
			"container_" + container.shape_id + "_child_heights_vertical")
		self.constraints += cb.assert_expr(cb.ite(is_horizontal, cb.eq(str(container.computed_width()), child_widths), "true"), 
			"container_" + container.shape_id + "_child_widths_horizontal")

		# Enforce that the height of the container should be equal to the height of the tallest child, if horizontal
		# Enforce that the width of the container should be equal to the width of the widest child, if vertical 
		m_w_constraint = cb.eq(str(container.computed_width()), (self.get_max_width_constraint(1,0,child_shapes)))
		m_h_constraint = cb.eq(str(container.computed_height()), (self.get_max_height_constraint(1,0,child_shapes)))
		self.constraints += cb.assert_expr(cb.ite(is_vertical, m_w_constraint, "true"), 
			"container_" + container.shape_id + "_max_width_vertical")

		self.constraints += cb.assert_expr(cb.ite(is_horizontal, m_h_constraint, "true"), 
			"container_" + container.shape_id + "_max_height_horizontal")

		# Enforce that the padding used by the container is no taller or wider than the smallest width or height element
		# min_w_constraint = cb.eq(str(container.computed_width()), (self.get_min_width_constraint(1,0,child_shapes)))
		# min_h_constraint = cb.eq(str(container.computed_height()), (self.get_min_height_constraint(1,0,child_shapes)))
		# self.constraints += cb.assert_expr(cb.ite(cb.or_expr(is_vertical, is_columns), cb.lt(container.padding.id, min_h_constraint), "true"), 
		# 	"container_" + container.shape_id + "_padding_lt_shortest_child")
		# self.constraints += cb.assert_expr(cb.ite(cb.or_expr(is_horizontal, is_rows), cb.lt(container.padding.id, min_w_constraint), "true"),
		# 	"container_" + container.shape_id + "_padding_lt_thinnest_child")

		# Columns/Rows arrangement constraints
		# Only apply if there are > 2 children elements
		if len(container.children) > 2:
			groups = self.split_children_into_groups(container)
			self.constraints += cb.assert_expr(cb.ite(is_rows, 
				self.align_rows_or_columns(container, spacing, groups, "row", "y", "height", "x", "width"), "true"), 
				"container_" + container.shape_id + "_align_rows")
			self.constraints += cb.assert_expr(cb.ite(is_columns, 
				self.align_rows_or_columns(container, spacing, groups, "column", "x", "width", "y", "height"), "true"), 
				"container_" + container.shape_id + "_align_columns")
			self.constraints += cb.assert_expr(cb.ite(is_rows,
				self.align_left_or_top(groups, spacing, "row", "x", "y", "height"), "true"),
				"container_" + container.shape_id + "_align_rows_left")
			self.constraints += cb.assert_expr(cb.ite(is_columns,
				self.align_left_or_top(groups, spacing, "column", "y", "x", "width"), "true"),
				"container_" + container.shape_id + "_align_columns_left")

			self.constraints += cb.assert_expr(cb.ite(is_rows,
				self.set_container_size_main_axis(container, spacing, groups, "height"), "true"),
				"container_" + container.shape_id + "_max_row_height")
			self.constraints += cb.assert_expr(cb.ite(is_columns,
				self.set_container_size_main_axis(container, spacing, groups, "width"), "true"),
				"container_" + container.shape_id + "_max_row_width")

			self.constraints += cb.assert_expr(cb.ite(is_rows,
				self.set_container_size_cross_axis(container, spacing, groups, "width"), "true"),
				"container_" + container.shape_id + "_max_container_height_from_rows")
			self.constraints += cb.assert_expr(cb.ite(is_columns,
				self.set_container_size_cross_axis(container, spacing, groups, "height"), "true"),
				"container_" + container.shape_id + "_max_container_width_from_columns")
		else:
			# Prevent columnns and rows variables if there are 2 children or less
			self.constraints += cb.assert_expr(cb.neq(arrangement.id, str(rows_index)), 
				"container_" + container.shape_id + "_arrangement_neq_rows")
			self.constraints += cb.assert_expr(cb.neq(arrangement.id, str(columns_index)), 
				"container_" + container.shape_id + "_arrangement_neq_columns")

	def align_container(self, container, spacing):
		alignment = container.variables.alignment
		arrangement = container.variables.arrangement
		container_x = container.variables.x
		container_y = container.variables.y

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

			left_aligned = cb.eq(child_x, container_x.id)
			right_aligned = cb.eq(cb.add(child_x, child_width), cb.add(container_x.id, container_width))
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
