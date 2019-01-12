from z3 import *
import shapes
import math
import time
import smtlib_builder as cb

def abs(x):
	return If(x>=0,x,-x)

class ConstraintBuilder(object):
	def __init__(self, solver): 
		# So we can override the add method for debugging
		self.solver = solver

	def add_constraints(self, constraints): 
		# Parse the constraints into a set of assertions
		self.solver.add_constraints(constraints)

	def init_previous_solution_constraints(self, previous_solutions, shapes): 
		# Saved solutions should not appear again in the results
		constraints = ""
		decl_constraints = ""
		declared = False
		for solution in previous_solutions: 
			elements = solution["elements"]
			if (not "added" in solution and not "removed" in solution) or (not len(solution["added"]) and not len(solution["removed"])):
				if not declared: 
					decl_constraints = self.get_solution_variable_declarations(shapes, elements)
					constraints += decl_constraints
					declared = True
				constraints += self.get_previous_solution_constraints_from_elements(shapes, elements, solution["id"])
		self.add_constraints(constraints)

	def init_solution_constraints(self, shapes, elements, solutionID):
		# Get the constraints for checking the validity of the previous solution
		constraints = self.get_solution_constraints_from_elements(shapes, elements)

		# All of the variables that were set for this solution should be maintained
		self.add_constraints(constraints)

	def get_solution_variable_declarations(self, shapes, elements): 
		decl_constraints = "" # Because Z3 requires declaring these again to use from_string to parse but
							  # They are not actually re-declared
		for elementID in elements:
			element = elements[elementID]

			# Get the shape corresponding to the element name
			shape = shapes[elementID]
			variables = shape.variables.toDict()
			if shape.type == "leaf":
				for variable_key in variables.keys(): 
					variable = variables[variable_key]
					decl_constraints += cb.declare(variable.id, variable.type)
		return decl_constraints

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
					if variable.type == "String":
						variable_value = "\"" + variable_value + "\""
					all_values.append(cb.eq(variable.id, 
						str(variable_value)))

		# Prevent the exact same set of values from being produced again (Not an And on all of the constraints)
		constraints = cb.assert_expr(cb.not_expr(cb.and_expr(all_values)), 
			"prevent_previous_solution_" + solutionID + "_values")
		return constraints

	def get_solution_constraints_from_elements(self, shapes, elements): 
		all_values = []
		decl_constraints = "" # Because Z3 requires declaring these again to use from_string to parse but
							  # They are not actually re-declared
		for elementID in elements:
			element = elements[elementID]

			# Get the shape corresponding to the element name
			shape = shapes[elementID]

			variables = shape.variables.toDict()
			for variable_key in variables.keys(): 
				variable = variables[variable_key]
				decl_constraints += cb.declare(variable.id, variable.type)
				if variable.name != "baseline": 
					all_values.append(cb.eq(variable.id, 
						str(variable.get_value_from_element(element))))

		# Prevent the exact same set of values from being produced again (Not an And on all of the constraints)
		constraints = cb.assert_expr(cb.not_expr(cb.and_expr(all_values)), 
			"fix_solution_" + solution["id"] + "_values")
		constraints = decl_constraints + constraints
		return constraints	

	def init_shape_baseline(self, shape): 
		constraints = ""
		if shape.has_baseline:
			constraints += cb.eq(shape.variables.baseline.id, 
				add(shape.variables.y.id, shape.orig_baseline), "baseine_" + shape.shape_id)
		return constraints

	def init_shape_bounds(self, shape, canvas_width, canvas_height):
		constraints = ""
		constraints += cb.assert_expr(cb.gte(shape.variables.x.id, "0"), "shape_" + shape.shape_id + "_x_gt_zero")
		constraints += cb.assert_expr(cb.lte(cb.add(shape.variables.x.id, str(shape.computed_width())), 
			str(canvas_width)), "shape_" + shape.shape_id + "_right_lt_width")
		constraints += cb.assert_expr(cb.gte(shape.variables.y.id, "0"), "shape_" + shape.shape_id + "_y_gt_zero")
		constraints += cb.assert_expr(cb.lte(cb.add(shape.variables.y.id, str(shape.computed_height())), 
			str(canvas_height)), "shape_" + shape.shape_id + "_bottom_lt_height")
		return constraints

	def init_shape_grid_values(self, shape, canvas): 
		grid = canvas.variables.grid.z3
		shape_x = shape.variables.x.z3
		# shape_y = shape.variables.y.z3
		# self.solver.cb.add((shape_x % grid) == 0, shape.shape_id + " x multiple of grid value.")
		# self.solver.cb.add((shape_y % grid) == 0, shape.shape_id + " y multiple of grid value.")


	def init_canvas_constraints(self, canvas): 
		alignment = canvas.variables.alignment
		justification = canvas.variables.justification
		margin = canvas.variables.margin
		background_color = canvas.variables.background_color
		canvas_x = canvas.variables.x
		canvas_y = canvas.variables.y
		constraints = ""

		constraints += cb.assert_expr(cb.gte(alignment.id, "0"), 'canvas_alignment_domain_lowest')
		constraints += cb.assert_expr(cb.lt(alignment.id, 
			str(len(alignment.domain))), 'canvas_alignment_domain_highest')
		constraints += cb.assert_expr(cb.gte(justification.id, "0"), 'canvas_justification_domain_lowest')
		constraints += cb.assert_expr(cb.lt(justification.id, str(len(justification.domain))), 
			"canvas_justification_domain_highest")

		or_values = []
		for margin_value in margin.domain:
			or_values.append(cb.eq(margin.id, str(margin_value)))
		constraints += cb.assert_expr(cb.or_expr(or_values), "canvas_margin_domain_in_range")

		bg_values = []
		for background_value in background_color.domain:
			bg_values.append(cb.eq(background_color.name, background_value))
		constraints += cb.assert_expr(cb.or_expr(or_values), "canvas_background_color_domain_in_range")
		page_shape = canvas.children[0]

		# page shape should stay within the bounds of the canvas container
		# minus the current margin value. 
		constraints += cb.assert_expr(cb.gte(page_shape.variables.x.id, cb.add(canvas_x.id, margin.id)), 
			page_shape.shape_id + "_gt_canvas_x")
		constraints += cb.assert_expr(cb.gte(page_shape.variables.y.id, cb.add(canvas_y.id, margin.id)), 
			page_shape.shape_id + "_gt_canvas_y")
		constraints += cb.assert_expr(cb.lte(cb.add(page_shape.variables.x.id, 
			str(page_shape.computed_width())), cb.sub(cb.add(canvas_x.id, 
				str(canvas.computed_width())), margin.id)), 
			page_shape.shape_id + "_gt_canvas_right")
		constraints += cb.assert_expr(cb.lte(cb.add(page_shape.variables.y.id, 
			str(page_shape.computed_height())), cb.sub(cb.add(canvas_y.id, 
				str(canvas.computed_height())), margin.id)), 
			page_shape.shape_id + "_gt_canvas_bottom")

		# Fix the canvas X,Y to their original valuess
		constraints += cb.assert_expr(cb.eq(canvas_x.id, str(canvas.x)), 'canvas_orig_x')
		constraints += cb.assert_expr(cb.eq(canvas_y.id, str(canvas.y)), 'canvas_orig_y')

		constraints += self.justify_canvas(canvas)
		constraints += self.align_canvas(canvas)
		constraints += self.init_grid_constraints(canvas)
		return constraints

	def init_grid_constraints(self, canvas): 
		grid = canvas.variables.grid
		grid_values = []
		for grid_value in grid.domain:
			grid_values.append(cb.eq(grid.id, str(grid_value)))
		return cb.assert_expr(cb.or_expr(grid_values), "canvas_grid_in_domain")

	def init_container_constraints(self, container, shapes):
		arrangement = container.variables.arrangement.id
		alignment = container.variables.alignment.id
		proximity = container.variables.proximity.id
		container_x = container.variables.x.id
		container_y = container.variables.y.id
		distribution = container.variables.distribution.id

		# Limit domains to the set of variable values
		constraints = ""
		constraints += cb.assert_expr(cb.gte(arrangement, "0"), "container_" + container.shape_id + "_arrangement_gt_0")
		constraints += cb.assert_expr(cb.lt(arrangement, str(len(container.variables.arrangement.domain))),
			"container_" + container.shape_id + "_arrangement_lt_domain" )
		constraints += cb.assert_expr(cb.gte(alignment, "0"), "container_" + container.shape_id + "_alignment_gt_0")
		constraints += cb.assert_expr(cb.lt(alignment, str(len(container.variables.alignment.domain))),
			"container_" + container.shape_id + "_alignment_lt_domain")

		# These two variables do not have variable values that correspond to an index 
		# so create an OR constraint instead
		proximity_values = []
		distribution_values = []
		for prox_value in container.variables.proximity.domain:
			proximity_values.append(cb.eq(proximity, str(prox_value)))

		for dist_value in container.variables.distribution.domain: 
			distribution_values.append(cb.eq(distribution, str(dist_value)))

		constraints += cb.assert_expr(cb.or_expr(distribution_values), "container_" 
			+ container.shape_id + "_distribution_in_domain")
		constraints += cb.assert_expr(cb.or_expr(proximity_values), "container_"
			+ container.shape_id + "_proximity_in_domain")

		# Enforce children constraints
		child_shapes = container.children
		if len(child_shapes): 
			has_group = False
			for s_index in range(0, len(child_shapes)): 
				shape1 = child_shapes[s_index]
				if shape1.type == "container" and shape1.shape_type != "labelGroup": 
					has_group = True

					# Enforce that the child container proximity value (closeness) should always be smaller than the distribution value 
					# Of the parent container so that they are more likely to appear as a cohesive element
					constraints += cb.assert_expr(cb.lt(shape1.variables.proximity.id, container.variables.distribution.id), 
						"child_shape_" + shape1.shape_id + "_proximity_wt_group_lt_parent_distribution_" + container.shape_id)

					constraints += cb.assert_expr(cb.lt(shape1.variables.proximity.id, container.variables.proximity.id), 
						"child_shape_" + shape1.shape_id + "_proximity_wt_group_lt_parent_proximity_" + container.shape_id)

				shape1_x = shape1.variables.x.id
				shape1_y = shape1.variables.y.id
				shape1_width = str(shape1.computed_width())
				shape1_height = str(shape1.computed_height())

				bottom_axis = shape1.variables.baseline.id if shape1.has_baseline else cb.add(shape1_y, shape1_height)

				# Shapes cannot exceed the bounds of their parent containers
				constraints += cb.assert_expr(cb.gte(shape1_x, container_x), 
					"child_shape_" + shape1.shape_id + "_within_parent_container_" + container.shape_id + "_left")
				constraints += cb.assert_expr(cb.gte(shape1_y, container_y), 
					"child_shape_" + shape1.shape_id + "_within_parent_container_" + container.shape_id + "_top")

				constraints += cb.assert_expr(cb.lte(cb.add(shape1_x, shape1_width), 
					cb.add(container_x, str(container.computed_width()))),
					"child_shape_" + shape1.shape_id + "_lt_parent_width")
				constraints += cb.assert_expr(cb.lte(bottom_axis, 
					cb.add(container_y, str(container.computed_height()))),
					"child_shape_" + shape1.shape_id + "_lt_parent_height")

				# Create importance level constraints
				if shape1.type == "leaf": 
					constraints += self.init_importance(shape1, container)

			# # If this is a hierarchical container, use the distribution variable. 
			# # If this is a bottom level group, using the proximity value 
			use_distribution = (has_group and not container.typed) or container.container_type == "page"
			spacing = container.variables.distribution.id if use_distribution else container.variables.proximity.id
			
			constraints += self.arrange_container(container, spacing)
			constraints += self.align_container(container, spacing)
			constraints += self.non_overlapping(container, spacing)
			return constraints

			# if container.typed: 
			# 	time_start = time.time()
			# 	# If this is a typed container, enforce all variables on child containers to be the same
			# 	self.init_repeat_group(container, shapes)
			# 	time_end = time.time()
			# 	print("Time to init repeat group: " + str(time_end-time_start))

	def init_importance(self, shape, container): 
		constraints = ""
		if shape.importance == "most":
			# Enforce the max size
			constraints += cb.assert_expr(cb.lte(str(shape.computed_width()), str(shapes.maximum_sizes[shape.shape_type])), 
				"shape_" + shape.shape_id + "_width_lt_maximum_width")
			constraints += cb.assert_expr(cb.lte(str(shape.computed_height()), str(shapes.maximum_sizes[shape.shape_type])), 
				"shape_" + shape.shape_id + "_height_lt_maximum_height")	

			magnification = []
			for domain_value in shape.variables.magnification.domain: 
				magnification.append(cb.eq(shape.variables.magnification.id, str(domain_value)))

			constraints += cb.assert_expr(cb.or_expr(magnification), 
				"shape_" + shape.shape_id + "_magnification_wt_domain.")

		if shape.importance == "least":
			# Enforce the max size
			constraints += cb.assert_expr(cb.gte(str(shape.computed_width()), str(shapes.minimum_sizes[shape.shape_type])), 
				"shape_" + shape.shape_id + "_width_lte_minimum_width")
			constraints += cb.assert_expr(cb.gte(str(shape.computed_height()), str(shapes.minimum_sizes[shape.shape_type])), 
				"shape_" + shape.shape_id + "_height_lte_minimum_height")	

			minification = []
			for domain_value in shape.variables.minification.domain: 
				minification.append(cb.eq(shape.variables.minification.id, str(domain_value)))

			constraints += cb.assert_expr(cb.or_expr(minification), 
				"shape_" + shape.shape_id + "_minification_wt_domain.")

		if container.importance == "most": 
			constraints += cb.assert_expr(cb.eq(container.variables.magnification.id, shape.variables.magnification.id), 
				"shape_" + shape.shape_id + "_magnification_eq_parent")

		if container.importance == "least": 
			constraints += cb.assert_expr(cb.eq(container.variables.minification.id, shape.variables.minification.id), 
				"shape_" + shape.shape_id + "_minification_eq_parent")
		return constraints

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
					groups_same = group1_variable.z3 == group2_variable.z3

					if group1_key != "x" and group1_key != "y": 
						if j < len(all_same_values): 
							all_same_values[j].append(groups_same)
						else: 
							all_same_values.append([groups_same])

		for all_same_variables in all_same_values: 
			# For each collection of child variable values for a variable
			# Enforce all values of that collection to be thes ame 
			self.solver.add(And(all_same_variables, self.solver.ctx))

		# The order of the elements within the groups should be uniform
		for group in subgroups:
			group_children = group.children
			for i in range(0, len(group_children)-1):
				child1 = group_children[i]
				child2 = group_children[i+1]
				child1_left = child1.variables.x.z3 + child1.computed_width() < child2.variables.x.z3
				child1_above = child1.variables.y.z3 + child1.computed_height() < child2.variables.y.z3
				child1_left_or_above = Or(child1_left, child1_above, self.solver.ctx)
		
				for j in range(0, len(child1.correspondingIDs)):
					child1_corrID = child1.correspondingIDs[j]
					child2_corrID = child2.correspondingIDs[j]
					child1_corr_shape = shapes[child1_corrID]
					child2_corr_shape = shapes[child2_corrID]
		
					child1_corr_left = child1_corr_shape.variables.x.z3 + child1_corr_shape.computed_width() < child2_corr_shape.variables.x.z3
					child1_corr_above = child1_corr_shape.variables.y.z3 + child1_corr_shape.computed_height() < child2_corr_shape.variables.y.z3
					child1_corr_left_or_above = Or(child1_corr_left, child1_corr_above, self.solver.ctx)

					child2_corr_left = child2_corr_shape.variables.x.z3 + child2_corr_shape.computed_width() < child1_corr_shape.variables.x.z3
					child2_corr_above = child2_corr_shape.variables.y.z3 + child2_corr_shape.computed_height() < child1_corr_shape.variables.y.z3
					child2_corr_left_or_above = Or(child2_corr_left, child2_corr_above, self.solver.ctx)

					order_pair = If(child1_left_or_above, child1_corr_left_or_above, child2_corr_left_or_above)
					self.solver.add(order_pair, container.shape_id + " " + group.shape_id + " Repeat Group: Enforce order of subgroups")

	def init_locks(self, shape): 
		# Add constraints for all of the locked properties
		if shape.locks is not None: 
			for lock in shape.locks:
				# Structure message for these constraints to have a specific format so they can be used to identify conflicts in the generated solutions
				self.solver.add(shape.variables[lock].z3 == shape.variable_values[lock], "lock_" + shape.shape_id + "_" + shape.variables[lock].name + "_" + str(shape.variable_values[lock]))

	def non_overlapping(self, container, spacing): 
		constraints = ""
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
					constraints += cb.assert_expr(cb.or_expr([left,right,top,bottom]), 
						"non_overlapping_shapes_" + shape1.shape_id + "_" + shape2.shape_id)
		return constraints

	def get_row_width(self, row, spacing):
		width = 0
		for i in range(0, len(row)):
			if i < len(row) - 1:
				width += row[i].computed_width() + spacing
			else:
				width += row[i].computed_width()
		return width

	def get_column_height(self, column, spacing):
		height = 0
		for i in range(0, len(column)):
			if i < len(column) - 1:
				height += column[i].computed_height() + spacing
			else:
				height += column[i].computed_height()
		return height

	def get_widest_row_constraint(self, row_i, widest_i, rows, spacing):
		widest_row = rows[widest_i]
		widest_row_width = self.get_row_width(widest_row, spacing)

		if row_i < len(rows):
			next_row = rows[row_i]
			next_row_width = self.get_row_width(next_row, spacing)
			return If(widest_row_width > next_row_width, self.get_widest_row_constraint(row_i+1, widest_i, rows, spacing), self.get_widest_row_constraint(row_i+1, row_i, rows, spacing))
		else:
			return widest_row_width

	def get_tallest_column_constraint(self, column_i, tallest_i, columns, spacing):
		tallest_column = columns[tallest_i]
		tallest_column_height = self.get_column_height(tallest_column, spacing)
		if column_i < len(columns):
			next_column = columns[column_i]
			next_column_height = self.get_column_height(next_column, spacing)
			return If(tallest_column_height > next_column_height, self.get_tallest_column_constraint(column_i+1, tallest_i, columns, spacing), self.get_tallest_column_constraint(column_i+1, column_i, columns, spacing))
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

	def get_max_height_constraint(self, child_i, tallest_i, child_shapes): 
		if child_i < len(child_shapes): 
			tallest_child = child_shapes[tallest_i]
			tallest_child_height = str(tallest_child.computed_height())

			next_child = child_shapes[child_i]
			next_child_height=  str(next_child.computed_height())
			return cb.ite(cb.gt(tallest_child_height, next_child_height),
				self.get_max_height_constraint(child_i+1, tallest_i, child_shapes), 
				self.get_max_height_constraint(child_i+1, child_i, child_shapes))
		else: 
			child_shape_height = str(child_shapes[tallest_i].computed_height())
			return child_shape_height

	def justify_canvas(self, canvas):
		justification = canvas.variables.justification
		margin = canvas.variables.margin
		canvas_y = canvas.variables.y
		
		first_child = canvas.children[0]
		child_y = first_child.variables.y.id

		# Canvas justification (because the canvas is the only type of container right now not sizing to its contents)
		constraints = ""
		t_index = justification.domain.index("top")
		c_index = justification.domain.index("center")
		is_top = cb.eq(justification.id, str(t_index))
		is_center = cb.eq(justification.id, str(c_index))
		top_justified = cb.eq(child_y, cb.add(canvas_y.id, margin.id))

		first_child_height = str(first_child.computed_height())
		bottom_justified = cb.eq(cb.add(child_y, first_child_height),
								 cb.add(canvas_y.id, cb.sub(str(canvas.computed_height()), margin.id)))
		center_justified = cb.eq(cb.add(child_y, cb.div(first_child_height, "2")),
							  	 cb.add(canvas_y.id, cb.div(str(canvas.computed_height()), "2")))
		constraints += cb.assert_expr(cb.ite(is_top, top_justified,
											 cb.ite(is_center, center_justified, bottom_justified)),
								   'canvas_justification')
		return constraints

	def align_canvas(self, canvas):
		alignment = canvas.variables.alignment
		margin = canvas.variables.margin
		canvas_x = canvas.variables.x

		first_child = canvas.children[0]
		child_x = first_child.variables.x

		# Canvas aligment is different than other containers since there is no concept of arrangement
		constraints = ""
		l_index = alignment.domain.index("left")
		c_index = alignment.domain.index("center")
		is_left = cb.eq(alignment.id, str(l_index))
		is_center = cb.eq(alignment.id, str(c_index))
		left_aligned = cb.eq(child_x.id, cb.add(canvas_x.id, margin.id))
		first_child_width = first_child.computed_width()
		center_aligned = cb.eq(cb.add(child_x.id, cb.div(str(first_child_width),"2")), 
			cb.add(canvas_x.id, cb.div(str(canvas.computed_width()),"2")))
		right_aligned = cb.eq(cb.add(child_x.id, str(first_child_width)), 
			cb.add(canvas_x.id, cb.sub(str(canvas.computed_width()), margin.id)))
		constraints += cb.assert_expr(cb.ite(is_left, left_aligned, 
			cb.ite(is_center, center_aligned, right_aligned)), 'canvas_alignment')
		return constraints

	def align_rows_or_columns(self, container, proximity, rows, column_or_row,
							  aligned_axis, aligned_axis_size, layout_axis, layout_axis_size):
		constraints = []
		l_index = container.variables.alignment.domain.index("left")
		c_index = container.variables.alignment.domain.index("center")
		is_left = container.variables.alignment.z3 == l_index
		is_center = container.variables.alignment.z3 == c_index
		for row in rows: 
			for i in range(len(row)-1): 
				shape1 = row[i]
				shape2 = row[i+1]

				aligned_axis_size_value = shape1.computed_width() if aligned_axis_size == "width" else shape1.computed_height()
				aligned_axis_size_value2 = shape2.computed_width() if aligned_axis_size == "width" else shape2.computed_height()

				left_top_aligned = shape1.variables[aligned_axis].z3 == shape2.variables[aligned_axis].z3
				right_bottom_aligned = (shape1.variables[aligned_axis].z3 + aligned_axis_size_value) == (shape2.variables[aligned_axis].z3 + aligned_axis_size_value2)
				center_aligned = (shape1.variables[aligned_axis].z3 + (aligned_axis_size_value/2)) == (shape2.variables[aligned_axis].z3 + (aligned_axis_size_value2/2))
				constraints.append(If(is_left, left_top_aligned, If(is_center, center_aligned, right_bottom_aligned)))

				# Shape 2 is exactly to the right of shape 1 or to the bottom if in a column 
				layout_axis_size_value = shape1.computed_width() if layout_axis_size == "width" else shape1.computed_height()
				constraints.append((shape1.variables[layout_axis].z3 + layout_axis_size_value + proximity) == shape2.variables[layout_axis].z3)
		if len(constraints):
			return And(constraints, self.solver.ctx)
		return True

	def align_left_or_top(self, rows, proximity, column_or_row, aligned_axis, below_or_right_axis, width_or_height):
		constraints = []
		for i in range(0, len(rows)-1):
			row1 = rows[i] 
			row2 = rows[i+1]
			if len(row1) > 0 and len(row2) > 0: 
				shape1 = row1[0]
				shape2 = row2[0]

				# Width or height of shape1 
				w_or_h = shape1.computed_width() if width_or_height == "width" else shape1.computed_height()

				# Shape1 row is left or top aligned to shape2 row
				constraints.append(shape1.variables[aligned_axis].z3 == shape2.variables[aligned_axis].z3)

				# shape2 row is below or to the right of shape1 row
				constraints.append(((shape1.variables[below_or_right_axis].z3 + w_or_h) + proximity) <= shape2.variables[below_or_right_axis].z3)
		if len(constraints):
			return And(constraints, self.solver.ctx)
		return True

	def set_container_size_main_axis(self, container, proximity, rows_or_columns, width_or_height):
		size = 0
		num_rows_or_columns = len(rows_or_columns)
		for i in range(0, num_rows_or_columns):
			row_or_column = rows_or_columns[i]
			if len(row_or_column):
				spacing = proximity if i < num_rows_or_columns - 1 else 0
				m_height_or_width = self.get_max_width_constraint(1,0,row_or_column) if width_or_height == "width" else self.get_max_height_constraint(1,0,row_or_column)
				size += m_height_or_width + spacing
		container_size = container.computed_width() if width_or_height == "width" else container.computed_height()
		return container_size == size

	def set_container_size_cross_axis(self, container, proximity, rows_or_columns, width_or_height):
		size = self.get_widest_row_constraint(1, 0, rows_or_columns, proximity) if width_or_height == "width" else self.get_tallest_column_constraint(1, 0, rows_or_columns, proximity)
		container_size = container.computed_width() if width_or_height == "width" else container.computed_height()
		return container_size == size

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

		constraints = ""
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

				constraints += cb.assert_expr(cb.ite(is_vertical, vertical_arrange, "true"),
					"container_" + container.shape_id + "_vertical_arrangement")
				constraints += cb.assert_expr(cb.ite(is_horizontal, horizontal_arrange, "true"), 
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
				constraints += cb.assert_expr(cb.ite(is_vertical, is_bottom, "true"), "container_" + container.shape_id + "_vertical_order_last_child")
				constraints += cb.assert_expr(cb.ite(is_horizontal, is_right, "true"), "container_" + container.shape_id + "_horizontal_order_last_child")

			if child.order == 0:
				is_top = cb.eq(child_y, container_y)
				is_left = cb.eq(child_x, container_x)
				constraints += cb.assert_expr(cb.ite(is_vertical, is_top, "true"), child.shape_id + "_" + container.shape_id + "_first_order_top")
				constraints += cb.assert_expr(cb.ite(is_horizontal, is_left, "true"), child.shape_id + "_" + container.shape_id + "_first_order_left")

		# Set the width and height of the container based on the arrangement axis 
		constraints += cb.assert_expr(cb.ite(is_vertical, cb.eq(str(container.computed_height()), child_heights), "true"), 
			"container_" + container.shape_id + "_child_heights_vertical")
		constraints += cb.assert_expr(cb.ite(is_horizontal, cb.eq(str(container.computed_width()), child_widths), "true"), 
			"container_" + container.shape_id + "_child_widths_horizontal")

		m_w_constraint = cb.eq(str(container.computed_width()), (self.get_max_width_constraint(1,0,child_shapes)))
		m_h_constraint = cb.eq(str(container.computed_height()), (self.get_max_height_constraint(1,0,child_shapes)))
		constraints += cb.assert_expr(cb.ite(is_vertical, m_w_constraint, "true"), 
			"container_" + container.shape_id + "_max_width_vertical")
		constraints += cb.assert_expr(cb.ite(is_horizontal, m_h_constraint, "true"), 
			"container_" + container.shape_id + "_max_height_horizontal")

		# # only initialize the row and column constraints if there are more than 2 children 
		# if len(container.children) > 2:
		# 	groups = self.split_children_into_groups(container)
		# 	self.solver.add(If(is_rows, self.align_rows_or_columns(container, spacing, groups, "row", "y", "height", "x", "width"), True), container.shape_id + " align rows")
		# 	self.solver.add(If(is_columns, self.align_rows_or_columns(container, spacing, groups, "column", "x", "width", "y", "height"), True), container.shape_id + " align columns")
		# 	self.solver.add(If(is_rows, self.align_left_or_top(groups, spacing, "row", "x", "y", "height"), True), container.shape_id + " align rows left")
		# 	self.solver.add(If(is_columns, self.align_left_or_top(groups, spacing, "column", "y", "x", "width"), True), container.shape_id + " align columns left ")
		# 	self.solver.add(If(is_rows, self.set_container_size_main_axis(container, spacing, groups, "height"), True), container.shape_id + " max row height")
		# 	self.solver.add(If(is_columns, self.set_container_size_main_axis(container, spacing, groups, "width"), True), container.shape_id + " max row width")
		# 	self.solver.add(If(is_rows, self.set_container_size_cross_axis(container, spacing, groups, "width"), True), container.shape_id + " max container height from rows")
		# 	self.solver.add(If(is_columns, self.set_container_size_cross_axis(container, spacing, groups, "height"), True), container.shape_id + " max container width from columns")
		# else:
		# Prevent columnns and rows variables if there are 2 children or less
		constraints += cb.assert_expr(cb.neq(arrangement.id, str(rows_index)))
		constraints += cb.assert_expr(cb.neq(arrangement.id, str(columns_index)))
		return constraints

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
		constraints = ""
		for child in child_shapes:
			time_start = time.time()
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
			time_end = time.time()
			print("Time to create child alignment constraints: " + str(time_end-time_start))
			
			time_start = time.time()
			constraints += cb.assert_expr(cb.ite(is_vertical, vertical, "true"), 
				"container_" + container.shape_id + "_" + child.shape_id + "_vertical_alignment")
			constraints += cb.assert_expr(cb.ite(is_horizontal, horizontal, "true"), 
				"container_" + container.shape_id + "_" + child.shape_id + "_horizontal_alignment") 
			time_end = time.time()

			print("Time to add child alignment constraints to the solver: " + str(time_end-time_start))
		return constraints