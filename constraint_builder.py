from z3 import *
import shapes
import math

def abs(x):
	return If(x>=0,x,-x)

class ConstraintBuilder(object):
	def __init__(self, solver): 
		# So we can override the add method for debugging
		self.solver = solver

	def init_previous_solution_constraints(self, previous_solutions, shapes): 
		# Saved solutions should not appear again in the results
		for solution in previous_solutions: 
			elements = solution["elements"]
			if (not "added" in solution and not "removed" in solution) or (not len(solution["added"]) and not len(solution["removed"])):
				all_values = self.get_previous_solution_constraints_from_elements(shapes, elements)

				# Prevent the exact same set of values from being produced again (Not an And on all of the constraints)
				self.solver.add(Not(And(all_values, self.solver.ctx)), "prevent previous solution " + solution["id"] + " values")

	def init_solution_constraints(self, shapes, elements, solutionID):
		# Get the constraints for checking the validity of the previous solution
		all_values = self.get_solution_constraints_from_elements(shapes, elements)

		# All of the variables that were set for this solution should be maintained
		for value in all_values:
			self.solver.add(value, "fix solution " + solutionID + " values " + str(value))

	def get_previous_solution_constraints_from_elements(self, shapes, elements):
		all_values = []
		for elementID in elements:
			element = elements[elementID]

			# Get the shape corresponding to the element name
			shape = shapes[elementID]
			variables = shape.variables.toDict()
			if shape.type == "leaf":
				for variable_key in variables.keys(): 
					variable = variables[variable_key]
					all_values.append(variable.z3 == variable.get_value_from_element(element))
		return all_values

	def get_solution_constraints_from_elements(self, shapes, elements): 
		all_values = []
		for elementID in elements:
			element = elements[elementID]

			# Get the shape corresponding to the element name
			shape = shapes[elementID]

			variables = shape.variables.toDict()
			for variable_key in variables.keys(): 
				variable = variables[variable_key]
				if variable.name != "baseline": 
					all_values.append(variable.z3 == variable.get_value_from_element(element))

		return all_values	

	def init_shape_baseline(self, shape): 
		if shape.has_baseline:
			self.solver.add(shape.variables.baseline.z3 == shape.variables.y.z3 + shape.orig_baseline, "baseline " + shape.shape_id)

	def init_shape_bounds(self, shape, canvas_width, canvas_height):
		self.solver.add(shape.variables.x.z3 >= 0, shape.shape_id + " x must be greater than zero.")
		self.solver.add((shape.variables.x.z3 + shape.computed_width()) <= canvas_width, shape.shape_id + " right must be less than width.")
		self.solver.add(shape.variables.y.z3 >= 0, shape.shape_id + " y must be greater than zero.")
		self.solver.add((shape.variables.y.z3 + shape.computed_height()) <= canvas_height, shape.shape_id + " bottom must be less than height.")

	def init_shape_grid_values(self, shape, canvas): 
		grid = canvas.variables.grid.z3
		shape_x = shape.variables.x.z3
		# shape_y = shape.variables.y.z3
		# self.solver.add((shape_x % grid) == 0, shape.shape_id + " x multiple of grid value.")
		# self.solver.add((shape_y % grid) == 0, shape.shape_id + " y multiple of grid value.")

	def init_canvas_constraints(self, canvas): 
		alignment = canvas.variables.alignment
		justification = canvas.variables.justification
		margin = canvas.variables.margin
		background_color = canvas.variables.background_color
		canvas_x = canvas.variables.x.z3
		canvas_y = canvas.variables.y.z3

		print('add first constraint')
		self.solver.add(alignment.z3 >= 0, 'canvas_alignment domain lowest')
		print('add second constraint')
		self.solver.add(alignment.z3 < len(alignment.domain), 'canvas_alignment domain highest')
		self.solver.add(justification.z3 >= 0, 'canvas_justification domain lowest')
		self.solver.add(justification.z3 < len(justification.domain), 'canvas justification domain highest')

		or_values = []
		for margin_value in margin.domain:
			or_values.append(margin.z3 == margin_value)
		self.solver.add(Or(or_values, self.solver.ctx), "canvas margin domain in range")

		bg_values = []
		for background_value in background_color.domain:
			bg_values.append(background_color.z3 == background_value)
		self.solver.add(Or(bg_values, self.solver.ctx), "canvas background_color domain in range")

		page_shape = canvas.children[0]
		# page shape should stay within the bounds of the canvas container
		# minus the current margin value. 
		self.solver.add(page_shape.variables.x.z3 >= (canvas_x + margin.z3), page_shape.shape_id + ' gt canvas_x')
		self.solver.add(page_shape.variables.y.z3 >= (canvas_y + margin.z3), page_shape.shape_id + ' gt canvas_y')
		self.solver.add((page_shape.variables.x.z3 + page_shape.computed_width()) <= (canvas_x + canvas.computed_width() - margin.z3), page_shape.shape_id + ' gt canvas_right')
		self.solver.add((page_shape.variables.y.z3 + page_shape.computed_height()) <= (canvas_y + canvas.computed_height() - margin.z3), page_shape.shape_id + ' gt canvas_bottom')

		# Fix the canvas X,Y to their original valuess
		self.solver.add(canvas_x == canvas.x, 'canvas orig x')
		self.solver.add(canvas_y == canvas.y, 'canvas orig y')

		self.justify_canvas(canvas)
		self.align_canvas(canvas)
		self.init_grid_constraints(canvas)

	def init_grid_constraints(self, canvas): 
		grid = canvas.variables.grid
		grid_values = []
		for grid_value in grid.domain:
			grid_values.append(grid.z3 == grid_value)
		self.solver.add(Or(grid_values, self.solver.ctx), "canvas grid value is within the domain")

	def init_container_constraints(self, container, shapes):
		arrangement = container.variables.arrangement.z3
		alignment = container.variables.alignment.z3
		proximity = container.variables.proximity.z3
		container_x = container.variables.x.z3
		container_y = container.variables.y.z3
		distribution = container.variables.distribution.z3
		# num_rows = container.variables.num_rows.z3

		# Limit domains to the set of variable values
		self.solver.add(arrangement >= 0, "container " + container.shape_id + " arrangment greater than zero")
		self.solver.add(arrangement < len(container.variables.arrangement.domain), "container " + container.shape_id + " arrangment less than domain")
		self.solver.add(alignment >= 0, "container " + container.shape_id + " alignment greater than zero")
		self.solver.add(alignment < len(container.variables.alignment.domain), "container " + container.shape_id + " alignment less than domain")
		# self.solver.add(num_rows >= 0, "container " + container.shape_id + " num_rows greater than zero")
		# self.solver.add(num_rows < len(container.variables.num_rows.domain), "container " + container.shape_id + " num_rows less than domain")

		# These two variables do not have variable values that correspond to an index so create an OR constraint instead
		proximity_values = []
		distribution_values = []
		for prox_value in container.variables.proximity.domain:
			proximity_values.append(proximity == prox_value)

		for dist_value in container.variables.distribution.domain: 
			distribution_values.append(distribution == dist_value)

		distribution_domain = Or(distribution_values, self.solver.ctx)
		self.solver.add(distribution_domain, "container " + container.shape_id + " distribution in domain")

		proximity_domain = Or(proximity_values, self.solver.ctx)
		self.solver.add(proximity_domain, "container " + container.shape_id + " proximity in domain")

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
					self.solver.add(shape1.variables.proximity.z3 < container.variables.distribution.z3, 
						shape1.shape_id + " proximity within group should be less than parent container " + container.shape_id + " distribution")
					self.solver.add(shape1.variables.proximity.z3 < container.variables.proximity.z3, 
						shape1.shape_id + " proximity within group should be less than parent container " + container.shape_id + " proximity")

				shape1_x = shape1.variables.x.z3
				shape1_y = shape1.variables.y.z3
				shape1_width = shape1.computed_width()
				shape1_height = shape1.computed_height()

				bottom_axis = shape1.variables.baseline.z3 if shape1.has_baseline else shape1_y + shape1_height

				# Shapes cannot exceed the bounds of their parent containers
				self.solver.add(shape1_x >= container_x, "child shape " + shape1.shape_id + " inside parent container (greater than left)")
				self.solver.add(shape1_y >= container_y, "child shape " + shape1.shape_id + " inside parent container (greater than top)")

				restrict_width = (shape1_x + shape1_width) <= (container_x + container.computed_width())
				self.solver.add(restrict_width, "child shape " + shape1.shape_id + " inside parent container (less than width)")
				self.solver.add(bottom_axis <= (container_y + container.computed_height()), "child shape " + shape1.shape_id + " inside parent container (less than height)")

				# Create importance level constraints
				if shape1.type == "leaf": 
					self.init_importance(shape1, container)

			# If this is a hierarchical container, use the distribution variable. 
			# If this is a bottom level group, using the proximity value 
			use_distribution = (has_group and not container.typed) or container.container_type == "page"
			spacing = container.variables.distribution.z3 if use_distribution else container.variables.proximity.z3
			
			self.arrange_container(container, spacing)
			self.align_container(container, spacing)
			self.non_overlapping(container, spacing)

			if container.typed: 
				# If this is a typed container, enforce all variables on child containers to be the same
				self.init_repeat_group(container, shapes)

	def init_importance(self, shape, container): 
		if shape.importance == "most":
			# Enforce the max size
			self.solver.add(shape.computed_width() <= shapes.maximum_sizes[shape.shape_type], "Shape " + shape.shape_id + " width must be less than the maximum size.")
			self.solver.add(shape.computed_height() <= shapes.maximum_sizes[shape.shape_type], "Shape " + shape.shape_id + " height must be less than the maximum size.")
			
			magnification = []
			for domain_value in shape.variables.magnification.domain: 
				magnification.append(shape.variables.magnification.z3 == domain_value)

			self.solver.add(Or(magnification, self.solver.ctx), "Shape " + shape.shape_id + " magnification values fall within domain.")

		if shape.importance == "least":
			# Enforce the minimum size
			set_min_width = shape.computed_width() >= shapes.minimum_sizes[shape.shape_type]
			self.solver.add(set_min_width, "Shape " + shape.shape_id + " width must be greater than the minimum size.")
			
			set_min_height = shape.computed_height() >= shapes.minimum_sizes[shape.shape_type]
			self.solver.add(set_min_height, "Shape " + shape.shape_id + " height must be greater than the minimum size.")

			minification = []
			for domain_value in shape.variables.minification.domain: 
				minification.append(shape.variables.minification.z3 == domain_value)

			self.solver.add(Or(minification, self.solver.ctx), "Shape " + shape.shape_id + " minification values fall within domain.")

		if container.importance == "most": 
			self.solver.add(container.variables.magnification.z3 == shape.variables.magnification.z3, "Shape " + shape.shape_id + " has magnification same as parent")

		if container.importance == "least": 
			self.solver.add(container.variables.minification.z3 == shape.variables.minification.z3, "Shape " + shape.shape_id + " has minification same as parent")

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
		child_shapes = container.children 
		for i in range(0, len(child_shapes)): 
			for j in range(0, len(child_shapes)): 
				if i != j: 
					shape1 = child_shapes[i]
					shape2 = child_shapes[j]
					shape1_x = shape1.variables.x.z3
					shape1_y = shape1.variables.y.z3
					shape2_x = shape2.variables.x.z3
					shape2_y = shape2.variables.y.z3
					shape1_width = shape1.computed_width()
					shape1_height = shape1.computed_height()
					shape2_width = shape2.computed_width()
					shape2_height = shape2.computed_height()

					# Non-overlapping
					left = shape1_x + shape1_width + spacing <= shape2_x
					right = shape2_x + shape2_width + spacing <= shape1_x
					top = shape1_y + shape1_height + spacing <= shape2_y
					bottom = shape2_y + shape2_height + spacing <= shape1_y
					self.solver.add(Or(left,right,top,bottom, self.solver.ctx), "Non-overlapping shapes " + shape1.shape_id + " " + shape2.shape_id)

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
			widest_child_width = widest_child.computed_width()

			next_child = child_shapes[child_i]
			next_child_width = next_child.computed_width()
			return If(widest_child_width > next_child_width, self.get_max_width_constraint(child_i+1, widest_i, child_shapes), self.get_max_width_constraint(child_i+1, child_i, child_shapes))
		else: 
			child_shape_width = child_shapes[widest_i].computed_width()
			return child_shape_width

	def get_max_height_constraint(self, child_i, tallest_i, child_shapes): 
		if child_i < len(child_shapes): 
			tallest_child = child_shapes[tallest_i]
			tallest_child_height = tallest_child.computed_height()

			next_child = child_shapes[child_i]
			next_child_height=  next_child.computed_height()
			return If(tallest_child_height > next_child_height, self.get_max_height_constraint(child_i+1, tallest_i, child_shapes), self.get_max_height_constraint(child_i+1, child_i, child_shapes))
		else: 
			child_shape_height = child_shapes[tallest_i].computed_height()
			return child_shape_height

	def justify_canvas(self, canvas):
		justification = canvas.variables.justification
		margin = canvas.variables.margin
		canvas_y = canvas.variables.y.z3
		
		first_child = canvas.children[0]
		child_y = first_child.variables.y.z3

		# Canvas justification (because the canvas is the only type of container right now not sizing to its contents)
		t_index = justification.domain.index("top")
		c_index = justification.domain.index("center")
		is_top = justification.z3 == t_index
		is_center = justification.z3 == c_index
		top_justified = child_y == (canvas_y + margin.z3)

		first_child_height = first_child.computed_height()
		bottom_justified = (child_y + first_child_height) == (canvas_y + canvas.computed_height() - margin.z3)
		center_justified = (child_y + (first_child_height/2)) == (canvas_y + (canvas.computed_height()/2))
		self.solver.add(If(is_top, top_justified, If(is_center, center_justified, bottom_justified)), 'canvas_justification')
		# self.solver.assert_and_track(If(is_top, top_justified, If(is_center, center_justified, bottom_justified)), "canvas_justification")

	def align_canvas(self, canvas):
		alignment = canvas.variables.alignment
		margin = canvas.variables.margin
		canvas_x = canvas.variables.x.z3

		first_child = canvas.children[0]
		child_x = first_child.variables.x.z3

		# Canvas aligment is different than other containers since there is no concept of arrangement
		l_index = alignment.domain.index("left")
		c_index = alignment.domain.index("center")
		is_left = alignment.z3 == l_index
		is_center = alignment.z3 == c_index
		left_aligned = child_x == (canvas_x + margin.z3)
		first_child_width = first_child.computed_width()
		center_aligned = (child_x + (first_child_width/2)) == (canvas_x + (canvas.computed_width()/2))
		right_aligned = (child_x + first_child_width) == (canvas_x + canvas.computed_width() - margin.z3)
		self.solver.add(If(is_left, left_aligned, If(is_center, center_aligned, right_aligned)), 'canvas_alignment')

	def align_rows_or_columns(self, container, proximity, rows, column_or_row, aligned_axis, aligned_axis_size, layout_axis, layout_axis_size):
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
		arrangement = container.variables.arrangement.z3
		container_x = container.variables.x.z3
		container_y = container.variables.y.z3

		# ====== Arrangement constraints =======
		# Vertical and horizontal arrangments
		# In order that elements were defined
		v_index = container.variables.arrangement.domain.index("vertical")
		is_vertical = arrangement == v_index

		h_index = container.variables.arrangement.domain.index("horizontal")
		is_horizontal = arrangement == h_index
		rows_index = container.variables.arrangement.domain.index("rows")
		is_rows = arrangement == rows_index
		columns_index = container.variables.arrangement.domain.index("columns")
		is_columns = arrangement == columns_index

		# not_rows = arrangement != rows_index
		# not_columns = arrangement != columns_index

		if container.container_order == "important": 
			vertical_pairs = []
			horizontal_pairs = []
			child_shapes = container.children
			for s_index in range(0, len(child_shapes)-1): 
				shape1 = child_shapes[s_index]
				shape1_x = shape1.variables.x.z3
				shape1_y = shape1.variables.y.z3

				shape2 = child_shapes[s_index+1]
				shape2_x = shape2.variables.x.z3
				shape2_y = shape2.variables.y.z3

				shape1_height = shape1.computed_height()
				vertical_pair_y = (shape1_y + shape1_height + spacing) == shape2_y
				vertical_pairs.append(vertical_pair_y)

				shape1_width = shape1.computed_width()
				horizontal_pair_x = (shape1_x + shape1_width + spacing) == shape2_x
				horizontal_pairs.append(horizontal_pair_x)

			vertical_arrange = And(vertical_pairs, self.solver.ctx)
			horizontal_arrange = And(horizontal_pairs, self.solver.ctx)
			self.solver.add(If(is_vertical, vertical_arrange, True), container.shape_id + " vertical arrangement")
			self.solver.add(If(is_horizontal, horizontal_arrange, True), container.shape_id + " horizontal arrangement")
			
		# Sum up the widths and heights
		child_widths = 0
		child_heights = 0
		child_shapes = container.children
		last_child_index = len(child_shapes) - 1

		# Enforce a max width or height of the container for horizontal or vertical
		for child_i in range(0, len(child_shapes)): 
			child = child_shapes[child_i]
			child_x = child.variables.x.z3
			child_y = child.variables.y.z3

			add_spacing = 0 if child_i == (len(child_shapes) - 1) else spacing
			child_widths += child.computed_width() + add_spacing
			child_heights += child.computed_height() + add_spacing

			if child.order == last_child_index: 
				# The bottom of the shape is the bottom of the container
				is_bottom = (child_y + child.computed_height()) == (container_y + container.computed_height())
				is_right = (child_x + child.computed_width()) == (container_x + container.computed_width())
				self.solver.add(If(is_vertical, is_bottom, True), container.shape_id + " vertical order last")
				self.solver.add(If(is_horizontal, is_right, True), container.shape_id + " horizontal order last")

			if child.order == 0:
				is_top = (child_y == container_y)
				is_left = (child_x == container_x)
				self.solver.add(If(is_vertical, is_top, True), child.shape_id + " " + container.shape_id + " first in order top")
				self.solver.add(If(is_horizontal, is_left, True), child.shape_id + " " + container.shape_id + " first in order left")


		# Set the width and height of the container based on the arrangement axis 
		self.solver.add(If(is_vertical, container.computed_height() == child_heights, True), container.shape_id + " child_heights vertical")
		self.solver.add(If(is_horizontal, container.computed_width() == child_widths, True), container.shape_id + " child widths horizontal")

		m_w_constraint = container.computed_width() == (self.get_max_width_constraint(1,0,child_shapes))
		m_h_constraint = container.computed_height() == (self.get_max_height_constraint(1,0,child_shapes))
		self.solver.add(If(is_vertical, m_w_constraint, True), container.shape_id + " max width vertical")
		self.solver.add(If(is_horizontal, m_h_constraint, True), container.shape_id + " max height horizontal")

		# only initialize the row and column constraints if there are more than 2 children 
		if len(container.children) > 2:
			groups = self.split_children_into_groups(container)
			self.solver.add(If(is_rows, self.align_rows_or_columns(container, spacing, groups, "row", "y", "height", "x", "width"), True), container.shape_id + " align rows")
			self.solver.add(If(is_columns, self.align_rows_or_columns(container, spacing, groups, "column", "x", "width", "y", "height"), True), container.shape_id + " align columns")
			self.solver.add(If(is_rows, self.align_left_or_top(groups, spacing, "row", "x", "y", "height"), True), container.shape_id + " align rows left")
			self.solver.add(If(is_columns, self.align_left_or_top(groups, spacing, "column", "y", "x", "width"), True), container.shape_id + " align columns left ")
			self.solver.add(If(is_rows, self.set_container_size_main_axis(container, spacing, groups, "height"), True), container.shape_id + " max row height")
			self.solver.add(If(is_columns, self.set_container_size_main_axis(container, spacing, groups, "width"), True), container.shape_id + " max row width")
			self.solver.add(If(is_rows, self.set_container_size_cross_axis(container, spacing, groups, "width"), True), container.shape_id + " max container height from rows")
			self.solver.add(If(is_columns, self.set_container_size_cross_axis(container, spacing, groups, "height"), True), container.shape_id + " max container width from columns")
		else:
			# Prevent columnns and rows variables
			self.solver.add(arrangement != rows_index)
			self.solver.add(arrangement != columns_index)

		# self.solver.add(If(is_rows, self.consecutive_rows_or_columns(container, "row"), True), container.shape_id + " consecutive rows")
		# self.solver.add(If(is_columns, self.consecutive_rows_or_columns(container, "column"),True), container.shape_id + " consecutive columns")
		# self.solver.add(If(is_rows, self.aligned_within_rows_or_columns(container, "row", "y", "height"), True), container.shape_id + " aligned rows")
		# self.solver.add(If(is_columns, self.alignedwithin_rows_or_columns(container, "column", "x", "width"),True), container.shape_id + " aligned columns")
		# self.solver.add(If(is_rows, self.aligned_across_rows_or_columns(container, "row", "y", "height"), True), container.shape_id + " aligned across columns")
		# self.solver.add(If(is_columns, self.aligned_across_rows_or_columns(container, "column", "x", "width"), True), container.shape_id + " aligned across rows")

		# self.solver.add(If(is_rows, self.no_gaps_in_rows_or_columns(container, "row", "x", "width"),True), container.shape_id + " no gaps rows")
		# self.solver.add(If(is_columns, self.no_gaps_in_rows_or_columns(container, "column", "y", "height"),True), container.shape_id + " no gaps columns")
		# self.solver.add(If(is_rows, self.child_rows_columns_in_domain(container, "row"), True, False), container.shape_id + " Child row within domain")
		# self.solver.add(If(is_columns, self.child_rows_columns_in_domain(container, "column"), True, False), container.shape_id + " Child column within domain")
		# self.solver.add(If(is_rows, self.correct_number_of_rows_columns(container, "row"), True, False), container.shape_id + " at least one in each row")
		# self.solver.add(If(is_columns, self.correct_number_of_rows_columns(container, "column"), True, False), container.shape_id + " at least one in each column")

	def align_container(self, container, spacing):
		alignment = container.variables.alignment
		arrangement = container.variables.arrangement
		container_x = container.variables.x
		container_y = container.variables.y

		l_index = alignment.domain.index("left")
		c_index = alignment.domain.index("center")
		is_left = alignment.z3 == l_index
		is_center = alignment.z3 == c_index
		v_index = arrangement.domain.index("vertical")
		is_vertical = arrangement.z3 == v_index
		h_index = arrangement.domain.index("horizontal")
		is_horizontal = arrangement.z3 == h_index

		# Alignment
		# Differs based on if the arrangment of the container is horizontal or vertical 
		child_shapes = container.children
		for child in child_shapes:
			child_x = child.variables.x.z3
			child_y = child.variables.y.z3

			bottom_axis = child.variables.baseline.z3 if child.has_baseline else child_y + child.computed_height()

			left_aligned = child_x == container_x.z3
			right_aligned = (child_x + child.computed_width()) == (container_x.z3 + container.computed_width())
			h_center_aligned = (child_x + (child.computed_width()/2)) == (container_x.z3 + (container.computed_width()/2))
			top_aligned = child_y == container_y.z3
			bottom_aligned = (bottom_axis) == (container_y.z3 + container.computed_height())
			v_center_aligned = (child_y + (child.computed_height()/2)) == (container_y.z3 + (container.computed_height()/2))
			horizontal = If(is_left, top_aligned, If(is_center, v_center_aligned, bottom_aligned))
			vertical = If(is_left, left_aligned, If(is_center, h_center_aligned, right_aligned))
			# self.solver.assert_and_track(If(is_vertical, vertical, horizontal), "alignment_constraint_" + container.shape_id + "_" + child.shape_id)
			self.solver.add(If(is_vertical, vertical, True), container.shape_id + " " + child.shape_id + " vertical alignment")
			self.solver.add(If(is_horizontal, horizontal, True), container.shape_id + " " + child.shape_id + " horizontal alignment")



