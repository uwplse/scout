from z3 import *
import shapes

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
				self.solver.add(Not(And(all_values)), "prevent previous solution " + solution["id"] + " values")

	def init_solution_constraints(self, shapes, elements, solutionID):
		# Saved solutions should not appear again in the results
		all_values = self.get_solution_constraints_from_elements(shapes, elements)

		# All of the variables that were set for this solution should be maintained (And constraint)
		if len(all_values): 
			self.solver.add(And(all_values), "prevent solution " + solutionID + " values")

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
				all_values.append(variable.z3 == variable.get_value_from_element(element))

		return all_values	

	def init_shape_bounds(self, shape, canvas_width, canvas_height):
		self.solver.add(shape.variables.x.z3 >= 0, shape.shape_id + " x must be greater than zero.")
		self.solver.add((shape.variables.x.z3 + shape.computed_width()) <= canvas_width, shape.shape_id + " right must be less than width.")
		self.solver.add(shape.variables.y.z3 >= 0, shape.shape_id + " y must be greater than zero.")
		self.solver.add((shape.variables.y.z3 + shape.computed_height()) <= canvas_height, shape.shape_id + " bottom must be less than height.")

	def init_canvas_constraints(self, canvas): 
		alignment = canvas.variables.alignment
		justification = canvas.variables.justification
		margin = canvas.variables.margin
		canvas_x = canvas.variables.x.z3
		canvas_y = canvas.variables.y.z3

		self.solver.add(alignment.z3 >= 0, 'canvas_alignment domain lowest')
		self.solver.add(alignment.z3 < len(alignment.domain), 'canvas_alignment domain highest')
		self.solver.add(justification.z3 >= 0, 'canvas_justification domain lowest')
		self.solver.add(justification.z3 < len(justification.domain), 'canvas justification domain highest')

		or_values = []
		for margin_value in margin.domain:
			or_values.append(margin.z3 == margin_value)
		self.solver.add(Or(or_values), "canvas margin domain in range")

		page_shape = canvas.children[0]
		# page shape should stay within the bounds of the canvas container
		# minus the current margin value. 
		self.solver.add(page_shape.variables.x.z3 >= (canvas_x + margin.z3), page_shape.shape_id + ' gt canvas_x')
		self.solver.add(page_shape.variables.y.z3 >= (canvas_y + margin.z3), page_shape.shape_id + ' gt canvas_y')
		self.solver.add((page_shape.variables.x.z3 + page_shape.computed_width()) <= (canvas_x + canvas.computed_width() - margin.z3), page_shape.shape_id + ' gt canvas_right')
		self.solver.add((page_shape.variables.y.z3 + page_shape.computed_height()) <= (canvas_y + canvas.computed_height() - margin.z3), page_shape.shape_id + ' gt canvas_bottom')

		# Fix the canvas X,Y to their original valuess
		self.solver.add(canvas_x == canvas.orig_x, 'canvas orig x')
		self.solver.add(canvas_y == canvas.orig_y, 'canvas orig y')

		self.justify_canvas(canvas)
		self.align_canvas(canvas)

	def init_container_constraints(self, container, shapes):
		arrangement = container.variables.arrangement.z3
		alignment = container.variables.alignment.z3
		proximity = container.variables.proximity.z3
		container_x = container.variables.x.z3
		container_y = container.variables.y.z3
		distribution = container.variables.distribution.z3

		# Limit domains to the set of variable values
		self.solver.add(arrangement >= 0, "container " + container.shape_id + " arrangment greater than zero")
		self.solver.add(arrangement < len(container.variables.arrangement.domain), "container " + container.shape_id + " arrangment less than domain")
		self.solver.add(alignment >= 0, "container " + container.shape_id + " alignment greater than zero")
		self.solver.add(alignment < len(container.variables.alignment.domain), "container " + container.shape_id + " alignment less than domain")

		# These two variables do not have variable values that correspond to an index so create an OR constraint instead
		proximity_values = []
		distribution_values = []
		for prox_value in container.variables.proximity.domain:
			proximity_values.append(proximity == prox_value)

		for dist_value in container.variables.distribution.domain: 
			distribution_values.append(distribution == dist_value)

		self.solver.add(Or(distribution_values), "container " + container.shape_id + " distribution in domain")
		self.solver.add(Or(proximity_values), "container " + container.shape_id + " proximity in domain")

		# Enforce children constraints
		child_shapes = container.children
		if len(child_shapes): 
			has_group = False
			for s_index in range(0, len(child_shapes)): 
				shape1 = child_shapes[s_index]
				if shape1.type == "container": 
					has_group = True

					# Enforce that the child container proximity value (closeness) should always be smaller than the distribution value 
					# Of the parent container so that they are more likely to appear as a cohesive element
					self.solver.add(shape1.variables.proximity.z3 < container.variables.distribution.z3, shape1.shape_id + " proximity within group should be less than parent container " + container.shape_id + " distribution")

				shape1_x = shape1.variables.x.z3
				shape1_y = shape1.variables.y.z3
				shape1_width = shape1.computed_height()
				shape1_height = shape1.computed_height()

				# Shapes cannot exceed the bounds of their parent containers
				self.solver.add(shape1_x >= container_x, "child shape " + shape1.shape_id + " inside parent container (greater than left)")
				self.solver.add(shape1_y >= container_y, "child shape " + shape1.shape_id + " inside parent container (greater than top)")
				self.solver.add((shape1_x + shape1_width) <= (container_x + container.computed_width()), "child shape " + shape1.shape_id + " inside parent container (less than width)")
				self.solver.add((shape1_y + shape1_height) <= (container_y + container.computed_height()), "child shape " + shape1.shape_id + " inside parent container (less than height)")

				# Create importance level constraints
				self.init_importance(shape1)

			# If this is a hierarchical container, use the distribution variable. 
			# If this is a bottom level group, using the proximity value 
			spacing = container.variables.distribution.z3 if has_group else container.variables.proximity.z3
			self.arrange_container(container, spacing)
			self.align_container(container, spacing)
			self.non_overlapping(container, spacing)

			if container.typed: 
				# If this is a typed container, enforce all variables on child containers to be the same
				self.init_repeat_group(container, shapes)

	def init_importance_domains(self, shape): 
		if shape.importance == "most": 
			magnification = []
			for domain_value in shape.variables.magnification.domain: 
				magnification.append(shape.variables.magnification.z3 == domain_value)
			# magnification.append(shape.variables.magnification.z3 == 0)

			self.solver.add(Or(magnification), "Shape " + shape.shape_id + " magnification values fall within domain.")
		elif shape.importance == "least": 
			minification = []
			for domain_value in shape.variables.minification.domain: 
				minification.append(shape.variables.minification.z3 == domain_value)
			# minification.append(shape.variables.minification.z3 == 0)

			self.solver.add(Or(minification), "Shape " + shape.shape_id + " minification values fall within domain.")

	def init_importance(self, shape): 
		# For shapes that have importance levels, they can increase or decrease but only to the minimum or maximum size. 
		if shape.importance == "most": 
			# Enforce the max size 
			self.solver.add(shape.computed_width() <= shapes.maximum_sizes[shape.shape_type], "Shape " + shape.shape_id + " width must be less than the maximum size.")
			self.solver.add(shape.computed_height()<= shapes.maximum_sizes[shape.shape_type], "Shape " + shape.shape_id + " height must be less than the maximum size.")
		elif shape.importance == "least": 
			# Enforce the minimum size 
			self.solver.add(shape.computed_width() >= shapes.minimum_sizes[shape.shape_type], "Shape " + shape.shape_id + " width must be greater than the minimum size.")
			self.solver.add(shape.computed_height() >= shapes.minimum_sizes[shape.shape_type], "Shape " + shape.shape_id + " height must be greater than the minimum size.")

		if shape.importance_set: 
			self.init_importance_domains(shape)

	def init_repeat_group(self, container, shapes): 
		subgroups = container.children
		all_same_values = []
		all_same_heights = []
		all_same_widths = []

		for i in range(0, len(subgroups)): 
			if i < len(subgroups) - 1: 
				group1 = subgroups[i]
				group2 = subgroups[i+1]
				group1_width = group1.computed_width()
				group1_height = group1.computed_height()
				group2_width = group2.computed_width()
				group2_height = group2.computed_height()

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

				# Keep the height and width of containers the same 
				all_same_widths.append(group1_width == group2_width)
				all_same_heights.append(group1_height == group2_height)

		for all_same_variables in all_same_values: 
			# For each collection of child variable values for a variable
			# Enforce all values of that collection to be thes ame 
			self.solver.add(And(all_same_variables))

		self.solver.add(And(all_same_heights))
		self.solver.add(And(all_same_widths))

		# Enforce that the corresponding shapes for each shape in the group items has same relational location
		# This should hopefully ensure that the order of the elements is uniform
		for group in subgroups: 
			group_children = group.children
			for i in range(0, len(group_children)-1): 
				child1 = group_children[i]
				child2 = group_children[i+1]
				x_distance = child1.variables.x.z3 - child2.variables.x.z3
				y_distance = child1.variables.y.z3 - child2.variables.y.z3
				for j in range(0, len(child1.correspondingIDs)): 
					child1_corrID = child1.correspondingIDs[j]
					child2_corrID = child2.correspondingIDs[j]
					child1_corr_shape = shapes[child1_corrID]
					child2_corr_shape = shapes[child2_corrID]
					x_distance2 = child1_corr_shape.variables.x.z3 - child2_corr_shape.variables.x.z3
					y_distance2 = child1_corr_shape.variables.y.z3 - child2_corr_shape.variables.y.z3
					self.solver.add(x_distance == x_distance2)
					self.solver.add(y_distance == y_distance2)

	def init_locks(self, shape): 
		# Add constraints for all of the locked properties
		# TODO: Make generic at some point
		if shape.locks is not None: 
			for lock in shape.locks:
				if lock == "location": 
					self.solver.add(shape.variables.y.z3 == shape.orig_y, "lock_" + shape.shape_id + "_" + shape.variables.y.name + "_" + str(shape.orig_y))
					self.solver.add(shape.variables.x.z3 == shape.orig_x, "lock_" + shape.shape_id + "_" + shape.variables.x.name + "_" + str(shape.orig_x))
				else: 
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
					self.solver.add(Or(left,right,top,bottom), "Non-overlapping shapes " + shape1.shape_id + " " + shape2.shape_id)

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
			next_child_height = next_child.computed_height()
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
		# self.solver.assert_and_track(If(is_left, left_aligned, If(is_center, center_aligned, right_aligned)), "canvas_alignment")

	
	def child_in_between(self, child_shapes, child1, child2, variable): 
		constraints = []
		for child in child_shapes: 
			if child.shape_id != child1.shape_id and child.shape_id != child2.shape_id: 
				constraint = If(Or(And(child.variables[variable].z3 > child1.variables[variable].z3, child.variables[variable].z3 < child2.variables[variable].z3),
								   And(child.variables[variable].z3 < child1.variables[variable].z3, child.variables[variable].z3 > child2.variables[variable].z3)), True, False)
				constraints.append(constraint)
		return Or(constraints)

	def consecutive_rows_or_columns(self, container, variable): 
		child_shapes = container.children
		constraints = []
		for i in range(0, len(child_shapes)): 
			for j in range(0, len(child_shapes)): 
				if i != j: 
					child1 = child_shapes[i]
					child2 = child_shapes[j]
					constraint = If((abs(child1.variables[variable].z3 - child2.variables[variable].z3) > 1), self.child_in_between(child_shapes, child1, child2, variable), True)
					constraints.append(constraint)
		return And(constraints)

	def aligned_pair(self, child1, child2, alignment, x_or_y, width_or_height): 
		l_index = alignment.domain.index("left")
		c_index = alignment.domain.index("center")
		is_left = alignment.z3 == l_index
		is_center = alignment.z3 == c_index
		w_or_h = child1.computed_width() if width_or_height == "width" else child1.computed_height()
		w_or_h2 = child2.computed_width() if width_or_height == "width" else child2.computed_height()

		left_aligned = child1.variables[x_or_y].z3 == child2.variables[x_or_y].z3
		center_aligned = ((child1.variables[x_or_y].z3 + (w_or_h/2)) == (child2.variables[x_or_y].z3 + (w_or_h2/2)))
		right_aligned = child1.variables[x_or_y].z3 + w_or_h == child2.variables[x_or_y].z3 + w_or_h2
		return If(is_left, left_aligned, If(is_center, center_aligned, right_aligned))

	def aligned_rows_or_columns(self, container, column_or_row, x_or_y, width_or_height): 
		child_shapes = container.children
		constraints = []
		for i in range(0, len(child_shapes)): 
			for j in range(0, len(child_shapes)): 
				if i != j: 
					child1 = child_shapes[i]
					child2 = child_shapes[j]
					constraint = If(child1.variables[column_or_row].z3 == child2.variables[column_or_row].z3,
						self.aligned_pair(child1, child2, container.variables.alignment, x_or_y, width_or_height),True)
					constraints.append(constraint)
		return And(constraints)

	def gap(self, child1, child2, x_or_y, width_or_height):
		w_or_h = child1.computed_width() if width_or_height == "width" else child1.computed_height()
		w_or_h2 = child2.computed_width() if width_or_height == "height" else child2.computed_width()

		gap1 = (child2.variables[x_or_y].z3 - (child1.variables[x_or_y].z3 + w_or_h))
		gap2 = (child1.variables[x_or_y].z3 - (child2.variables[x_or_y].z3 + w_or_h2))
		return If(child1.variables[x_or_y].z3 < child2.variables[x_or_y].z3, gap1, gap2)

	def in_between(self, child, child1, child2, x_or_y, width_or_height):
		constraint = If(Or(And(child.variables[x_or_y].z3 > child1.variables[x_or_y].z3, child.variables[x_or_y].z3 < child2.variables[x_or_y].z3), 
						And(child.variables[x_or_y].z3 < child1.variables[x_or_y].z3, child.variables[x_or_y].z3 > child2.variables[x_or_y].z3)), True, False)
		return constraint

	def no_children_between(self, child1, child2, child_shapes, column_or_row, x_or_y, width_or_height): 
		constraints = []
		for i in range(0, len(child_shapes)): 
			child = child_shapes[i]
			if child.shape_id != child2.shape_id and child.shape_id != child1.shape_id: 
				# ASsume that child1 and child2 are in the same row
				constraint = If(child.variables[column_or_row].z3 == child1.variables[column_or_row].z3, self.in_between(child, child1, child2, x_or_y, width_or_height), False)
				constraints.append(constraint)
		return Not(Or(constraints))

	def no_gaps_in_rows_or_columns(self, container, column_or_row, x_or_y, width_or_height): 
		child_shapes = container.children
		constraints = []
		for i in range(0, len(child_shapes)): 
			for j in range(0, len(child_shapes)): 
				if i != j: 
					child1 = child_shapes[i]
					child2 = child_shapes[j]
					constraint = If(child1.variables[column_or_row].z3 == child2.variables[column_or_row].z3, 
						Not(And((self.gap(child1,child2,x_or_y,width_or_height) > container.variables.proximity.z3), 
							self.no_children_between(child1, child2, child_shapes, column_or_row, x_or_y, width_or_height))), True)
					constraints.append(constraint)
		return And(constraints)

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
		# rows_index = container.variables.arrangement.domain.index("rows")
		# is_rows = arrangement == rows_index
		# columns_index = container.variables.arrangement.domain.index("columns")
		# is_columns = arrangement == columns_index

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

			vertical_arrange = And(vertical_pairs)
			horizontal_arrange = And(horizontal_pairs)
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
				self.solver.add(If(is_vertical, is_bottom, is_right), "Order last")

			if child.order == 0:
				is_top = (child_y == container_y)
				is_left = (child_x == container_x)
				self.solver.add(If(is_vertical, is_top, is_left), child.shape_id + " " + container.shape_id + " first in order")

		# Set the width and height of the container based on the arrangement axis 
		self.solver.add(If(is_vertical, container.computed_height() == child_heights, True), container.shape_id + " child_heights vertical")
		self.solver.add(If(is_horizontal, container.computed_width() == child_widths, True), container.shape_id + " child widths horizontal")

		m_w_constraint = container.computed_width() == (self.get_max_width_constraint(1,0,child_shapes))
		m_h_constraint = container.computed_height() == (self.get_max_height_constraint(1,0,child_shapes))
		self.solver.add(If(is_vertical, m_w_constraint, True), container.shape_id + " max height vertical")
		self.solver.add(If(is_horizontal, m_h_constraint, True), container.shape_id + " max width horizontal")

		# self.solver.add(If(is_rows, self.consecutive_rows_or_columns(container, "row"), True))
		# self.solver.add(If(is_columns, self.consecutive_rows_or_columns(container, "column"),True))
		# self.solver.add(If(is_rows, self.aligned_rows_or_columns(container, "row", "y", "height"), True))
		# self.solver.add(If(is_columns, self.aligned_rows_or_columns(container, "column", "x", "width"),True))
		# self.solver.add(If(is_rows, self.no_gaps_in_rows_or_columns(container, "row", "x", "width"),True))
		# self.solver.add(If(is_columns, self.no_gaps_in_rows_or_columns(container, "column", "y", "height"),True))

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

		# Alignment
		# Differs based on if the arrangment of the container is horizontal or vertical 
		child_shapes = container.children
		for child in child_shapes:
			child_x = child.variables.x.z3
			child_y = child.variables.y.z3

			left_aligned = child_x == container_x.z3
			right_aligned = (child_x + child.computed_width()) == (container_x.z3 + container.computed_width())
			h_center_aligned = (child_x + (child.computed_width()/2)) == (container_x.z3 + (container.computed_width()/2))
			top_aligned = child_y == container_y.z3
			bottom_aligned = (child_y + child.computed_height()) == (container_y.z3 + container.computed_height())
			v_center_aligned = (child_y + (child.computed_height()/2)) == (container_y.z3 + (container.computed_height()/2))
			horizontal = If(is_left, top_aligned, If(is_center, v_center_aligned, bottom_aligned))
			vertical = If(is_left, left_aligned, If(is_center, h_center_aligned, right_aligned))
			# self.solver.assert_and_track(If(is_vertical, vertical, horizontal), "alignment_constraint_" + container.shape_id + "_" + child.shape_id)
			self.solver.add(If(is_vertical, vertical, horizontal), container.shape_id + " " + child.shape_id + " alignment")
			



