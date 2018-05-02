from z3 import *

class Solver(object):
	def __init__(self, solver): 
		self.solver = solver
		self.debug = True

	def add(self, constraint, name=""): 
		if len(name) and self.debug: 
			self.solver.assert_and_track(constraint, name)
		else: 
			self.solver.add(constraint)

class ConstraintBuilder(object):
	def __init__(self, solver): 
		# So we can override the add method for debugging
		self.solver = Solver(solver)

	def init_previous_solution_constraints(self, previous_solutions, shapes): 
		# Saved solutions should not appear again in the results
		saved = previous_solutions["saved"]
		for saved_solution in saved: 
			elements = saved_solution["elements"]
			all_values = self.get_previous_solution_constraints_from_elements(shapes, elements)
			self.solver.add(Not(And(all_values)))

		designs = previous_solutions["designs"]
		for design_solution in designs: 
			elements = design_solution["elements"]
			all_values = self.get_previous_solution_constraints_from_elements(shapes, elements)
			self.solver.add(Not(And(all_values)))

		trash = previous_solutions["trashed"]
		for trashed_solution in trash: 
			elements = trashed_solution["elements"]
			all_values = self.get_previous_solution_constraints_from_elements(shapes, elements)
			self.solver.add(Not(And(all_values)))		

	def get_previous_solution_constraints_from_elements(self, shapes, elements):
		all_values = []
		for element in elements: 
			# Get the shape corresponding to the element name
			shape = shapes[element["name"]]
			variables = shape.variables.toDict()
			if element["type"] != "page" and element["type"] != "group" and element["type"] != "canvas":
				for variable_key in variables.keys(): 
					variable = variables[variable_key]
					if variable_key == "x" or variable_key == "y": 
						all_values.append(variable.z3 == element["location"][variable_key])
					elif variable_key in element:
						all_values.append(variable.z3 == element[variable_key])
		return all_values

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
		self.solver.add((page_shape.variables.x.z3 + page_shape.width) <= (canvas_x + canvas.width - margin.z3), page_shape.shape_id + ' gt canvas_right')
		self.solver.add((page_shape.variables.y.z3 + page_shape.height) <= (canvas_y + canvas.height - margin.z3), page_shape.shape_id + ' gt canvas_bottom')	

		# Fix the canvas X,Y to their original valuess
		self.solver.add(canvas_x == canvas.orig_x, 'canvas orig x')
		self.solver.add(canvas_y == canvas.orig_y, 'canvas orig y')

		self.justify_canvas(canvas)
		self.align_canvas(canvas)

	def init_container_constraints(self, container):
		arrangement = container.variables.arrangement.z3
		alignment = container.variables.alignment.z3
		proximity = container.variables.proximity.z3
		container_x = container.variables.x.z3
		container_y = container.variables.y.z3

		# Limit domains to the set of variable values
		self.solver.add(arrangement >= 0, "container " + container.shape_id + " arrangment greater than zero")
		self.solver.add(arrangement < len(container.variables.arrangement.domain), "container " + container.shape_id + " arrangment less than domain")
		self.solver.add(alignment >= 0, "container " + container.shape_id + " alignment greater than zero")
		self.solver.add(alignment < len(container.variables.alignment.domain), "container " + container.shape_id + " alignment less than domain")

		or_values = []
		for prox_value in container.variables.proximity.domain: 
			or_values.append(proximity == prox_value)
		self.solver.add(Or(or_values), "container " + container.shape_id + " proximity in domain")

		child_shapes = container.children
		for s_index in range(0, len(child_shapes)): 
			shape1 = child_shapes[s_index]
			shape1_x = shape1.variables.x.z3
			shape1_y = shape1.variables.y.z3

			# Shapes cannot exceed the bounds of their parent containers
			self.solver.add(shape1_x >= container_x, "child shape " + shape1.shape_id + " inside parent container (greater than left)")
			self.solver.add(shape1_y >= container_y, "child shape " + shape1.shape_id + " inside parent container (greater than top)")
			self.solver.add((shape1_x + shape1.width) <= (container_x + container.width), "child shape " + shape1.shape_id + " inside parent container (less than width)")
			self.solver.add((shape1_y + shape1.height) <= (container_y + container.height), "child shape " + shape1.shape_id + " inside parent container (less than height)")

		self.arrange_container(container)
		self.align_container(container)
		self.non_overlapping(container)

	def init_container_locks(self, container): 
		# Add constraints for all of the locked properties
		# TODO: Make generic at some point
		if container.locks is not None: 
			for lock in container.locks: 
				# "container " + container.shape_id + " variable " + container.variables[lock].name + " fixed to " + str(container.variable_values[lock])
				self.solver.add(container.variables[lock].z3 == container.variable_values[lock], container.shape_id + " variable " + container.variables[lock].name + " fixed to " + str(container.variable_values[lock]))

	def init_location_locks(self, shape): 
		if shape.locks is not None:
			for lock in shape.locks: 
				if lock == "location": 
					self.solver.add(shape.variables.x.z3 == shape.orig_x, shape.shape_id + " locked to position x")
					self.solver.add(shape.variables.y.z3 == shape.orig_y, shape.shape_id + " locked to position y")

	def non_overlapping(self, container): 
		proximity = container.variables.proximity.z3
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

					# Non-overlapping
					left = shape1_x + shape1.width + proximity <= shape2_x
					right = shape2_x + shape2.width + proximity <= shape1_x
					top = shape1_y + shape1.height + proximity <= shape2_y
					bottom = shape2_y + shape2.height + proximity <= shape1_y
					self.solver.add(Or(left,right,top,bottom), "Non-overlapping shapes " + shape1.shape_id + " " + shape2.shape_id)

	def get_max_width_constraint(self, child_i, widest_i, child_shapes): 
		if child_i < len(child_shapes): 
			widest_child = child_shapes[widest_i]
			next_child = child_shapes[child_i]
			return If(widest_child.width > next_child.width, self.get_max_width_constraint(child_i+1, widest_i, child_shapes), self.get_max_width_constraint(child_i+1, child_i, child_shapes))
		else: 
			return child_shapes[widest_i].width

	def get_max_height_constraint(self, child_i, tallest_i, child_shapes): 
		if child_i < len(child_shapes): 
			tallest_child = child_shapes[tallest_i]
			next_child = child_shapes[child_i]
			return If(tallest_child.height > next_child.height, self.get_max_height_constraint(child_i+1, tallest_i, child_shapes), self.get_max_height_constraint(child_i+1, child_i, child_shapes))
		else: 
			return child_shapes[tallest_i].height

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
		bottom_justified = (child_y + first_child.height) == (canvas_y + canvas.height - margin.z3)
		center_justified = (child_y + (first_child.height/2)) == (canvas_y + (canvas.height/2))
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
		center_aligned = (child_x + (first_child.width/2)) == (canvas_x + (canvas.width/2))
		right_aligned = (child_x + first_child.width) == (canvas_x + canvas.width - margin.z3)
		self.solver.add(If(is_left, left_aligned, If(is_center, center_aligned, right_aligned)), 'canvas_alignment')
		# self.solver.assert_and_track(If(is_left, left_aligned, If(is_center, center_aligned, right_aligned)), "canvas_alignment")

	# Sets up the arrangment constrains for a given container
	def arrange_container(self, container): 
		arrangement = container.variables.arrangement.z3
		proximity = container.variables.proximity.z3
		container_x = container.variables.x.z3
		container_y = container.variables.y.z3

		# ====== Arrangement constraints =======
		# Vertical and horizontal arrangments
		# In order that elements were defined
		v_index = container.variables.arrangement.domain.index("vertical")
		is_vertical = arrangement == v_index

		if container.order == "important": 
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

				vertical_pair_y = (shape1_y + shape1.height + proximity) == shape2_y
				vertical_pairs.append(vertical_pair_y)
				horizontal_pair_x = (shape1_x + shape1.width + proximity) == shape2_x
				horizontal_pairs.append(horizontal_pair_x)

			vertical_arrange = And(vertical_pairs)
			horizontal_arrange = And(horizontal_pairs)
			# self.solver.assert_and_track(If(is_vertical, vertical_arrange, horizontal_arrange), "arrangment_constraint_" + container.shape_id)
			self.solver.add(If(is_vertical, vertical_arrange, horizontal_arrange), container.shape_id + " arrangement")
			
		# Sum up the widths and heights
		child_widths = 0
		child_heights = 0
		child_shapes = container.children
		for child_i in range(0, len(child_shapes)): 
			child = child_shapes[child_i]
			child_x = child.variables.x.z3
			child_y = child.variables.y.z3

			add_proximity = 0 if child_i == (len(child_shapes) - 1) else proximity
			child_widths += child.width + add_proximity
			child_heights += child.height + add_proximity

			if child.order == "last": 
				# The bottom of the shape is the bottom of the container
				is_bottom = (child_y + child.height) == (container_y + container.height)
				is_right = (child_x + child.width) == (container_x + container.width)
				self.solver.add(If(is_vertical, is_bottom, is_right), "Order last")

			if child.order == "first":
				is_top = (child_y == container_y)
				is_left = (child_x == container_x)
				self.solver.add(If(is_vertical, is_top, is_left), child.shape_id + " " + container.shape_id + " first in order")

		# Set the width and height of the container based on the arrangement axis 
		# self.solver.assert_and_track(If(is_vertical, container.height == child_heights, container.width == child_widths), "height_constraint_" + container.shape_id)
		self.solver.add(If(is_vertical, container.height == child_heights, container.width == child_widths), container.shape_id + " child_heights")

		m_w_constraint = container.width == (self.get_max_width_constraint(1,0,child_shapes))
		m_h_constraint = container.height == (self.get_max_height_constraint(1,0,child_shapes))
		# self.solver.assert_and_track(If(is_vertical, m_w_constraint, m_h_constraint), "max_height_constraint_" + container.shape_id)
		self.solver.add(If(is_vertical, m_w_constraint, m_h_constraint), container.shape_id + " max height or width")


	def align_container(self, container):
		alignment = container.variables.alignment
		proximity = container.variables.proximity
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

			left_aligned = child_x == (container_x.z3 + proximity.z3)
			right_aligned = (child_x + child.width) == (container_x.z3 + container.width - proximity.z3)
			h_center_aligned = (child_x + (child.width/2)) == (container_x.z3 + (container.width/2))
			top_aligned = child_y == container_y.z3 + proximity.z3
			bottom_aligned = (child_y + child.height) == (container_y.z3 + container.height - proximity.z3)
			v_center_aligned = (child_y + (child.height/2)) == (container_y.z3 + (container.height/2))
			horizontal = If(is_left, top_aligned, If(is_center, v_center_aligned, bottom_aligned))
			vertical = If(is_left, left_aligned, If(is_center, h_center_aligned, right_aligned))
			# self.solver.assert_and_track(If(is_vertical, vertical, horizontal), "alignment_constraint_" + container.shape_id + "_" + child.shape_id)
			self.solver.add(If(is_vertical, vertical, horizontal), container.shape_id + " " + child.shape_id + " alignment")
			





