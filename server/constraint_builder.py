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

	def init_canvas_constraints(self, canvas): 
		self.solver.add(canvas.alignment.z3 >= 0, 'canvas_alignment domain lowest')
		self.solver.add(canvas.alignment.z3 < len(canvas.alignment.domain), 'canvas_alignment domain highest')
		self.solver.add(canvas.justification.z3 >= 0, 'canvas_justification domain lowest')
		self.solver.add(canvas.justification.z3 < len(canvas.justification.domain), 'canvas justification domain highest')

		child_shapes = canvas.children
		if len(child_shapes) > 0: 
			# Every child shape should remain inside of its parent container
			for s_index in range(0, len(child_shapes)): 
				shape1 = child_shapes[s_index]
				self.solver.add(shape1.x.z3 >= canvas.x.z3, shape1.shape_id + ' gt canvas_x')
				self.solver.add(shape1.y.z3 >= canvas.y.z3, shape1.shape_id + ' gt canvas_y')
				self.solver.add((shape1.x.z3 + shape1.width) <= (canvas.x.z3 + canvas.width), shape1.shape_id + ' gt canvas_right')
				self.solver.add((shape1.y.z3 + shape1.height) <= (canvas.y.z3 + canvas.height), shape1.shape_id + ' gt canvas_bottom')	

			# Set the canvas X,Y to their original values
			self.solver.add(canvas.x.z3 == canvas.orig_x, 'canvas orig x')
			self.solver.add(canvas.y.z3 == canvas.orig_y, 'canvas orig y')

			self.justify_canvas(canvas)
			self.align_canvas(canvas)

	def init_container_constraints(self, container):
		# Limit domains to the set of variable values
		self.solver.add(container.arrangement.z3 >= 0)
		self.solver.add(container.arrangement.z3 < len(container.arrangement.domain))
		self.solver.add(container.alignment.z3 >= 0)
		self.solver.add(container.alignment.z3 < len(container.alignment.domain))

		or_values = []
		for prox_value in container.proximity.domain: 
			or_values.append(container.proximity.z3 == prox_value)
		self.solver.add(Or(or_values))

		child_shapes = container.children
		for s_index in range(0, len(child_shapes)): 
			shape1 = child_shapes[s_index]

			# Shapes cannot exceed the bounds of their parent containers
			self.solver.add(shape1.x.z3 >= container.x.z3)
			self.solver.add(shape1.y.z3 >= container.y.z3)
			self.solver.add((shape1.x.z3 + shape1.width) <= (container.x.z3 + container.width))
			self.solver.add((shape1.y.z3 + shape1.height) <= (container.y.z3 + container.height))

		self.arrange_container(container)
		self.align_container(container)
		self.non_overlapping(container)

	def init_shape_constraints(self, shape): 
		if shape.locked: 
			self.solver.add(shape.x.z3 == shape.orig_x)
			self.solver.add(shape.y.z3 == shape.orig_y)

	def non_overlapping(self, container): 
		child_shapes = container.children 
		for i in range(0, len(child_shapes)): 
			for j in range(0, len(child_shapes)): 
				if i != j: 
					shape1 = child_shapes[i]
					shape2 = child_shapes[j]
					# Non-overlapping
					left = shape1.x.z3 + shape1.width + container.proximity.z3 <= shape2.x.z3
					right = shape2.x.z3 + shape2.width + container.proximity.z3 <= shape1.x.z3
					top = shape1.y.z3 + shape1.height + container.proximity.z3 <= shape2.y.z3
					bottom = shape2.y.z3 + shape2.height + container.proximity.z3 <= shape1.y.z3
					self.solver.add(Or(left,right,top,bottom))

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
		first_child = canvas.children[0]

		# Canvas justification (because the canvas is the only type of container right now not sizing to its contents)
		t_index = canvas.justification.domain.index("top")
		c_index = canvas.justification.domain.index("center")
		is_top = canvas.justification.z3 == t_index
		is_center = canvas.justification.z3 == c_index
		top_justified = first_child.y.z3 == canvas.y.z3
		bottom_justified = (first_child.y.z3 + first_child.height) == (canvas.y.z3 + canvas.height)
		center_justified = (first_child.y.z3 + (first_child.height/2)) == (canvas.y.z3 + (canvas.height/2))
		self.solver.add(If(is_top, top_justified, If(is_center, center_justified, bottom_justified)), 'canvas_justification')
		# self.solver.assert_and_track(If(is_top, top_justified, If(is_center, center_justified, bottom_justified)), "canvas_justification")

	def align_canvas(self, canvas):
		first_child = canvas.children[0]

		# Canvas aligment is different than other containers since there is no concept of arrangement
		l_index = canvas.alignment.domain.index("left")
		c_index = canvas.alignment.domain.index("center")
		is_left = canvas.alignment.z3 == l_index
		is_center = canvas.alignment.z3 == c_index
		left_aligned = first_child.x.z3 == canvas.x.z3
		center_aligned = (first_child.x.z3 + (first_child.width/2)) == (canvas.x.z3 + (canvas.width/2))
		right_aligned = (first_child.x.z3 + first_child.width) == (canvas.x.z3 + canvas.width)
		self.solver.add(If(is_left, left_aligned, If(is_center, center_aligned, right_aligned)), 'canvas_alignment')
		# self.solver.assert_and_track(If(is_left, left_aligned, If(is_center, center_aligned, right_aligned)), "canvas_alignment")

	# Sets up the arrangment constrains for a given container
	def arrange_container(self, container): 
		# ====== Arrangement constraints =======
		# Vertical and horizontal arrangments 
		# In order that elements were defined
		v_index = container.arrangement.domain.index("vertical")
		is_vertical = container.arrangement.z3 == v_index

		if container.order == "important": 
			vertical_pairs = []
			horizontal_pairs = []
			child_shapes = container.children
			for s_index in range(0, len(child_shapes)-1): 
				shape1 = child_shapes[s_index]
				shape2 = child_shapes[s_index+1]
				vertical_pair_y = (shape1.y.z3 + shape1.height + container.proximity.z3) == shape2.y.z3 
				vertical_pairs.append(vertical_pair_y)
				horizontal_pair_x = (shape1.x.z3 + shape1.width + container.proximity.z3) == shape2.x.z3
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
			add_proximity = 0 if child_i == (len(child_shapes) - 1) else container.proximity.z3
			child_widths += child.width + add_proximity
			child_heights += child.height + add_proximity

			if child.order == "last": 
				# The bottom of the shape is the bottom of the container
				is_bottom = (child.y.z3 + child.height) == (container.y.z3 + container.height)
				is_right = (child.x.z3 + child.width) == (container.x.z3 + container.width)
				self.solver.add(If(is_vertical, is_bottom, is_right))

			if child.order == "first":
				is_top = (child.y.z3 == container.y.z3)
				is_left = (child.x.z3 == container.x.z3)
				self.solver.add(If(is_vertical, is_top, is_left), child.shape_id + " " + container.shape_id + " first in order")

		# Set the width and height of the container based on the arrangement axis 
		# self.solver.assert_and_track(If(is_vertical, container.height == child_heights, container.width == child_widths), "height_constraint_" + container.shape_id)
		self.solver.add(If(is_vertical, container.height == child_heights, container.width == child_widths), container.shape_id + " child_heights")

		m_w_constraint = container.width == (self.get_max_width_constraint(1,0,child_shapes))
		m_h_constraint = container.height == (self.get_max_height_constraint(1,0,child_shapes))
		# self.solver.assert_and_track(If(is_vertical, m_w_constraint, m_h_constraint), "max_height_constraint_" + container.shape_id)
		self.solver.add(If(is_vertical, m_w_constraint, m_h_constraint), container.shape_id + " max height or width")


	def align_container(self, container): 
		l_index = container.alignment.domain.index("left")
		c_index = container.alignment.domain.index("center")
		is_left = container.alignment.z3 == l_index
		is_center = container.alignment.z3 == c_index
		v_index = container.arrangement.domain.index("vertical")
		is_vertical = container.arrangement.z3 == v_index

		# Alignment
		# Differs based on if the arrangment of the container is horizontal or vertical 
		child_shapes = container.children
		for child in child_shapes:
			left_aligned = child.x.z3 == (container.x.z3 + container.proximity.z3)
			right_aligned = (child.x.z3 + child.width) == (container.x.z3 + container.width - container.proximity.z3)
			h_center_aligned = (child.x.z3 + (child.width/2)) == (container.x.z3 + (container.width/2))
			top_aligned = child.y.z3 == container.y.z3 + container.proximity.z3
			bottom_aligned = (child.y.z3 + child.height) == (container.y.z3 + container.height - container.proximity.z3)
			v_center_aligned = (child.y.z3 + (child.height/2)) == (container.y.z3 + (container.height/2))
			horizontal = If(is_left, top_aligned, If(is_center, v_center_aligned, bottom_aligned))
			vertical = If(is_left, left_aligned, If(is_center, h_center_aligned, right_aligned))
			# self.solver.assert_and_track(If(is_vertical, vertical, horizontal), "alignment_constraint_" + container.shape_id + "_" + child.shape_id)
			self.solver.add(If(is_vertical, vertical, horizontal), container.shape_id + " " + child.shape_id + " alignment")
			

