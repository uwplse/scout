from z3 import *

# These will eventually be customizable
GRID_CONSTANT = 5
GROUP_PROXIMITY = 5
GLOBAL_PROXIMITY = 5

MINIMUM_WIDTH_SHAPE = 10
MINIMUM_HEIGHT_SHAPE = 10

class ConstraintHelper(object): 
	def __init__(self, solver, problem): 
		self.solver = solver
		self.problem = problem

	# Cost function
	def group_area(self, groups): 
		# Optimize by the total area for each group
		total_area = 0
		for group in groups: 
			total_area += group.width*group.height
		return total_area

	def maximize_alignments(self, shapes): 
		total_alignments = 0
		for i in range(0, len(shapes)): 
			for j in range(0, len(shapes)): 
				if i != j: 	
					shape1 = shapes[i]
					shape2 = shapes[j]
					total_alignments += If(self.is_aligned(shape1, shape2), 0, 1)

		return total_alignments
	
	def is_aligned(self, shape1, shape2): 
		top = shape1.adjusted_y == shape2.adjusted_y
		bottom = (shape1.adjusted_y + shape1.height) == (shape2.adjusted_y + shape2.height)
		left = shape1.adjusted_x == shape2.adjusted_x
		right = (shape1.adjusted_x + shape1.width) == (shape2.adjusted_x + shape2.width)
		y_center = (shape1.adjusted_y + (shape1.height/2)) == (shape2.adjusted_y + (shape2.height/2))
		x_center = (shape1.adjusted_x + (shape1.width/2)) == (shape2.adjusted_x + (shape2.width/2))
		return Or(top, bottom, left, right, x_center, y_center)

	def add_locked_position_constraint(self, shape): 
		self.solver.add(shape.adjusted_x == shape.orig_x)
		self.solver.add(shape.adjusted_y == shape.orig_y)

	def add_locked_size_constraint(self, shape): 
		self.solver.add(shape.adjusted_width == shape.orig_width)
		self.solver.add(shape.adjusted_height == shape.orig_height)

	def add_importance_constraints(self, shape): 
		if shape.importance == "most": 
			self.solver.add(shape.adjusted_width >= shape.orig_width)
			self.solver.add(shape.adjusted_height >= shape.orig_height)
			self.solver.add(shape.adjusted_width <= self.problem.box_width)
			self.solver.add(shape.adjusted_height <= self.problem.box_height)
		elif shape.importance == "least": 
			self.solver.add(shape.adjusted_width <= shape.orig_width)
			self.solver.add(shape.adjusted_height <= shape.orig_height)
			self.solver.add(shape.adjusted_width >= MINIMUM_WIDTH_SHAPE)
			self.solver.add(shape.adjusted_height >= MINIMUM_HEIGHT_SHAPE)
		else: 
			self.add_locked_size_constraint(shape)

	def add_effect_constraint(self, shape, effected_shape): 
		distance_constraint = self.get_distance_constraint(effected_shape, shape)
		self.solver.add(distance_constraint) 

	def add_bounds_constraints(self, shape): 
		# The height/width and position cannot exceed the available bounds
		self.solver.add((shape.adjusted_x+shape.adjusted_width) <= self.problem.box_width)
		self.solver.add((shape.adjusted_y+shape.adjusted_height) <= self.problem.box_height)

		# The x,y coordinates cannot be negative
		self.solver.add(shape.adjusted_x >= 0)
		self.solver.add(shape.adjusted_y >= 0)

	def add_grid_constraints(self, shape): 
		# Positions must be a multiple of the grid constant
		self.solver.add((shape.adjusted_x % GRID_CONSTANT) == 0)
		self.solver.add((shape.adjusted_y % GRID_CONSTANT) == 0)

	def add_proximity_constraints(self, shape1, shape2): 
		right = shape1.adjusted_x + shape1.adjusted_width + GLOBAL_PROXIMITY <= (shape2.adjusted_x)
		left = (shape1.adjusted_x) >= shape2.adjusted_x + shape2.adjusted_width + GLOBAL_PROXIMITY
		bottom = shape1.adjusted_y + shape1.adjusted_height + GLOBAL_PROXIMITY <= (shape2.adjusted_y)
		top = (shape1.adjusted_y) >= shape2.adjusted_y + shape2.adjusted_height + GLOBAL_PROXIMITY

		self.solver.add(Or(left, right, top, bottom))

	def add_grouping_constraints(self, shape, group): 
		# A shape should stay inside the bounds of its parent group 
		self.solver.add(shape.adjusted_x >= group.adjusted_x)
		self.solver.add((shape.adjusted_x+shape.adjusted_width) <= (group.adjusted_x+group.adjusted_width))
		self.solver.add(shape.adjusted_y >= group.adjusted_y)
		self.solver.add((shape.adjusted_y+shape.adjusted_height) <= (group.adjusted_y+group.adjusted_height))

	def add_min_size_constraints(self, shape, min_width, min_height): 
		self.solver.add(shape.adjusted_width >= min_width)
		self.solver.add(shape.adjusted_height >= min_height)

	def add_max_size_constraints(self, shape, max_width, max_height):
		# Round up to the nearest moduloe of the grid constant
		diff_height = GRID_CONSTANT - (max_height%GRID_CONSTANT)
		diff_width = GRID_CONSTANT - (max_width%GRID_CONSTANT)
		max_height = max_height + diff_height
		max_width = max_width + diff_width

		self.solver.add(shape.adjusted_width <= max_width)
		self.solver.add(shape.adjusted_height <= max_height)

	def get_distance_constraint(self, shape1, shape2):
		left = (shape2.adjusted_x + shape2.width) < shape1.adjusted_x
		right = shape2.adjusted_x > (shape1.adjusted_x + shape1.width)
		top = (shape2.adjusted_y + shape2.height) < shape1.adjusted_y
		bottom = shape2.adjusted_y > (shape1.adjusted_y + shape1.height)

		left_distance = (shape1.adjusted_x - (shape2.adjusted_x + shape2.width))<=GROUP_PROXIMITY
		right_distance = (shape2.adjusted_x - (shape1.adjusted_x + shape1.width)) <= GROUP_PROXIMITY
		top_distance = (shape1.adjusted_y - (shape2.adjusted_y + shape2.height)) <= GROUP_PROXIMITY
		bottom_distance = (shape2.adjusted_y - (shape1.adjusted_y + shape1.height)) <= GROUP_PROXIMITY
		bottom_within_range = (shape2.adjusted_y + shape2.height) >= (shape1.adjusted_y - GROUP_PROXIMITY)
		top_within_range = shape2.adjusted_y <= (shape1.adjusted_y + shape1.height + GROUP_PROXIMITY)
		left_within_range = shape2.adjusted_x <= (shape1.adjusted_x + shape1.width + GROUP_PROXIMITY)
		right_within_range = (shape2.adjusted_x + shape2.width) >=  (shape1.adjusted_x - GROUP_PROXIMITY)


		left_cst = If(left, And(left_distance, bottom_within_range, top_within_range), False)
		right_cst = If(right, And(right_distance, bottom_within_range, top_within_range), False)
		top_cst = If(top, And(top_distance, left_within_range, right_within_range), False)
		bottom_cst = If(bottom, And(bottom_distance, left_within_range, right_within_range), False)
		return Or(left_cst, right_cst, top_cst, bottom_cst)











