from z3 import *

# These will eventually be customizable
GRID_CONSTANT = 5
GROUP_PROXIMITY = 5
GLOBAL_PROXIMITY = 5

MINIMUM_WIDTH_SHAPE = 10
MINIMUM_HEIGHT_SHAPE = 10

# Override default abs, max, min functions to construct Z3 expressions
def abs(x):
	return If(x>=0,x,-x)

def max(x, y): 
	return If(x > y, x, y)

def min(x, y): 
	return If(x < y, x, y)

class Z3Helper(object): 
	def __init__(self, solver, bounds_width, bounds_height): 
		self.solver = solver

		# cost variables
		self.alignment_cost = Int('NumAlignments')
		self.distance_cost = Int('DistanceCost')

		self.box_width = bounds_width
		self.box_height = bounds_height

	##### Global Constraints ######
	def add_bounds_constraints(self, shape):
		# The height/width and position cannot exceed the available bounds
		self.solver.add((shape.adjusted_x+shape.adjusted_width) <= self.box_width)
		self.solver.add((shape.adjusted_y+shape.adjusted_height) <= self.box_height)

		# The x,y coordinates cannot be negative
		self.solver.add(shape.adjusted_x >= 0)
		self.solver.add(shape.adjusted_y >= 0)

	def add_grid_constraints(self, shape):
		# Positions must be a multiple of the grid constant
		self.solver.add((shape.adjusted_x % GRID_CONSTANT) == 0)
		self.solver.add((shape.adjusted_y % GRID_CONSTANT) == 0)

	def add_non_overlapping_constraints(self, shape1, shape2):
		# Non-overlapping
		left = shape1.adjusted_x + shape1.adjusted_width + GLOBAL_PROXIMITY <= shape2.adjusted_x
		right = shape2.adjusted_x + shape2.adjusted_width + GLOBAL_PROXIMITY <= shape1.adjusted_x
		top = shape1.adjusted_y + shape1.adjusted_height + GLOBAL_PROXIMITY <= shape2.adjusted_y
		bottom = shape2.adjusted_y + shape2.adjusted_height + GLOBAL_PROXIMITY <= shape1.adjusted_y
		self.solver.add(Or(left,right,top,bottom))

	def add_size_constraints(self, shape): 
		# To Do - Think of reasonable min/max heights for shapes based on the type
		self.solver.add(shape.adjusted_width >= MINIMUM_WIDTH_SHAPE)
		self.solver.add(shape.adjusted_height >= MINIMUM_HEIGHT_SHAPE)
		self.solver.add(shape.adjusted_width <= self.box_width)
		self.solver.add(shape.adjusted_height <= self.box_height)

	##### User Defined #####
	def add_effect_constraint(self, shape, effected_shape):
		distance_constraint = self.get_distance_constraint(effected_shape, shape)

		# TODO: Should be aligned
		self.solver.add(distance_constraint)

	def add_group_constraints(self, group, size_constraint, alignment_constraint): 
		# self.solver.add(group.alignment >=0)
		# self.solver.add(group.alignment <=5)
		self.solver.add(size_constraint)
		self.solver.add(alignment_constraint)

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

	def add_locked_position_constraint(self, shape):
		self.solver.add(shape.adjusted_x == shape.orig_x)
		self.solver.add(shape.adjusted_y == shape.orig_y)

	def add_locked_size_constraint(self, shape):
		print(shape.id)
		self.solver.add(shape.adjusted_width == shape.orig_width)
		self.solver.add(shape.adjusted_height == shape.orig_height)

	def add_importance_constraints(self, shape):
		if shape.importance == "most":
			self.solver.add(shape.adjusted_width >= shape.orig_width)
			self.solver.add(shape.adjusted_height >= shape.orig_height)
			self.solver.add(shape.adjusted_width <= self.box_width)
			self.solver.add(shape.adjusted_height <= self.box_height)
		elif shape.importance == "least":
			self.solver.add(shape.adjusted_width <= shape.orig_width)
			self.solver.add(shape.adjusted_height <= shape.orig_height)
			self.solver.add(shape.adjusted_width >= MINIMUM_WIDTH_SHAPE)
			self.solver.add(shape.adjusted_height >= MINIMUM_HEIGHT_SHAPE)
		else:
			self.add_locked_size_constraint(shape)

	def add_alignment_cost(self, shapes): 
		self.solver.add(self.alignment_cost == self.num_alignments(shapes))

	def add_alignment_constraint(self, shape1, shape2):
		# Add each alignment constraint as a soft constraint
		aligned = self.is_aligned(shape1, shape2)
		self.solver.add_soft(aligned)

	def is_aligned(self, shape1, shape2):
		top = shape1.adjusted_y == shape2.adjusted_y
		bottom = (shape1.adjusted_y + shape1.adjusted_height) == (shape2.adjusted_y + shape2.adjusted_height)
		left = shape1.adjusted_x == shape2.adjusted_x
		right = (shape1.adjusted_x + shape1.adjusted_width) == (shape2.adjusted_x + shape2.adjusted_width)
		y_center = (shape1.adjusted_y + (shape1.adjusted_height/2)) == (shape2.adjusted_y + (shape2.adjusted_height/2))
		x_center = (shape1.adjusted_x + (shape1.adjusted_width/2)) == (shape2.adjusted_x + (shape2.adjusted_width/2))
		return Or(top, bottom, left, right, x_center, y_center)

	def num_alignments(self, shapes):
		total_alignments = 0
		for i in range(0, len(shapes)):
			for j in range(0, len(shapes)):
				if i != j:
					shape1 = shapes[i]
					shape2 = shapes[j]
					total_alignments += If(self.is_aligned(shape1, shape2), 1, 0)

		return total_alignments

	def add_distance_cost(self, shapes): 
		# The most recent previous solution
		num_shapes = len(shapes)
		self.previous_solution = IntVector('PrevSolution', num_shapes*4)

		self.solver.add(self.distance_cost == self.get_distance_cost(shapes))

	def add_distance_increase_cost(self): 
		distance_const = 500
		self.solver.add(self.distance_cost >= distance_const)

	def add_previous_solution_from_original(self, shape, p_index): 
		self.solver.add(self.previous_solution[p_index] == shape.orig_x)
		self.solver.add(self.previous_solution[p_index+1] == shape.orig_y)
		self.solver.add(self.previous_solution[p_index+2] == shape.orig_width)
		self.solver.add(self.previous_solution[p_index+3] == shape.orig_height)

	def add_previous_solution_from_bounds(self, bounds, p_index): 
		adj_x,adj_y,adj_width,adj_height = bounds
		self.solver.add(self.previous_solution[p_index] == adj_x)
		self.solver.add(self.previous_solution[p_index+1] == adj_y)
		self.solver.add(self.previous_solution[p_index+2] == adj_width)
		self.solver.add(self.previous_solution[p_index+3] == adj_height)

	def get_distance_cost(self, shapes): 
		# Compute the IoU cost of this solution from the previous solution
		prev_i = 0
		total_cost = 0
		for i in range(0, len(shapes)): 
			shape = shapes[i]

			prev_x = self.previous_solution[prev_i]
			prev_y = self.previous_solution[prev_i+1]
			prev_width = self.previous_solution[prev_i+2]
			prev_height = self.previous_solution[prev_i+3]
			total_cost += abs(shape.adjusted_x-prev_x)
			total_cost += abs(shape.adjusted_y-prev_y)
			total_cost += abs(shape.adjusted_width-prev_width)
			total_cost += abs(shape.adjusted_height-prev_height)
			# # Compute the area of overlap between the two boxes
			# xA = max(prev_x, shape.adjusted_x)
			# yA = max(prev_y, shape.adjusted_y)
			# xB = min(prev_width, shape.adjusted_width)
			# yB = min(prev_height, shape.adjusted_height)
			# overlap = (xB - xA + 1) * (yB - yA + 1)
			# curr_area = shape.adjusted_width * shape.adjusted_height
			# prev_area = prev_width * prev_height
			# iou = overlap / (curr_area + prev_area - overlap)

			# total_cost += iou # We want to minimize the amount of overlap with the previous solution
			prev_i += 4
		return total_cost


