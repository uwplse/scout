import copy
from z3 import *

# These will eventually be customizable
GRID_CONSTANT = 5
GROUP_PROXIMITY = 5
GLOBAL_PROXIMITY = 5

MINIMUM_WIDTH_SHAPE = 10
MINIMUM_HEIGHT_SHAPE = 10

class Z3Solver(object): 
	def __init__(self, layout_problem=None):
		if layout_problem is not None:
			self.shapes = layout_problem.shapes
			self.groups = layout_problem.groups
			self.problem = layout_problem
		self.model = None
		self.solver = Solver()

		# cost variables
		self.alignment_cost = Int('NumAlignments')
		self.max_alignments = -1
		self.current_alignments = -1 

	def add(self, constraint, strength=""):
		self.solver.add(constraint)

	def check(self):
		return self.solver.check()

	def get_json_shapes(self): 
		# if self.groups is not None: 
		# 	for group_id, group in self.groups.items(): 
		# 		f_x = self.model[group.adjusted_x]
		# 		f_y = self.model[group.adjusted_y]
		# 		f_width = self.model[group.adjusted_width]
		# 		f_height = self.model[group.adjusted_height]
		# 		arrangement = self.model[group.arrangement]

		# 		adj_x = f_x.as_string()
		# 		adj_y = f_y.as_string()
		# 		adj_width = f_width.as_string()
		# 		adj_height = f_height.as_string()
		# 		# align = alignment.as_string()

		# 		print(group_id, adj_x, adj_y, adj_width, adj_height, arrangement)

		# Convert the produced values back to the format of shapes to be drawn
		final_json = []
		if self.shapes is not None: 
			for shape_id, shape in self.shapes.items(): 
				final_x = shape.adjusted_x
				final_y = shape.adjusted_y
				final_width = shape.adjusted_width
				final_height = shape.adjusted_height

				f_x = self.model[final_x]
				f_y = self.model[final_y]
				f_width = self.model[final_width]
				f_height = self.model[final_height]

				adj_x = f_x.as_string()
				adj_y = f_y.as_string()
				adj_width = f_width.as_string()
				adj_height = f_height.as_string()

				adj_x = int(adj_x)
				adj_y = int(adj_y)
				adj_width = int(adj_width)
				adj_height = int(adj_height)

				# TOODO later figure out why necessary or do something more efficient
				json_shape = copy.deepcopy(shape.json_shape)
				json_shape["location"]["x"] = adj_x
				json_shape["location"]["y"] = adj_y
				json_shape["size"]["width"] = adj_width
				json_shape["size"]["height"] = adj_height

				final_json.append(json_shape)

		return final_json

	def add_constraint_from_solution(self): 
		# Print out the current alignment cost
		final_alignments = self.model[self.alignment_cost]
		f_aligns = final_alignments.as_string()
		print("num alignments: " + f_aligns)
		
		####### Add one value as a constraint to the solution
		constraints = []
		for shape_id, shape in self.shapes.items():
			final_x = shape.adjusted_x
			final_y = shape.adjusted_y

			f_x = self.model[final_x]
			f_y = self.model[final_y]
			adj_x = f_x.as_string()
			adj_y = f_y.as_string()

			adj_x = int(adj_x)
			adj_y = int(adj_y)

			x_not_same = shape.adjusted_x != adj_x
			y_not_same = shape.adjusted_y != adj_y
			constraints.append(x_not_same)
			constraints.append(y_not_same)

			# Width and height can change but may be equal to original so only add these if width/height are adjustable
			if shape.size_adjustable:
				final_width = shape.adjusted_width
				final_height = shape.adjusted_height
				f_width = self.model[final_width]
				f_height = self.model[final_height]
				adj_width = f_width.as_string()
				adj_height = f_height.as_string()
				adj_width = int(adj_width)
				adj_height = int(adj_height)
				width_not_same = shape.adjusted_width != adj_width
				height_not_same = shape.adjusted_height != adj_height
				constraints.append(width_not_same)
				constraints.append(height_not_same)

		if len(constraints):
			self.solver.add(Or(constraints))

	def increment_cost_constraint(self):
		# Print out the current alignment cost
		final_alignments = self.model[self.alignment_cost]
		f_aligns = final_alignments.as_string()
		print("num alignments: " + f_aligns)

		####### Tell the solver to increase the number of alignments by X percent
		f_aligns = int(f_aligns)

		if self.current_alignments != -1: 
			self.solver.pop()

		self.current_alignments = f_aligns

		# Try to increase the max
		self.solver.push()
		self.solver.add(self.alignment_cost >= f_aligns)

	def backtrack(self):
		print("Current alignments cost: " + str(self.current_alignments))
		if self.current_alignments >= 0: 
			self.solver.pop()
			self.current_alignments -= 1
			self.solver.push()
			self.solver.add(self.alignment_cost == self.current_alignments)
		else: 
			return False
		return True
	
	def get_solution(self): 
		print("Looking for a solution.")
		# Pass in the cost function
		curr_shapes = list(self.shapes.values())
		# object_fun = self.solver.maximize(self.num_alignments(curr_shapes))
		result = self.solver.check();
		# upper_vals = self.solver.upper_values(object_fun)
		# upper = self.solver.upper(object_fun)
		# lower_vals = self.solver.lower_values(object_fun)
		# lower = self.solver.lower(object_fun)

		# obj = self.solver.objectives()
		if str(result) == 'sat': 
			# Find one solution for now
			self.model = self.solver.model()
			return True
		else: 
			print("No solution found :(")
		return False

	def add_effect_constraint(self, shape, effected_shape):
		distance_constraint = self.get_distance_constraint(effected_shape, shape)

		# TODO: Should be aligned

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

	# def add_non_overlapping_constraints(self, shape1, shape2):
	# 	# Auxiliary variables
	# 	y0 = Int('y' + str(self.auxiliary_vars))
	# 	y1 = Int('y' + str(self.auxiliary_vars+1))
	# 	y2 = Int('y' + str(self.auxiliary_vars+2))
	# 	y3 = Int('y' + str(self.auxiliary_vars+3))
	# 	self.auxiliary_vars+=4
	#
	# 	# Restrict the range so it satisfies at least one of the four
	# 	self.solver.add(y0 >= 0)
	# 	self.solver.add(y1 >= 0)
	# 	self.solver.add(y2 >= 0)
	# 	self.solver.add(y3 >= 0)
	#
	# 	self.solver.add(y0 <= 1)
	# 	self.solver.add(y1 <= 1)
	# 	self.solver.add(y2 <= 1)
	# 	self.solver.add(y3 <= 1)
	#
	# 	M_x = self.problem.box_width
	# 	M_y = self.problem.box_height
	#
	# 	# Non-overlapping
	# 	left = shape1.adjusted_x + shape1.adjusted_width + GLOBAL_PROXIMITY <= shape2.adjusted_x + (M_x * (1-y0))
	# 	right = shape2.adjusted_x + shape2.adjusted_width + GLOBAL_PROXIMITY <= shape1.adjusted_x + (M_x * (1-y1))
	# 	top = shape1.adjusted_y + shape1.adjusted_height + GLOBAL_PROXIMITY <= shape2.adjusted_y + (M_y * (1-y2))
	# 	bottom = shape2.adjusted_y + shape2.adjusted_height + GLOBAL_PROXIMITY <= shape1.adjusted_y + (M_y * (1-y3))
	#
	# 	# Add non-overlapping constraints into the solver
	# 	self.solver.add(left)
	# 	self.solver.add(right)
	# 	self.solver.add(top)
	# 	self.solver.add(bottom)
	#
	# 	self.solver.add((y0 + y1 + y2 + y3) >= 1)

	def add_non_overlapping_constraints(self, shape1, shape2):
		# Non-overlapping
		left = shape1.adjusted_x + shape1.adjusted_width + GLOBAL_PROXIMITY <= shape2.adjusted_x
		right = shape2.adjusted_x + shape2.adjusted_width + GLOBAL_PROXIMITY <= shape1.adjusted_x
		top = shape1.adjusted_y + shape1.adjusted_height + GLOBAL_PROXIMITY <= shape2.adjusted_y
		bottom = shape2.adjusted_y + shape2.adjusted_height + GLOBAL_PROXIMITY <= shape1.adjusted_y
		self.solver.add(Or(left,right,top,bottom))

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
			self.solver.add(shape.adjusted_width <= self.problem.box_width)
			self.solver.add(shape.adjusted_height <= self.problem.box_height)
		elif shape.importance == "least":
			self.solver.add(shape.adjusted_width <= shape.orig_width)
			self.solver.add(shape.adjusted_height <= shape.orig_height)
			self.solver.add(shape.adjusted_width >= MINIMUM_WIDTH_SHAPE)
			self.solver.add(shape.adjusted_height >= MINIMUM_HEIGHT_SHAPE)
		else:
			self.add_locked_size_constraint(shape)

	def add_alignment_cost(self): 
		all_shapes = list(self.shapes.values())
		self.solver.add(self.alignment_cost == self.num_alignments(all_shapes))

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