from z3 import *
# from cassowary import Variable, STRONG

# Base class for the constraints
# Inherited by both the Z3 solver helper and the Cassowary solver helper
class ConstraintHelper(object): 
	def __init__(self, solver, problem): 
		self.solver = solver
		self.problem = problem
		self.auxiliary_vars = 0

class CassowaryHelper(ConstraintHelper): 
	def __init__(self, solver, problem): 
		ConstraintHelper.__init__(self, solver, problem)

class Z3Helper(ConstraintHelper): 
	def __init__(self, solver, problem): 
		ConstraintHelper.__init__(self, solver, problem)

	# Cost function to minimize group area
	def group_area(self, groups): 
		# Optimize by the total area for each group
		total_area = 0
		for group in groups: 
			total_area += group.width*group.height
		return total_area

	# Cost function to maximize the number of aglinemtns

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











