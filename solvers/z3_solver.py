import copy
from z3 import *
import z3_helper
from fractions import Fraction

GRID_CONSTANT = 5

class Z3Solver(object): 
	def __init__(self, layout_problem):
		self.shapes = layout_problem.shapes
		self.groups = layout_problem.groups
		self.shape_items = self.shapes.values()
		self.shapes_list = list(self.shape_items)
		self.problem = layout_problem

		self.model = None
		self.solver = Optimize()
		# self.solver.set(unsat_core=True)

		# Keeps track of the overall number of solutions found so far
		self.solutions_found = 0

		self.helper = z3_helper.Z3Helper(self.solver, self.problem.box_width, self.problem.box_height)

		# Previous solutions 
		self.previous_solutions = []

		self.previous_alignments_score = -1 
		self.previous_balance_score = -1

		self.first_alignments_score = -1 
		self.first_balance_score = -1 
		
	def check(self):
		return self.solver.check()

	def unsat_core(self):
		return self.solver.unsat_core()

	def increment_solutions(self): 
		self.solutions_found += 1

	def update_solution_from_model(self): 
		test_total_width = 0

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

			shape.curr_x = adj_x
			shape.curr_y = adj_y
			shape.curr_width = adj_width
			shape.curr_height = adj_height

			test_total_width += adj_width

	def get_previous_solution_negation(self): 
		curr_values = []
		for shape in self.shape_items: 
			stmt_x = shape.adjusted_x == shape.curr_x
			stmt_y = shape.adjusted_y == shape.curr_y
			stmt_width = shape.adjusted_width == shape.curr_width
			stmt_height = shape.adjusted_height == shape.curr_height

			curr_values.append(stmt_x)
			curr_values.append(stmt_y)
			curr_values.append(stmt_width)
			curr_values.append(stmt_height)

		return Not(And(curr_values))

	def get_json_shapes(self): 
		# Convert the produced values back to the format of shapes to be drawn
		final_json = []
		for shape in self.shape_items: 
			json_shape = copy.deepcopy(shape.json_shape)

			# Calculate the rescaled_values
			json_shape["location"]["x"] = shape.curr_x * GRID_CONSTANT
			json_shape["location"]["y"] = shape.curr_y * GRID_CONSTANT
			json_shape["size"]["width"] = shape.curr_width * GRID_CONSTANT
			json_shape["size"]["height"] = shape.curr_height * GRID_CONSTANT

			final_json.append(json_shape)
		return final_json

	def print_cost_scores(self): 
		# Print out the current balance cost
		final_balance = self.model[self.helper.balance_cost]
		balance = final_balance.as_string()
		print("Balance cost: " + balance)

		# Print out the current alignments cost percentage
		final_alignment = self.model[self.helper.alignments_cost]
		alignment = Fraction(final_alignment.as_string())
		alignment = float(alignment)
		print("Alignment cost: " + final_alignment.as_string())

	def update_constraints_from_model(self): 
		test = False
		if self.solutions_found > 0:
			# Then, get and store the previous solution conjunction into the list of previous solutions 
			previous = self.get_previous_solution_negation() 
			self.previous_solutions.append(previous)
			# self.solver.assert_and_track(previous, 'prev' + str(self.solutions_found))
			self.solver.add(previous)
		# 	self.solver.pop()
			
		# # Create a new solving context
		# self.solver.push()

		# # Add the previous solutions back into the set of constraints
		# if self.solutions_found > 0:
		# 	###### Add one value as a constraint to the solution
		# 	# Add the distance function into the set of constraints
		# 	# self.helper.add_distance_cost(self.shapes_list)

		# 	# p_index = 0
		# 	# for shape in self.shapes_list:
		# 	# 	f_x = self.model[shape.adjusted_x]
		# 	# 	f_y = self.model[shape.adjusted_y]
		# 	# 	adj_x = f_x.as_string()
		# 	# 	adj_y = f_y.as_string()
		# 	# 	adj_x = int(adj_x)
		# 	# 	adj_y = int(adj_y)
		
		# 	# 	f_width = self.model[shape.adjusted_width]
		# 	# 	f_height = self.model[shape.adjusted_height]
		# 	# 	adj_width = f_width.as_string()
		# 	# 	adj_height = f_height.as_string()
		# 	# 	adj_width = int(adj_width)
		# 	# 	adj_height = int(adj_height)
		# 	# 	new_bounds = [adj_x, adj_y, adj_width, adj_height]
		
		# 	# 	self.helper.add_previous_solution_from_bounds(new_bounds, p_index)
		# 	# 	p_index += 4
		
		# 	# Previous computed distance
		# 	self.previous_alignments_score = self.model[self.helper.alignments_cost]
		# 	self.previous_balance_score = self.model[self.helper.balance_cost]
		# 	# if self.first_balance_score == -1 and self.first_alignments_score == -1: 
		# 	# 	self.first_balance_score = self.previous_balance_score
		# 	# 	self.first_alignments_score = self.previous_alignments_score

		# 	# self.helper.add_distance_increase_cost()
		# 	self.helper.add_alignment_balance_increase_cost(self.previous_alignments_score, self.previous_balance_score)

	# def increment_cost_constraint(self):
	# 	# Print out the current alignment cost
	# 	final_alignments = self.model[self.alignment_cost]
	# 	f_aligns = final_alignments.as_string()
	# 	print("num alignments: " + f_aligns)

	# 	####### Tell the solver to increase the number of alignments by X percent
	# 	f_aligns = int(f_aligns)

	# 	if self.current_alignments != -1: 
	# 		self.solver.pop()

	# 	self.current_alignments = f_aligns

	# 	# Try to increase the max
	# 	self.solver.push()
	# 	self.solver.add(self.alignment_cost >= f_aligns)

	def backtrack(self):
		print("Current alignments cost: " + str(self.previous_alignments_score))
		print("Current balance score: " + str(self.previous_balance_score))
		# if self.current_alignments >= 0:
		# 	self.solver.pop()
		# 	self.current_alignments -= 1
		# 	self.solver.push()
		# 	self.solver.add(self.alignment_cost == self.current_alignments)
		# else:
		# 	return False
		return True
	
	def get_solution(self): 
		# print("Looking for a solution.")
		# Pass in the cost function

		# print("minimizing the balance cost")
		# balance_cost = self.solver.minimize(self.helper.get_horizontal_balance_cost(self.shapes_list))
		# alignments_cost = self.solver.minimize(self.helper.get_alignments_cost(self.shapes_list))
		# constraints = self.solver.sexpr()
		result = self.solver.check();

		# obj = self.solver.objectives()
		if str(result) == 'sat': 
			# Find one solution for now
			self.model = self.solver.model()
			self.update_solution_from_model()
			return True
		else: 
			print("No solution found :(")
		return False








