import copy
from ortools.constraint_solver import pywrapcp
import or_tools_helper
from fractions import Fraction

class OrToolsSolver(object): 
	def __init__(self, layout_problem, solver=None):
		self.shapes = layout_problem.shapes
		self.groups = layout_problem.groups

		self.shapes_list = list(self.shapes.values())
		self.groups_list = list(self.groups.values())
		self.num_shapes = len(self.shapes_list)

		self.problem = layout_problem

		self.model = None

		if solver is None: 
			self.solver = pywrapcp.Solver("solver")
		else: 
			self.solver = solver

		# Keeps track of the overall number of solutions found so far
		self.solutions_found = 0

		self.helper = or_tools_helper.OrToolsHelper(self.solver, self.problem.box_width, self.problem.box_height)

		# Previous solutions 
		self.previous_solutions = []

		self.solved = False

		self.db = None
		
	def check(self):
		return self.solver.check()

	def unsat_core(self):
		return True

	def increment_solutions(self): 
		self.solutions_found += 1

	def update_solution_from_model(self): 
		for shape_id, shape in self.shapes.items(): 
			final_x = shape.adjusted_x.Value()
			final_y = shape.adjusted_y.Value()
			final_width = shape.adjusted_width.Value()
			final_height = shape.adjusted_height.Value()

			shape.curr_x = final_x
			shape.curr_y = final_y
			shape.curr_width = final_width
			shape.curr_height = final_height

	def get_previous_solution_negation(self): 
		curr_values = []
		for shape in self.shapes.values(): 
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
		for shape in self.shapes.values(): 
			json_shape = copy.deepcopy(shape.json_shape)
			json_shape["location"]["x"] = shape.curr_x
			json_shape["location"]["y"] = shape.curr_y
			json_shape["size"]["width"] = shape.curr_width
			json_shape["size"]["height"] = shape.curr_height

			final_json.append(json_shape)
		return final_json

	def print_cost_scores(self): 
		# Print out the current balance cost
		# final_balance = self.model[self.helper.balance_cost]
		# balance = final_balance.as_string()
		# print("Balance cost: " + balance)

		# Print out the current alignments cost percentage
		final_alignment = self.model[self.helper.alignments_cost]
		# alignment = Fraction(final_alignment.as_string())
		# alignment = float(alignment)
		# print("Alignment cost: " + final_alignment.as_string())

		# Left balance
		# final_l_balance = self.model[self.helper.l_balance]
		# final_r_balance = self.model[self.helper.r_balance]
		# final_s_balance = self.model[self.helper.s_balance]
		# l_balance = final_l_balance.as_string()
		# r_balance = final_r_balance.as_string()
		# s_balance = final_s_balance.as_string()
		# print("Left balance cost: " + l_balance)
		# print("Right balance cost: " + r_balance)
		# print("Splitting balance cost: " + s_balance)

	def get_variables_list(self): 
		variables = []
		for shape in self.shapes.values(): 
			variables.append(shape.adjusted_x)
			variables.append(shape.adjusted_y)
			variables.append(shape.adjusted_width)
			variables.append(shape.adjusted_height)
		return variables

	def update_constraints_from_model(self): 
		if not self.db: 
			variables = self.get_variables_list()
			total_pairs = self.num_shapes * (self.num_shapes-1)
			obj_expr = self.solver.IntVar(0, total_pairs, "obj_expr")
			self.solver.Add(obj_expr == self.helper.num_alignments(curr_shapes))
			self.objective = self.solver.Maximize(obj_expr, 1)

			self.db = self.solver.Phase(variables, self.solver.CHOOSE_FIRST_UNBOUND, self.solver.ASSIGN_MIN_VALUE)
			self.solver.Solve(self.db, self.objective)

			# if self.collector.SolutionCount() > 0:
			# 	num_soltuions = self.collector.SolutionCount()
			# 	best_solution = self.collector.SolutionCount() - 1
			# 	print("Objective value:", self.collector.ObjectiveValue(best_solution))
				# print()
				# print('x= ', collector.Value(best_solution, x))
				# print('y= ', collector.Value(best_solution, y))

		# if self.solutions_found > 0:
		# 	# Then, get and store the previous solution conjunction into the list of previous solutions 
		# 	previous = self.get_previous_solution_negation() 
		# 	self.previous_solutions.append(previous)
			# self.solver.assert_and_track(previous, 'prev' + str(self.solutions_found))
			# self.solver.Add(previous)
		# 	self.solver.pop()
			
		# # Create a new solving context
		# self.solver.push()

		# Add the previous solutions back into the set of constraints
		# if self.solutions_found > 0:
		# 	# TODO: possibly optimize so we can just add a new one on every time
		# 	for i in range(0, len(self.previous_solutions)):
		# 		self.solver.assert_and_track(self.previous_solutions[i], 'prev' + str(i))
			
			####### Add one value as a constraint to the solution
			# Add the distance function into the set of constraints
			# all_shapes = list(self.shapes.values())
			# self.helper.add_distance_cost(all_shapes)
			# if self.solutions_found == 0:
			# 	p_index = 0
			# 	for shape in all_shapes:
			# 		self.helper.add_previous_solution_from_or©iginal(shape, p_index)
			# 		p_index += 4
			# else:
			# 	p_index = 0
			# 	for shape in all_shapes:
			# 		f_x = self.model[shape.adjusted_x]
			# 		f_y = self.model[shape.adjusted_y]
			# 		adj_x = f_x.as_string()
			# 		adj_y = f_y.as_string()
			# 		adj_x = int(adj_x)
			# 		adj_y = int(adj_y)
			#
			# 		f_width = self.model[shape.adjusted_width]
			# 		f_height = self.model[shape.adjusted_height]
			# 		adj_width = f_width.as_string()
			# 		adj_height = f_height.as_string()
			# 		adj_width = int(adj_width)
			# 		adj_height = int(adj_height)
			# 		new_bounds = [adj_x, adj_y, adj_width, adj_height]
			#
			# 		self.helper.add_previous_solution_from_bounds(new_bounds, p_index)
			# 		p_index += 4
			#
			# 	# Previous computed distance
			# 	# prev_distance = self.model[self.distance_cost]
			# 	# dist = final_distance.as_string()
			# 	# dist = int(dist)
			# 	self.helper.add_distance_increase_cost()


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
		# print("Current alignments cost: " + str(self.current_alignments))
		# if self.current_alignments >= 0:
		# 	self.solver.pop()
		# 	self.current_alignments -= 1
		# 	self.solver.push()
		# 	self.solver.add(self.alignment_cost == self.current_alignments)
		# else:
		# 	return False
		return True
	
	def get_solution(self): 
		self.next_solution = self.solver.NextSolution()
		if self.next_solution: 
			self.update_solution_from_model()
			return "sat"
		else: 
			return "unsat"
		# print("Looking for a solution.")
		# Pass in the cost function
		# curr_shapes = list(self.shapes.values())

		# print("minimizing the balance cost")
		# balance_cost = self.solver.minimize(self.helper.get_horizontal_balance_cost(curr_shapes))
		# alignments_cost = self.solver.minimize(self.helper.get_alignments_cost(curr_shapes))
		# constraints = self.solver.sexpr()
		# result = self.solver.check();

		# # with open('../results/constraints.rkt', 'w') as outfile: 
		# # 	outfile.write(constraints)
		# # upper_vals = self.solver.upper_values(object_fun)
		# # upper = self.solver.upper(object_fun)
		# # lower_vals = self.solver.lower_values(object_fun)
		# # lower = self.solver.lower(object_fun)

		# # obj = self.solver.objectives()
		# if str(result) == 'sat': 
		# 	# Find one solution for now
		# 	self.model = self.solver.model()
		# 	self.update_solution_from_model()
		# 	return True
		# else: 
		# 	print("No solution found :(")
		# return False








