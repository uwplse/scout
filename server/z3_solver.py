import copy
from z3 import *
import z3_helper

class Z3Solver(object): 
	def __init__(self, layout_problem):
		self.shapes = layout_problem.shapes
		self.groups = layout_problem.groups
		self.problem = layout_problem

		self.model = None
		self.solver = Solver()
		self.solver.set(unsat_core=True)

		# Keeps track of the overall number of solutions found so far
		self.solutions_found = 0

		self.helper = z3_helper.Z3Helper(self.solver, self.problem.box_width, self.problem.box_height)
		
	def check(self):
		return self.solver.check()

	def unsat_core(self):
		return self.solver.unsat_core()

	def increment_solutions(self): 
		self.solutions_found += 1

	def get_json_shapes(self): 
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
		if self.solutions_found > 0:
			# Print out the current alignment cost
			# final_alignments = self.model[self.alignment_cost]
			# f_aligns = final_alignments.as_string()
			# print("num alignments: " + f_aligns)

			final_distance = self.model[self.helper.distance_cost]
			dist = final_distance.as_string()
			print("Distance from previous: " + dist)

			self.solver.pop()
			
		self.solver.push()
		
		####### Add one value as a constraint to the solution
		# Add the distance function into the set of constraints
		all_shapes = list(self.shapes.values())
		self.helper.add_distance_cost(all_shapes)
		if self.solutions_found == 0: 
			p_index = 0
			for shape in all_shapes:
				self.helper.add_previous_solution_from_original(shape, p_index)
				p_index += 4
		else: 
			p_index = 0
			for shape in all_shapes:
				f_x = self.model[shape.adjusted_x]
				f_y = self.model[shape.adjusted_y]
				adj_x = f_x.as_string()
				adj_y = f_y.as_string()
				adj_x = int(adj_x)
				adj_y = int(adj_y)

				f_width = self.model[shape.adjusted_width]
				f_height = self.model[shape.adjusted_height]
				adj_width = f_width.as_string()
				adj_height = f_height.as_string()
				adj_width = int(adj_width)
				adj_height = int(adj_height)
				new_bounds = [adj_x, adj_y, adj_width, adj_height]

				self.helper.add_previous_solution_from_bounds(new_bounds, p_index)
				p_index += 4

			# Previous computed distance
			# prev_distance = self.model[self.distance_cost]
			# dist = final_distance.as_string()
			# dist = int(dist)
			self.helper.add_distance_increase_cost()


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
		print(self.solver.sexpr())
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








