from z3 import *
import time
import sys
import multiprocessing
import json
import z3_solver
import logging
import solver_helpers as sh

GRID_CONSTANT = 5
GLOBAL_PROXIMITY = 5
NUM_SOLUTIONS = 50
NUM_DIFFERENT = 5
SOLVER_WAIT = 0.2

class CustomSolver(object):
	def __init__(self, elements, previous_solutions, relative_designs=""): 
		self.elements = elements # Set of design elements to solve for a design from 
		self.previous_solutions = previous_solutions # Set of previous designs, don't produce these again
		self.num_solutions = 0
		self.relative_designs = relative_designs
		self.solutions = []

	def check(self):
		# results = dict()
		# constraints = ""

		# # Encode the fixed constraints 
		# for shape in self.shapes.values(): 
		# 	constraints += self.cb.init_locks(shape)
		# self.override_solver.add_constraints(constraints)

		# time_start = time.time()
		# valid = self.z3_check(time_start)

		# results["valid"] = valid

		# # Check all of the previous solutions
		# for solution in self.previous_solutions: 
		# 	# Create a new stack context for the solver before we encode the fixed values for the solution
		# 	self.solver.push() 

		# 	# Look for any shapes that have been removed or added in this solution
		# 	shapes_removed = []
		# 	shapes_added = []
		# 	elements = solution["elements"]
		# 	for elementID in elements:
		# 		if elementID not in self.shapes:
		# 			shapes_removed.append(elementID)

		# 	for shapeID in self.shapes:
		# 		shape = self.shapes[shapeID]
		# 		if shapeID not in elements and (shape.type != "container" or len(shape.children)):
		# 			shapes_added.append(shapeID)

		# 	if len(shapes_added) or len(shapes_removed):
		# 		# If any shapes were added or removed from the canvas since this solution was retrieved
		# 		# Mark the solution as invalid
		# 		solution["valid"] = False

		# 		# Send back the added and removed shapes to be used for highlighting inconsistencies in the constriants tree
		# 		solution["added"] = shapes_added
		# 		solution["removed"] = shapes_removed

		# 		print("Shapes were added or removed. not resolving. ")
		# 	else:
		# 		# For this solution, fix the values of the variables to the solution values
		# 		# Otherwise, check the solution for validity again
		# 		# This encodes the values that should be fixed for this solution
		# 		self.cb.init_solution_constraints(self.shapes, elements, solution["id"])

		# 		start_time = time.time()
		# 		result = self.z3_check(start_time)
		# 		unsat_core = self.solver.unsat_core()

		# 		# update the valid state of the solution
		# 		solution["valid"] = result

		# 		if result:
		# 			# Remove an previous conflicts if the solution is solveable again. 
		# 			if "conflicts" in solution: 
		# 				del solution["conflicts"]

		# 			print("Solution could be found.")
		# 		else:
		# 			# Get the unsat core for each solution
		# 			unsat_core = self.solver.unsat_core()

		# 			# Parse the output message to send identifiers to highlight the conflicting constraints
		# 			conflicts = sh.parse_unsat_core(unsat_core)
		# 			solution["conflicts"] = conflicts
					
		# 			print("Solution could not be found.")

		# 	self.solver.pop()

		# time_end = time.time()
		# total_time = time_end - time_start
		# print("Total time to check satisfiability: " + str(total_time))
		# results["solutions"] = self.previous_solutions
		# return results
		return True

	def run_solve(self, z3_context, elements_json, prev_solutions_json, results, i):
		# Get the element shapes from the commmand line
		elements = json.loads(elements_json)
		prev_solutions = json.loads(prev_solutions_json)

		# Construct the solver instance
		solver = z3_solver.Solver(z3_context, elements, prev_solutions)

		# Solve for a design solution
		state = sh.Solution()
		solution = solver.branch_and_bound(state)
		logging.debug(solution)
		results[i] = solution

	def solve(self):
		# Branch and bound get one solution at a time
		time_start = time.time()
		self.branch_and_bound_n_solutions()
		time_end = time.time()
		print('Total time in branch and bound: ' + str(time_end-time_start))
		print("number of solutions found: " + str(len(self.solutions)))

		if len(self.solutions):
			self.solutions.sort(key=lambda s: s["cost"])
			print("lowest cost: " + str(self.solutions[0]["cost"]))
			print("highest cost: " + str(self.solutions[len(self.solutions)-1]["cost"]))
		else:
			print("No solutions found.")
		return self.solutions

	# def z3_check(self, time_start): 
	# 	time_z3_start = time.time()
	# 	result = self.solver.check()
	# 	time_z3_end = time.time()
	# 	time_z3_total = time_z3_end - time_z3_start
	# 	self.time_z3 += time_z3_total
	# 	if str(result) == 'sat': 
	# 		return True
	# 	else: 
	# 		return False

	def branch_and_bound_n_solutions(self):
		manager = multiprocessing.Manager()
		results = manager.dict()
		jobs = []

		i = 0
		while i < NUM_SOLUTIONS:
			# Each instance of Z3 needs to use a different context object 
			logging.debug("Launching z3solve: " + str(self.num_solutions))

			z3_context = z3.Context()
			p = multiprocessing.Process(target=self.run_solve,
				args=(z3_context, self.elements, self.previous_solutions, results, i))
			jobs.append(p)
			p.start()

			# pid = subprocess.Popen(["python", "z3_solver.py", self.elements, self.previous_solutions],
			# 					   stdout=subprocess.PIPE)
			# out, err = pid.communicate()
			# out = out.decode("utf-8")
			# out = out.replace("'", '"')
			# sln = json.loads(out)
			# self.num_solutions += 1
			i += 1

		logging.debug("Number of processes: " + str(len(jobs)))
		for proc in jobs:
			proc.join()

		slns = results.values()
		print("Number of solutions: "  + str(len(slns)))
		self.solutions = slns







