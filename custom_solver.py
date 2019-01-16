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
NUM_SOLUTIONS = 10
NUM_DIFFERENT = 5
SOLVER_WAIT = 0.2

class CustomSolver(object):
	def __init__(self, elements, previous_solutions, relative_designs=""): 
		self.elements = elements # Set of design elements to solve for a design from 
		self.previous_solutions = previous_solutions # Set of previous designs, don't produce these again
		self.num_solutions = 0
		self.relative_designs = relative_designs
		self.solutions = []

	def run_solve(self, z3_context, elements_json, prev_solutions_json, results, i):
		# Get the element shapes from the commmand line
		elements = json.loads(elements_json)
		prev_solutions = json.loads(prev_solutions_json)

		# Construct the solver instance
		solver = z3_solver.Solver(z3_context, elements, prev_solutions)

		# Solve for a design solution
		state = sh.Solution()
		time_start = time.time()
		solution = solver.branch_and_bound(state)
		time_end = time.time()
		logging.debug("Time in z3 " + str(i) + ": " + str(solver.time_z3))
		logging.debug("Time to generate a solution " + str(i) + ": " + str(time_end-time_start))
		results[i] = solution

	def solve(self):
		# Branch and bound get one solution at a time
		time_start = time.time()
		self.branch_and_bound_n_solutions()
		time_end = time.time()
		logging.debug('Total time in branch and bound: ' + str(time_end-time_start))
		logging.debug("number of solutions found: " + str(len(self.solutions)))

		if len(self.solutions):
			self.solutions.sort(key=lambda s: s["cost"])
			print("lowest cost: " + str(self.solutions[0]["cost"]))
			print("highest cost: " + str(self.solutions[len(self.solutions)-1]["cost"]))
		else:
			print("No solutions found.")
		return self.solutions

	def check(self):
		# Branch and bound get one solution at a time
		time_start = time.time()
		self.check_validity_of_solutions()
		time_end = time.time()
		logging.debug('Total time checking validity: ' + str(time_end-time_start))

		return self.solutions

	def run_check(self, z3_context, elements_json, solution, results, i):
		elements = json.loads(elements_json)

		# Construct the solver instance
		solver = z3_solver.Solver(z3_context, elements) 

		time_start = time.time()
		solution = solver.check_validity(solution)
		time_end = time.time()
		logging.debug("Time to check validity of solution " + str(i) + ": " + str(time_end-time_start))

		results[i] = solution

	def check_validity_of_solutions(self): 
		manager = multiprocessing.Manager()
		results = manager.dict()
		jobs = []

		prev_solutions = json.loads(self.previous_solutions)
		num_previous = len(prev_solutions)

		i = 0 
		while i < num_previous: 
			logging.debug("Launching z3check solution: " + str(i))
			
			solution = prev_solutions[i]
			z3_context = z3.Context()
			p = multiprocessing.Process(target=self.run_check, 
				args=(z3_context, self.elements, solution, results, solution['id']))

			jobs.append(p)
			p.start()
			i += 1

		logging.debug("Number of processes: " + str(len(jobs)))
		for proc in jobs: 
			proc.join()

		# Update solutions with their validity
		for solution in prev_solutions: 
			sln_id = solution['id']
			results_sln = results[sln_id]
			solution['valid'] = results_sln['valid']
			if 'conflicts' in results_sln:
				solution['conflicts'] = results_sln['conflicts']

			if 'added' in results_sln: 
				solution['added'] = results_sln['added']

			if 'removed' in results_sln: 
				solution['removed'] = results_sln['removed']
		self.solutions = prev_solutions

	def branch_and_bound_n_solutions(self):
		manager = multiprocessing.Manager()
		results = manager.dict()
		jobs = []

		i = 0
		while i < NUM_SOLUTIONS:
			# Each instance of Z3 needs to use a different context object 
			logging.debug("Launching z3solve: " + str(i))

			z3_context = z3.Context()
			p = multiprocessing.Process(target=self.run_solve,
				args=(z3_context, self.elements, self.previous_solutions, results, i))
			jobs.append(p)
			p.start()
			i += 1

		logging.debug("Number of processes: " + str(len(jobs)))
		for proc in jobs:
			proc.join()

		slns = results.values()
		print("Number of solutions: "  + str(len(slns)))
		self.solutions = slns







