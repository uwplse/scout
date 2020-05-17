from z3 import *
import time
import sys
import multiprocessing
import json
import z3_solver
import logging
import solution as sln

NUM_SOLUTIONS = 10
TIMEOUT = 10

class CustomSolver(object):
	def __init__(self, elements, previous_solutions, relative_designs=""): 
		""" Custom solver class is in charge of initializing threads, and launching solving processes to Z3 based on whether 
			we are doing a reflow to attempt to repair invalid solutions (reflow), 
			a check on validity of current solutions (check), or solving for new solutions (solve)

			Attributes: 
				elements: Set of design elements 
				previous_solutions: List of previous solutions where each is an element tree of a previous solution 
				num_solutions: Number of solutions found so far 
				solutions: List that will contain the set of solved for solutions after threads return 
		""" 
		self.elements = elements # Set of design elements to solve for a design from 
		self.previous_solutions = previous_solutions # Set of previous designs, don't produce these again
		self.num_solutions = 0
		self.solutions = []

	def solve(self):
		""" Calls the solve process to return N new solutions. 
		""" 		
		time_start = time.time()
		self.branch_and_bound_n_solutions()
		time_end = time.time()
		logging.debug('Total time in branch and bound: ' + str(time_end-time_start))

		if len(self.solutions):
			self.solutions.sort(key=lambda s: s["cost"])
			print("lowest cost: " + str(self.solutions[0]["cost"]))
			print("highest cost: " + str(self.solutions[len(self.solutions)-1]["cost"]))
		else:
			print("No solutions found.")
		return self.solutions

	def check(self):
		""" Calls the check process to update the validity of the current set of active solutions. 
		""" 	
		time_start = time.time()
		self.check_validity_of_solutions()
		time_end = time.time()
		logging.debug('Total time checking validity: ' + str(time_end-time_start))

		return self.solutions

	def reflow(self, changed_element_id, changed_property, changed_value, keep_or_prevent):
		""" Calls the reflow process to attempt to repair invalid solutions. 

			Parameters: 
				changed_element_id: ID of the changed element
				changed_property: Name of the variable that was changed 
				changed_value: The value that the variable was changed to 
				keep_or_prevent: Whether the update was to "keep" or "prevent" the value.
		""" 
		time_start = time.time()
		self.reflow_solutions(changed_element_id, changed_property, changed_value, keep_or_prevent)
		time_end = time.time()
		logging.debug('Total time reflowing solutionss: ' + str(time_end-time_start))

		return self.solutions


	def run_solve(self, z3_context, elements_json, prev_solutions_json, results, i):
		""" Launch the solving process inside a thread to get a new design solution 

			Parameters: 
				z3_context: Z3 context objects
				elements_json: JSOn string of the elements tree 
				previous_solutions_json: JSON string of the previous soluitons to avoid producing again 
				results: Results collection to store the checked solution 
				i: index to store in the results collection 
		"""
		# Get the element shapes from the commmand line
		elements = json.loads(elements_json)
		prev_solutions = json.loads(prev_solutions_json)

		# Construct the solver instance
		solver = z3_solver.Solver(z3_context, elements, prev_solutions)

		# Solve for a design solution
		state = sln.Solution()
		time_start = time.time()
		solution = solver.branch_and_bound(state)

		time_end = time.time()
		logging.debug("Time in z3 " + str(i) + ": " + str(solver.time_z3))
		logging.debug("Time to generate a solution " + str(i) + ": " + str(time_end-time_start))
		if solution is None: 
			logging.debug("----No solution found---")
		results[i] = solution

	def run_check(self, z3_context, elements_json, solution, results, i):
		elements = json.loads(elements_json)
		""" Launch a check thread 

			Parameters: 
				z3_context: Z3 context objects
				elements_json: JSOn string of the elements tree 
				solution: solution elements tree of the solution to check 
				results: Results collection to store the checked solution 
				i: index to store in the results collection 
		"""

		# Construct the solver instance
		# Do not prune the variable domains when we are checking validitiy so we 
		# don't remove the values for the previous solution from the domains. 
		solver = z3_solver.Solver(z3_context, elements, prune_domains=False) 

		time_start = time.time()
		solution = solver.check_validity(solution)
		time_end = time.time()
		logging.debug("Time to check validity of solution " + str(i) + ": " + str(time_end-time_start))

		results[i] = solution

	def run_reflow(self, z3_context, elements, solution, changed_element_id, 
		changed_property, changed_value, keep_or_prevent, results, i):
		""" Launch a reflow thread. 

			Parameters: 
				z3_context: A Z3 context object 
				elements: JSON string of the element tree 
				solution: The currrent solution tree from the previous soluiton with the values. 
				changed_element_id: ID of the changed element
				changed_property: Name of the variable that was changed 
				changed_value: The value that the variable was changed to 
				keep_or_prevent: Whether the update was to "keep" or "prevent" the value.
				results: collection for the results of reflow 
				i: Index to store in the results collection 
		"""
		elements = json.loads(elements)

		# Construct the solver instance
		solver = z3_solver.Solver(z3_context, elements, prune_domains=False)

		time_start = time.time()

		# Solver class repairs the soluiton 
		repaired_solution = solver.repair_solution(solution, changed_element_id, changed_property, changed_value, keep_or_prevent)
		if repaired_solution is None:
			# This means the solution could not be repaired, so we request a new one to replace it. 
			print("Getting brand new solution")
			solver = z3_solver.Solver(z3_context, elements)
			# Get a new soltuion to replace the invalid one
			state = sln.Solution()
			time_start = time.time()
			repaired_solution = solver.branch_and_bound(state)

		time_end = time.time()
		logging.debug("Time to check validity of solution " + str(i) + ": " + str(time_end-time_start))

		results[i] = repaired_solution

	def reflow_solutions(self, changed_element_id, changed_property, changed_value, keep_or_prevent):
		""" Launch reflow threads. Reflow threads will try to repair the invalid solutions based on the updated 
			property and element. """ 
		manager = multiprocessing.Manager()
		results = manager.dict()
		jobs = []

		solutions = json.loads(self.previous_solutions)
		num_previous = len(solutions)

		i = 0 
		while i < num_previous: 
			logging.debug("Launching reflow solution: " + str(i))
			
			solution = solutions[i]
			z3_context = z3.Context()
			p = multiprocessing.Process(target=self.run_reflow, 
				args=(z3_context, self.elements, solution, changed_element_id, changed_property, 
					changed_value, keep_or_prevent, results, solution['id']))

			jobs.append(p)
			p.start()
			i += 1

		logging.debug("Number of processes: " + str(len(jobs)))
		for proc in jobs: 
			proc.join()

		print("number of solutions: ")
		print(str(len(solutions)))
		repaired_solutions = []
		for solution in solutions: 
			sln_id = solution['id']
			if sln_id in results: 
				results_sln = results[sln_id]
				if results_sln is not None and results_sln['valid'] and not len(results_sln['conflicts']):
					# Copy the repaired elements into the solution if a solution could be found
					# update conflics
					solution['elements'] = results_sln['elements']
					solution['conflicts'] = results_sln['conflicts']
					solution['id'] = results_sln['id'];
					repaired_solutions.append(solution)

		self.solutions = repaired_solutions

	def check_validity_of_solutions(self): 
		""" Launch multiple threads to check validity of previous design solutions """ 
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

		# Update solutions with their validity after solving. 
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
		"""Main method to launch multiple threads for solving """
		manager = multiprocessing.Manager()
		results = manager.dict()
		jobs = []

		i = 0
		while i < NUM_SOLUTIONS:
			# Each instance of Z3 needs to use a different context object 
			logging.debug("Launching z3solve: " + str(i))

			# Have to create new z3 context for each thread so they don't interfere with each other. 
			z3_context = z3.Context()
			p = multiprocessing.Process(target=self.run_solve,
				args=(z3_context, self.elements, self.previous_solutions, results, i))
			jobs.append(p)
			p.start()
			i += 1


		start = time.time()
		timed_out = True 
		while time.time() - start <= TIMEOUT: 
			if any(proc.is_alive() for proc in jobs): 
				time.sleep(.1)
			else: 
				timed_out = False
				break 

		if timed_out: 
			# Join threads back after all have completed 
			for proc in jobs:
				if proc.is_alive():  
					print("Joining solver process after timeout.")
					proc.join(0)
					proc.terminate()
		else: 
			print("All solver threads completed before timeout.")

		# Get results from result object 
		slns = results.values()
		slns = [sln for sln in slns if sln is not None]

		print("Number of solutions: "  + str(len(slns)))
		self.solutions = slns







