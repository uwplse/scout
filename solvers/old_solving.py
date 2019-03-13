# Old solving algorithms we tested out
def branch_and_bound(self, time_start, state=sh.Solution()):
	if self.num_solutions >= NUM_SOLUTIONS:
		return

	if len(self.unassigned) == 0:
		# Ask the solver for a solution to the X,Y location varibles
		# constraints = self.solver.sexpr()
		time_z3_start = time.time()
		result = self.solver.check();
		self.z3_calls += 1
		time_z3_end = time.time()
		time_z3_total = time_z3_end - time_z3_start
		self.time_z3 += time_z3_total
		unsat_core = self.solver.unsat_core()
		constraints = self.solver.sexpr()
		self.print_solution()

		if str(result) == 'sat':
			# print("------Valid solution------")
			self.num_solutions += 1

			# Find one solution for now
			time_z3_start = time.time()
			model = self.solver.model()
			time_z3_start = time.time()
			time_z3_total = time_z3_end - time_z3_start
			self.time_z3 += time_z3_total

			# Keep the solution & convert to json
			sln = state.convert_to_json(self.shapes, model)
			self.solutions.append(sln)
			if len(self.solutions) == NUM_SOLUTIONS:
				time_end = time.time()
				total_time = time_end - time_start
				print("Total time to " + str(NUM_SOLUTIONS) + ": " + str(total_time))
			return
		else:
			self.invalid_solutions += 1
			# self.print_solution()
	else:
		# Selects the next variable to assign
		next_var = self.select_next_variable()
		state.add_assigned_variable(next_var)

		# Randomize the order in which we iterate through the domain
		# random_domain = self.get_randomized_domain(next_var)
		for val_index in range(0, len(next_var.domain)):
			next_var.assigned = val_index

			# Creates a new stack context for the variable assignment
			self.solver.push()

			# Set the value of the variable to fixed in the solver
			self.encode_assigned_variable(next_var)

			# GGet a solution
			time_z3_start = time.time()
			result = self.solver.check()
			self.z3_calls += 1
			time_z3_end = time.time()
			time_z3_total = time_z3_end - time_z3_start
			self.time_z3 += time_z3_total

			# Only branch if the result so far is satisfiable
			if str(result) == 'sat':
				self.branch_and_bound(time_start, state)
			else: 
				# print("pruning branch: ")
				# self.print_partial_solution()
				self.branches_pruned+=1

			# Remove the stack context after the branch for this assignment has been explored
			self.solver.pop()

		# Then unassign the value
		self.restore_variable(next_var, var_i)
	return 

# Loop and solve until num solutions is reached
def z3_solve(self, time_start, search_space_size, state=sh.Solution()):
	print("num variables " + str(len(self.variables)))
	while self.num_solutions < NUM_SOLUTIONS and (self.num_solutions + self.invalid_solutions) < search_space_size: 
		# print("valid: " + str(self.num_solutions))
		# Call to Z3 
		time_z3_start = time.time()
		try: 
			result = self.solver.check();
		except Z3Exception:
			print("Z3 Exception: Could not check for consistency.")
			self.num_solutions += 1 
			continue

		self.z3_calls += 1
		time_z3_end = time.time()
		time_z3_total = time_z3_end - time_z3_start
		self.time_z3 += time_z3_total
		if str(result) == 'sat': 
			self.num_solutions += 1

			# Find one solution for now
			time_z3_start = time.time()
			model = self.solver.model()
			time_z3_start = time.time()
			time_z3_total = time_z3_end - time_z3_start
			self.time_z3 += time_z3_total

			sln = state.convert_to_json(self.shapes, model)
			self.solutions.append(sln)

			# Encode a conjunction into the solver
			if not self.relative_search: 
				# Encodes the previous solution plus a cost function enforce the number of variables to be different by a certain amount each time. 
				self.encode_constraints_for_model(model, sln["id"])
			else:
				# Encodes only the previous solution to prevent that solution from appearing again 
				self.encode_previous_solution_from_model(model, sln["id"])

			# self.print_solution_from_model(model)

			if len(self.solutions) == NUM_SOLUTIONS:
				time_end = time.time()
				total_time = time_end - time_start
				print("Total time to " + str(NUM_SOLUTIONS) + ": " + str(total_time))
		else: 
			self.invalid_solutions += 1

def encode_constraints_for_model(self, model, solution_id): 
	# Pop the previous 
	if self.num_solutions > 1:
		# Remove the previous stack context
		# Pop the stack context before adding the set of constraints to prevent the 
		# Previous solution model from appearing again
		self.solver.pop()

	# The next solution cannot be the exact same set of assignments as the current solution
	# These are cumulative
	self.encode_previous_solution_from_model(model, solution_id)
		
	# Build the vector to store the previous solution
	previous_solution_values = []
	for v_i in range(0, len(self.variables)): 
		variable = self.variables[v_i]
		variable_value = model[variable.z3]
		variable_value = variable_value.as_string() 
		variable_value = int(variable_value)
		previous_solution_values.append(self.previous_solution[v_i] == variable_value)

	if self.num_solutions > 0: 
		self.solver.push()
		
		# Add the previous solution values for the cost function
		self.override_solver.add(previous_solution_values, "prevent previous solution values " + solution_id) 

		# New solutions must be at least NUM_DIFFERENT variable changes away from 
		# the previous solution
		self.override_solver.add(self.variables_different == self.num_variables_different(), "Number of variables different cost function value " + solution_id)

		half = math.floor(len(self.variables)/2)
		self.override_solver.add(self.variables_different >= half, "number of variables different greater than half. " + solution_id)

# Computes the number of variables that are different than the previous solution
def num_variables_different(self):
	vars_diff = 0
	for var_i in range(0, len(self.variables)): 
		variable = self.variables[var_i]
		vars_diff += If(variable.z3 != self.previous_solution[var_i], 1, 0)
	return vars_diff

def print_solution_from_model(self, model): 
	print("------------Solution-------------")
	for variable in self.variables: 
		# Get the value of the variable out of the model 
		variable_value = model[variable.z3]
		variable_value = variable_value.as_string()
		variable_value = int(variable_value)
		print(variable.shape_id)
		print(variable.name)
		print(variable_value)