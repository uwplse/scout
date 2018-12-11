	
# This uses an alternate method for setting up disjunctings
# Does not result in faster performance than using a standard OR constraint :(
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


# This is the old solving algorithm that used the cost optimization function with no backgracking involved
	# def old_solving_pass(self):
	# 	while solutions_found < MAX_SOLUTIONS:
	# 		print("Number of solutions: " + str(solutions_found))
	# 		if solutions_found > 0:
	# 			self.solver.add_constraint_from_solution()
	#
	# 			# Now solve for a new solution
	# 			sln = self.solver.get_solution()
	# 			if not sln:
	# 				break
	# 			else:
	# 				new_solution = self.get_next_solution()
	# 				results.append(new_solution)
	# 				solutions_found += 1
	# 		else:
	# 			sln = self.solver.get_solution()
	# 			if sln:
	# 				new_solution = self.get_next_solution()
	# 				results.append(new_solution)
	# 				solutions_found += 1
	# 			else:
	# 				break