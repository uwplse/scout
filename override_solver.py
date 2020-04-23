class OverrideSolver(object):
	def __init__(self, solver):
		""" Wrapper for the solver class so that 
			we can toggle between different add methods for debugging.
		"""
		self.solver = solver
		self.debug = True
		self.ctx = solver.ctx
		self.num_constraints = 0

	def load_constraints(self, constraints):
		""" Load in the set of constraints from an SMT lib string """ 
		self.solver.from_string(constraints)

	def model(self):
		""" Return the current solver model """ 
		return self.solver.model()

	def assertions(self):
		""" Return the current set of assertions """ 
		return self.solver.assertions()

	def add(self, constraint, name=""): 
		""" Add a constraint based on the mode 

			Parameters: 
				constraint: Constraint string to add to assertions 
				name: Optional name string to give the assertion for debugging 
		"""
		# Debugging mode uses assert and track so that we can see the names fo variables in the output. 
		if len(name) and self.debug: 
			self.solver.assert_and_track(constraint, name)
		else: 
			self.solver.add(constraint)