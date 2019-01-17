from z3 import * 
import time
import sys
import json
import random
import constraint_builder
import shapes as shape_classes
import smtlib_builder as smt
import solver_helpers as sh
import logging
logging.basicConfig(level=logging.DEBUG)

class OverrideSolver(object):
	def __init__(self, solver):
		self.solver = solver
		self.debug = True
		self.ctx = solver.ctx
		self.num_constraints = 0

	def load_constraints(self, constraints):
		self.solver.from_string(constraints)

	def model(self):
		return self.solver.model()

	def assertions(self):
		return self.solver.assertions()

	def add(self, constraint, name=""): 
		if len(name) and self.debug: 
			self.solver.assert_and_track(constraint, name)
		else: 
			self.solver.add(constraint)

class Solver(object): 
	def __init__(self, solver_ctx, elements, solutions=[], relative_designs=None):
		# Construct the solver instance we will use for Z3
		self.solver_ctx = solver_ctx
		self.solver = z3.Solver(ctx=self.solver_ctx)
		self.solver.set(unsat_core=True)
		self.solutions = [] # Initialize the variables somewhere
		self.unassigned = []
		self.elements = elements
		self.previous_solutions = solutions
		self.relative_search = False
		self.shapes, self.root = self.build_shape_hierarchy()
		self.root = self.root[0]

		self.variables = self.init_variables()
		self.output_variables = self.init_output_variables()
		self.variables_different = Int('VariablesDifferent')

		self.override_solver = OverrideSolver(self.solver)
		self.cb = constraint_builder.ConstraintBuilder(self.override_solver)

		# Build the initial set of constraints on the shapes and containers 
		time_start = time.time()

		self.cb.declare_variables(self.shapes)
		self.init_constraints()
		time_end = time.time()
		logging.debug("Time to create constraints (init_constraints): " + str(time_end-time_start))

		# Intialize the locked constraints (Keep/Prevent values)
		start_time = time.time()
		for shape in self.shapes.values(): 
			self.cb.init_locks(shape)
		end_time = time.time()
		logging.debug("Time taken to encode locks: " + str(end_time-start_time))
			
		# Initialize the constraints preventing previous solutions from re-occuring
		start_time = time.time()
		# Prevent the previous solutions that have the same set of elements
		solutions_to_prevent = self.get_previous_solutions_to_prevent()
		self.cb.init_previous_solution_constraints(solutions_to_prevent, self.shapes)
		end_time = time.time()
		logging.debug("Time taken to encode previous solutions: " + str(end_time-start_time))

		# For debugging how large the search space isd
		size = self.compute_search_space()
		logging.debug("Total search space size: " + str(size))
		sys.stdout.flush()
		start_time = time.time()

		self.unassigned = copy.copy(self.variables)

		time_start = time.time()
		self.cb.load_constraints()
		time_end = time.time()
		logging.debug("Time to parse constraints: "  + str(time_end-time_start))

		sys.stdout.flush()

		# For performance metrics
		self.time_z3 = 0
		self.z3_calls = 0
		self.branches_pruned = 0

		# Initialize any relative design constraints, if given 
		# if "relative_design" in relative_designs: 
		# 	self.relative_search = True
		# 	relative_design_elements = relative_designs["relative_design"]
		# 	relative_design_action = relative_design["relative_action"]

		# 	if relative_design_action == "like": 
		# 		self.cb.init_relative_design_constraints(relative_design_elements)
		# 		# Set up constraints to get designs more like the relative design
		# 		# This means any returned solution should only have 1 variable different than the relative design

	def get_previous_solutions_to_prevent(self): 
		# Get the set of previous solutions that have the same set of shapes as the current outline
		solutions_to_prevent = []
		for solution in self.previous_solutions: 
			elements = []
			shapes_added, shapes_removed = self.check_added_or_removed_shapes(elements)
			if not len(shapes_added) and not len(shapes_removed): 
				solutions_to_prevent.append()
		return solutions_to_prevent

	def init_constraints(self):
		# Initialize the set of constraints on shapes and containers
		canvas = None
		for shape in self.shapes.values(): 
			if shape.type == "canvas":
				self.cb.init_canvas_constraints(shape)
				canvas = shape

			if shape.type == "container": 
				self.cb.init_container_constraints(shape, self.shapes)

		for shape in self.shapes.values():
			if shape.type == "leaf":
				self.cb.init_shape_bounds(shape)
				self.cb.init_shape_baseline(shape)
				# self.cb.init_shape_grid_values(shape, canvas)

	def build_shape_hierarchy(self): 
		shapes = dict()
		root = self.construct_shape_hierarchy([self.elements], shapes)
		return shapes,root

	def construct_shape_hierarchy(self, elements, shapes, parent_emphasis="normal", at_root=False):
		shape_hierarchy = []
		num_siblings = len(elements)
		for i in range(0, len(elements)): 
			element = elements[i]
			element_type = element["type"]

			# If parent node emphasis is set, cascade that value to the child elements
			element_emphasis = element["importance"] if "importance" in element else "normal"
			if parent_emphasis != "normal": 
				element["importance"] = parent_emphasis
				element_emphasis = parent_emphasis

			sub_hierarchy = None

			is_at_root = True if element_type == "canvas" else False
			if "children" in element: 
				children = element["children"]
				sub_hierarchy = self.construct_shape_hierarchy(children, shapes, element_emphasis, is_at_root)

			shape_object = None
			if element_type == "canvas": 
				shape_object = shape_classes.CanvasShape(self.solver_ctx, 
					element["name"], element, num_siblings)
				shapes[shape_object.shape_id] = shape_object
			elif element_type == "group" or element_type == "labelGroup":
				shape_object = shape_classes.ContainerShape(self.solver_ctx, 
					element["name"], element, num_siblings, at_root=at_root)
				shapes[shape_object.shape_id] = shape_object
			else:
				shape_object = shape_classes.LeafShape(self.solver_ctx,
					element["name"], element, num_siblings, at_root=at_root)
				shapes[shape_object.shape_id] = shape_object

			if sub_hierarchy is not None: 
				shape_object.add_children(sub_hierarchy)

			shape_hierarchy.append(shape_object)

		return shape_hierarchy

	def init_variables(self):
		last = []
		first = []
		variables = []

		for shape in self.shapes.values():
			if shape.type == "container": 
				first.append(shape.variables.arrangement)
				last.append(shape.variables.alignment)
				last.append(shape.variables.proximity)
				last.append(shape.variables.distribution)
			
			elif shape.type == "canvas":
				last.append(shape.variables.alignment)
				last.append(shape.variables.justification)
				last.append(shape.variables.margin)
				last.append(shape.variables.columns)
				# last.append(shape.variables.background_color)
			
			if shape.type == "leaf": 
				last.append(shape.variables.size_factor)

		# More important variables are in first. putting them at the end of the list , they will get assigned first
		variables.extend(last)
		variables.extend(first)

		# Later: Justification and alignment
		return variables

	def compute_search_space(self):
		total = 1
		for variable in self.variables:
			total *= len(variable.domain)
		return total	

	def init_output_variables(self):
		output_variables = []
		for shape in self.shapes.values(): 
			if shape.type != "container" and shape.type != "canvas": 
				output_variables.append(shape.variables.x)
				output_variables.append(shape.variables.y)
		return output_variables

	def restore_state(self): 
		# Unassign and reset the variables
		for variable in self.variables: 
			variable.assigned = None

		self.unassigned = copy.copy(self.variables)

		# Restore the stack context for the solver
		for i in range(0, len(self.variables)):
			self.solver.pop()

	def select_next_variable(self):
		return self.unassigned.pop()

	def select_next_variable_random(self): 
		# Select a random index to assign
		random_index = random.randint(0, len(self.unassigned)-1)
		return random_index, self.unassigned.pop(random_index)

	def restore_variable(self, variable, index):
		variable.assigned = None
		self.unassigned.insert(index, variable)

	def get_randomized_domain(self, variable):
		randomized_domain = variable.domain[0:len(variable.domain)]
		random.shuffle(randomized_domain)
		return randomized_domain

	def encode_assigned_variable(self, variable):
		constraints = smt.declare(variable.id, variable.type)
		if variable.index_domain:
			constraints += smt.assert_expr(smt.eq(variable.id, str(variable.assigned)),
				"variable_" + variable.id + "_assigned_to_" + str(variable.assigned))
			self.override_solver.load_constraints(constraints)
		else:
			dom_value = variable.domain[variable.assigned]
			if variable.type == "String": 
				dom_value = "\"" + dom_value + "\""

			constraints += smt.assert_expr(smt.eq(variable.id, str(dom_value)),
				"variable_" + variable.id + "_assigned_to_" + str(variable.assigned))
			self.override_solver.load_constraints(constraints)

	def encode_previous_solution_from_model(self, model, solution_id): 
		# The next solution cannot be the exact same outputs as the previous assignment
		# It may be possible for multiple solutions to have the same outputs (exact x,y coordinates for all shapes)
		# So to restrict this, we encode the X,Y positions in the clauses to prevent these solutions
		all_values = []
		variables = sh.parse_variables_from_model(model)
		
		decl_constraints = "" # Because from_string requires declaring vars again even if already defined :(
		for v_i in range(0, len(self.output_variables)): 
			variable = self.output_variables[v_i]
			model_var = variables[variable.id]
			variable_value = model[model_var]
			variable_value = variable_value.as_string() 
			variable_value = int(variable_value)
			all_values.append(smt.eq(variable.id, str(variable_value)))
			decl_constraints += smt.declare(variable.id, variable.type)

		constraints = smt.assert_expr(smt.not_expr(smt.and_expr(all_values)), 
			"prevent_prev_solution_" + solution_id + "_from_appearing_again")
		constraints = decl_constraints + constraints
		self.override_solver.load_constraints(constraints)

	def branch_and_bound(self, state):
		if len(self.unassigned) == 0:
			time_z3_start = time.time()
			result = self.solver.check()
			# constraints = self.solver.sexpr()
			self.z3_calls += 1
			time_z3_end = time.time()
			time_z3_total = time_z3_end - time_z3_start
			self.time_z3 += time_z3_total

			if str(result) == 'sat':
				# Find one solution for now
				time_z3_start = time.time()
				model = self.solver.model()
				time_z3_start = time.time()
				time_z3_total = time_z3_end - time_z3_start
				self.time_z3 += time_z3_total

				# Keep the solution & convert to json
				# self.print_solution()
				time_start = time.time()
				sln = state.convert_to_json(self.shapes, model, self.solver_ctx)
				time_end = time.time()
				logging.debug("Time in converting solution to json: " + str(time_end-time_start))
				self.restore_state()

				# Encode the previous solution outputs into the model so we don't produce it again in the next iteration
				self.encode_previous_solution_from_model(model, sln["id"])
				return sln
			else:
				self.invalid_solutions += 1
				# self.print_solution()
		else:
			# Selects the next variable to assign
			var_i, next_var = self.select_next_variable_random()
			state.add_assigned_variable(next_var)

			# Randomize the order in which we iterate through the domain
			random_domain = self.get_randomized_domain(next_var)
			for val_index in range(0, len(random_domain)):
				dom_value = random_domain[val_index]
				in_domain_index = next_var.domain.index(dom_value)
				next_var.assigned = in_domain_index

				# Creates a new stack context for the variable assignment
				self.solver.push()

				# Set the value of the variable to fixed in the solvfer
				self.encode_assigned_variable(next_var)

				# GGet a solution
				time_z3_start = time.time()
				result = self.solver.check()

				time_z3_end = time.time()
				time_z3_total = time_z3_end - time_z3_start
				self.time_z3 += time_z3_total

				# Only branch if the result so far is satisfiable
				if str(result) == 'sat':
					sln = self.branch_and_bound(state)
					if sln is not None: 
						return sln
				else: 
					# self.print_partial_solution()
					self.branches_pruned+=1

				# Remove the stack context after the branch for this assignment has been explored
				self.solver.pop()

			# Then unassign the value
			self.restore_variable(next_var, var_i)
		return 

	def z3_check(self): 
		result = self.solver.check()
		if str(result) == 'sat': 
			return True
		else: 
			return False

	def check_added_or_removed_shapes(self, elements): 
		shapes_added = []
		shapes_removed = []

		# Look for shapes that were added or removed and in that case, we dont' need to check validity 
		for elementID in elements:
			if elementID not in self.shapes:
				shapes_removed.append(elementID)

		for shapeID in self.shapes:
			shape = self.shapes[shapeID]
			if shapeID not in elements and (shape.type != "container" or len(shape.children)):
				shapes_added.append(shapeID)

		return shapes_added, shapes_removed

	def check_validity(self, solution):
		# Look for any shapes that have been removed or added in this solution
		elements = solution["elements"]
		shapes_added, shapes_removed = self.check_added_or_removed_shapes(elements)
		if len(shapes_added) or len(shapes_removed):
			# If any shapes were added or removed from the canvas since this solution was retrieved
			# Mark the solution as invalid
			solution["valid"] = False

			# Send back the added and removed shapes to be used for highlighting inconsistencies in the constriants tree
			solution["added"] = shapes_added
			solution["removed"] = shapes_removed

			print("Shapes were added or removed. not resolving. ")
		else:
			# For this solution, fix the values of the variables to the solution values
			# Otherwise, check the solution for validity again
			# This encodes the values that should be fixed for this solution
			constraints  = self.cb.init_solution_constraints(self.shapes, elements, solution["id"])
			self.override_solver.load_constraints(constraints)

			result = self.z3_check()
			unsat_core = self.solver.unsat_core()

			# update the valid state of the solution
			solution["valid"] = result

			if result:
				# Remove an previous conflicts if the solution is solveable again. 
				if "conflicts" in solution: 
					del solution["conflicts"]

				print("Solution could be found.")
			else:
				# Get the unsat core for each solution
				unsat_core = self.solver.unsat_core()

				# Parse the output message to send identifiers to highlight the conflicting constraints
				conflicts = sh.parse_unsat_core(unsat_core)
				solution["conflicts"] = conflicts
				
				print("Solution could not be found.")

		return solution


	def print_solution(self):
		print("------------Solution------------")
		for variable in self.variables:
			print(variable.shape_id)
			print(str(variable.domain[variable.assigned]))

	def print_partial_solution(self):
		for variable in self.variables:
			if variable.assigned is not None:
				print(variable.shape_id)
				print(str(variable.domain[variable.assigned]))
