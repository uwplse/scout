import jsonpickle
import copy
import uuid
from z3 import *
import z3_helper
import shapes as shape_classes
import solver_helpers as sh
import time
import random
import constraint_builder

GRID_CONSTANT = 5
GLOBAL_PROXIMITY = 5
NUM_SOLUTIONS = 3

def get_shape_x_domain(width): 
	domain = []
	beg = 0 
	while beg <= width: 
		domain.append(beg)
		beg += GRID_CONSTANT
	return domain

def get_shape_y_domain(height): 
	domain = []
	beg = 0
	while beg <= height: 
		domain.append(beg)
		beg += GRID_CONSTANT
	return domain

class Solver(object): 
	def __init__(self, elements, groups, canvas_width, canvas_height): 
		self.solutions = [] # Initialize the variables somewhere
		self.unassigned = []
		self.elements = elements
		self.groups = groups
		self.canvas_width = canvas_width
		self.canvas_height = canvas_height
		self.shapes, self.root = self.init_shape_hierarchy(canvas_width, canvas_height)

		# Canvas contains all the elements as direct children for now
		self.canvas_shape = shape_classes.CanvasShape("canvas", [0, 0, canvas_width, canvas_height])	
		self.canvas_shape.add_child(self.root)
		self.variables = self.init_variables()

		# Construct the solver instance we will use for Z3
		self.solver = z3.Solver()
		self.solver_helper = z3_helper.Z3Helper(self.solver, canvas_width, canvas_height)
		self.cb = constraint_builder.ConstraintBuilder(self.solver)
		self.init_domains()

		# For debugging how large the search space isd
		size = self.compute_search_space()
		print("Total search space size: " + str(size))

		# To Do : Move elswhere
		self.cb.init_canvas_constraints(self.canvas_shape)
		for shape in self.shapes: 
			if shape.type == "container": 
				self.cb.init_container_constraints(shape)
			else: 
				self.cb.init_shape_constraints(shape)

		# Timing variables to measure performance for various parts
		self.time_z3 = 0
		self.time_encoding = 0
		self.invalid_solutions = 0 # Used to keep track of the number of invalid solutions
		self.num_solutions = 0
		self.branches_pruned = 0
		self.z3_calls = 0


	def init_shape_hierarchy(self, canvas_width, canvas_height):
		shapes = []

		# Place all the elements directly on the canvas in a group that is sizing to contents
		# This will make it easier to manipulate alignment/justification at the canvas level
		root_id = uuid.uuid4().hex
		root = shape_classes.ContainerShape("canvas_root")
		shapes.append(root)

		# Root will contain the root  level shapes (just below the canvas)
		for element in self.elements:
			element_orig_bounds = [element["location"]["x"],element["location"]["y"],element["size"]["width"],element["size"]["height"]]
			locked = False
			if "locked" in element:
				locked = element["locked"]

			order = None
			if "order" in element: 
				order = element["order"]

			element_shape = shape_classes.LeafShape(element["name"], element_orig_bounds, locked, order)
			shapes.append(element_shape)
			root.add_child(element_shape)

		for element in self.elements:
			element_name = element["name"]
			if "labels" in element:
				# Find the shape & the corresponding labeled shape
				# TODO: Find better way to do this (using dictionary)
				label_shape = [shp for shp in root.children if shp.shape_id == element_name]
				labeled_shape = [shp for shp in root.children if shp.shape_id == element["labels"]]
				label_shape = label_shape[0]
				labeled_shape = labeled_shape[0]

				# Make a container for them to go into
				container_id = uuid.uuid4().hex
				container_shape = shape_classes.ContainerShape(container_id)
				container_shape.children.append(label_shape)
				container_shape.children.append(labeled_shape)
				root.add_child(container_shape)
				shapes.append(container_shape)

				# Remove the entries from the dictionary
				root.remove_child(label_shape)
				root.remove_child(labeled_shape)

		grouped_elements = dict()
		for element in self.elements:
			if "group" in element:
				group_name = element["group"]
				if group_name in grouped_elements:
					grouped_elements[group_name].append(element)
				else:
					grouped_elements[group_name] = [element]

		group_metadata = dict()
		for group in self.groups: 
			if "name" in group: 
				group_metadata[group["name"]] = group

		for group_name,group_items in grouped_elements.items():
			group_id = uuid.uuid4().hex

			order = None
			if group_name in group_metadata: 
				group_metadata = group_metadata[group_name]
				if "order" in group_metadata: 
					order = group_metadata["order"]

			group_shape = shape_classes.ContainerShape(group_name, order=order)
			for element in group_items:
				element_name = element["name"]
				element_shape = [shp for shp in root.children if shp.shape_id == element_name][0]
				group_shape.add_child(element_shape)
				root.remove_child(element_shape)
			shapes.append(group_shape)
			root.add_child(group_shape)

		# Shapes left in the dictionary are at the root level
		return shapes, root

	# initialize domains
	def init_domains(self):
		for shape in self.shapes:
			# x_size = len(shape.x.domain)
			# y_size = len(shape.y.domain)
			self.solver.add(shape.x.z3 >= 0)
			self.solver.add((shape.x.z3 + shape.width) <= self.canvas_width)
			self.solver.add(shape.y.z3 >= 0)
			self.solver.add((shape.y.z3 + shape.height) <= self.canvas_height)

	def init_variables(self):
		last = []
		first = []
		variables = []
		last.append(self.canvas_shape.alignment)
		last.append(self.canvas_shape.justification)

		for child in self.root.children:
			if child.type == "container" and len(child.children):
				first.append(child.arrangement)
				last.append(child.alignment)
				last.append(child.proximity)

		first.append(self.root.arrangement)
		last.append(self.root.alignment)
		last.append(self.root.proximity)

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

	# def init_global_constraints():
	# 	# Stay in bounds of the canvas
	# 	for shape in self.shapes:
	# 		self.solver_helper.add_bounds_constraints(shape)

	def solve(self):
		self.unassigned = copy.copy(self.variables)

		start_time = time.time()
		self.branch_and_bound(start_time)
		end_time = time.time()
		print("number of solutions found: " + str(len(self.solutions)))
		print("number of invalid solutions: " + str(self.invalid_solutions))
		print("branches pruned: " + str(self.branches_pruned))
		print("Z3 time: " + str(self.time_z3))
		print("Z3 calls: " + str(self.z3_calls))
		print("Encoding time: " + str(self.time_encoding))
		print("Amount of time taken: " + str(end_time-start_time))

		if len(self.solutions):
			self.solutions.sort(key=lambda s: s["cost"])
			print("lowest cost: " + str(self.solutions[0]["cost"]))
			print("higest cost: " + str(self.solutions[len(self.solutions)-1]["cost"]))
		else:
			print("No solutions found.")
		return self.solutions

	def select_next_variable(self):
		# Select a random index to assign
		# random_index = random.randint(0, len(self.unassigned)-1)
		random_index = len(self.unassigned)-1
		return random_index, self.unassigned.pop(random_index)

	def restore_variable(self, variable, index):
		variable.assigned = None
		self.unassigned.insert(index, variable)

	def get_randomized_domain(self, variable):
		randomized_domain = variable.domain[0:len(variable.domain)]
		random.shuffle(randomized_domain)
		return randomized_domain

	def encode_assigned_variables(self):
		variable_equals_assigned = []
		for variable in self.variables:
			variable_equals_assigned.append(variable.z3 == variable.assigned)
		self.solver.add(And(variable_equals_assigned))

	def encode_assigned_variable(self, variable):
		time_encoding_start = time.time()
		if variable.name == "proximity":
			prox_value = variable.domain[variable.assigned]
			self.solver.add(variable.z3 == prox_value)
		else:
			self.solver.add(variable.z3 == variable.assigned)

		time_encoding_end = time.time()
		self.time_encoding += (time_encoding_end - time_encoding_start)

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
				sln = state.convert_to_json(self.elements, self.shapes, model)
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
			var_i, next_var = self.select_next_variable()
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

				unsat_core = self.solver.unsat_core()

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









