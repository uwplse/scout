# Main class for generating a layout with branch  and bound algorithms
# building constraints, and calling into the solver. Also responsible for 
# repairing solutions that are invalid by relaxing one or more property values. 
from z3 import *
import time
import sys
import json
import random
import constraint_builder
import domain_reducer as dr
import shapes as shape_classes
import smtlib_builder as smt
import override_solver
import solution as sln
import logging
import numpy as np
import uuid
import size_domains as sizes
from size_domains import LAYOUT_GRID_PROPERTIES, SIZE_PROPERTIES, BASELINE_GRIDS
z3.set_param(
         'smt.arith.random_initial_value', True,
         'smt.random_seed', np.random.randint(0, 655350),
         'sat.phase', 'random',
         'sat.random_seed', np.random.randint(0, 655350))
logging.basicConfig(level=logging.DEBUG)

RANDOM_SEEDS=100000
CANVAS_WIDTH = 360
REPAIR_TRIES = 2

# These constaints help us decide which variables to relax when we are reparing for a 
# given variable conflicts. 
# this process could likely be simplified by relaxing only those that are in conflict in the 
# unsat core, but we didn't do that for this iteration. 
RELAX_PROPERTIES = {
	"arrangement": [["x", "y", "width", "height", "left_column", "right_column"], ["padding"]],
	"padding": [["x", "y", "width", "height", "left_column", "right_column"], ["arrangement"]],
	"alignment": [],
	"group_alignment": [], 
	"width": [["x", "height", "size_factor"], ["arrangement"], ["padding"]],
	"height": [["y", "width", "size_factor"], ["arrangement"], ["padding"]], 
	"y": [["height", "width", "size_factor"], ["arrangement"], ["padding"]], 
	"x": [["height", "width", "size_factor"], ["arrangement"], ["padding"]], 
	"left_column": [["x", "y"], ["size_combo"], ["arrangement"], ["padding"]], 
	"right_column": [["x", "y"], ["size_combo"], ["arrangement"], ["padding"]], 
	"canvas_alignment": [["x", "y"], ["size_combo"], ["arrangement"], ["padding"]], 
	"baseline_grid": [], 
	"margin": [["grid_layout"]], 
	"columns": [["grid_layout"]], 
	"column_width": [["grid_layout"]], 
	"gutter_width": [["grid_layout"]]
}

CHILDREN_RELAX_PROPERTIES = {
	"arrangement": [["x", "y"], ["size_combo"], ["padding", "arrangement"]], 
	"padding": [["x", "y"], ["size_combo"], ["padding", "arrangement"]],
	"left_column": [["x", "y"], ["size_combo"], ["padding", "arrangement"]],
	"right_column": [["x", "y"], ["size_combo"], ["padding", "arrangement"]],
	"canvas_alignment": [["x", "y"], ["size_combo"], ["padding", "arrangement"]],
	"alignment": [["x", "y"]],
	"group_alignment": [["x", "y"]], 
	"height": [["size_combo"]],
	"width": [["size_combo"]], 
	"x": [["x", "y"]], 
	"y": [["x", "y"]], 
	"baseline_grid": [["y", "left_column", "right_column"], ["size_factor"], ["x"], 
		["arrangement", "padding"]], 
	"margin": [["y", "x", "left_column", "right_column", "size_combo", "padding", "arrangement"]],
	"columns": [["x", "left_column", "y", "right_column"], ["size_combo"], ["padding", "arrangement"]], 
	"column_width": [["x", "left_column", "right_column"], ["size_combo"], ["y"], ["padding", "arrangement"]], 
	"gutter_width": [["x", "left_column", "right_column"], ["size_combo"], ["y"], ["padding", "arrangement"]]
}

CANVAS_RELAX_PROPERTIES = {
	"padding": [["grid_layout"], ["baseline_grid"]], 
	"arrangement": [["grid_layout"], ["baseline_grid"]], 
	"alignment": [["baseline_grid"], ["grid_layout"]],
	"group_alignment": [["baseline_grid"], ["grid_layout"]],
	"y": [["grid_layout"], ["baseline_grid"]], 
	"left_column": [["grid_layout"]],
	"right_column": [["grid_layout"]],
	"column_width": [["grid_layout"], ["baseline_grid"]], 
	"canvas_alignment": [["grid_layout"], ["baseline_grid"]], 
	"gutter_width": [["grid_layout"], ["baseline_grid"]], 
	"margin": [["grid_layout", "baseline_grid"]], 
	"height": [["baseline_grid"], ["grid_layout"]], 
	"width": [["grid_layout"], ["baseline_grid"]]
}


class Solver(object): 
	def __init__(self, solver_ctx, elements, solutions=[], relative_designs=None, prune_domains=True):
		# Construct the solver instance we will use for Z3
		self.solver_ctx = solver_ctx
		self.solver = z3.Solver(ctx=self.solver_ctx)
		self.solver.set(unsat_core=True)
		self.solutions = [] # Initialize the variables somewhere
		self.unassigned = []
		self.elements = elements
		self.previous_solutions = solutions
		self.relative_search = False
		self.prune_domains = prune_domains # Determines whether the domains have obviously invalid values removed
		self.shapes, self.root = self.build_shape_hierarchy()
		self.root = self.root[0]
		self.invalid_solutions = 0
		self.domain_reducer = dr.DomainReducer(self.shapes)

		if prune_domains: 
			self.domain_reducer.prune_size_variable_domains_for_locks()
			self.domain_reducer.prune_layout_grid_domains()
			self.domain_reducer.prune_size_domains()

		self.output_variables = self.init_output_variables()
		self.variables_different = Int('VariablesDifferent')


		self.override_solver = override_solver.OverrideSolver(self.solver)
		self.cb = constraint_builder.ConstraintBuilder(self.override_solver)

		# Build the initial set of constraints on the shapes and containers 
		time_start = time.time()

		self.cb.declare_variables(self.shapes)
		self.init_constraints()
		time_end = time.time()
		logging.debug("Time to create constraints (init_constraints): " + str(time_end-time_start))

		# Initialize variables
		self.variables = self.init_variables()

		# Intialize the locked constraints (Keep/Prevent values)
		start_time = time.time()
		for shape in self.shapes.values(): 
			self.cb.init_locks(shape)
			self.cb.init_prevents(shape)
		end_time = time.time()
		logging.debug("Time taken to encode locks: " + str(end_time-start_time))
			
		# Initialize the constraints preventing previous solutions from re-occuring
		start_time = time.time()

		# Prevent the previous solutions that have the same set of elements
		solutions_to_prevent = self.get_previous_solutions_to_prevent()
		self.cb.init_previous_solution_constraints(solutions_to_prevent, self.shapes)
		end_time = time.time()
		logging.debug("Time taken to encode previous solutions: " + str(end_time-start_time))

		self.unassigned = copy.copy(self.variables)

		time_start = time.time()
		self.cb.load_constraints()
		time_end = time.time()
		logging.debug("Time to parse constraints: "  + str(time_end-time_start))

		sys.stdout.flush()


		total = self.compute_search_space()
		logging.debug("Size of search space: "  + str(total))

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
			elements = solution["elements"]
			shapes_added, shapes_removed = self.check_added_or_removed_shapes(elements)
			if not len(shapes_added) and not len(shapes_removed): 
				solutions_to_prevent.append(solution)
		return solutions_to_prevent

	def init_constraints(self):
		# Initialize the set of constraints on shapes and containers
		canvas = None
		canvas = self.shapes['canvas'] 
		self.cb.init_canvas_constraints(canvas)

		for shape in self.shapes.values(): 
			if shape.type == "container": 
				self.cb.init_container_constraints(shape, self.shapes, canvas)

		for shape in self.shapes.values():
			if shape.type == "leaf":
				self.cb.init_shape_bounds(shape)
				self.cb.init_shape_baseline(shape)
				self.cb.init_shape_alternate(shape)

		for shape in self.shapes.values(): 
			if shape.importance: 
				if shape.importance == "high": 
					self.cb.init_high_emphasis(shape, self.shapes.values())
				if shape.importance == "low":
					self.cb.init_low_emphasis(shape, self.shapes.values())

	def build_shape_hierarchy(self): 
		shapes = dict()
		root = self.construct_shape_hierarchy([self.elements], shapes)
		return shapes,root

	def construct_shape_hierarchy(self, elements, shapes, parent_emphasis="normal", at_root=False, selected_grid=[], selected_baseline_grid=[]):
		# Build the shape hierarchy from the JSON collection 
		shape_hierarchy = []
		for i in range(0, len(elements)): 
			element = elements[i]
			element_type = element["type"]

			# If parent node emphasis is set, cascade that value to the child elements
			element_emphasis = element["importance"] if "importance" in element else "normal"
			if parent_emphasis != "normal": 
				element["importance"] = parent_emphasis
				element_emphasis = parent_emphasis

			sub_hierarchy = None

			is_alternate = False
			if "alternate" in element and element["alternate"]: 
				is_alternate = True

			shape_object = None
			if element_type == "canvas": 
				selected_grid = sizes.get_layout_grids()
				selected_baseline_grid = BASELINE_GRIDS
				if self.prune_domains: 
					selected_grid = sizes.select_consistent_layout_grid(elements[0])
					selected_baseline_grid = sizes.select_consistent_baseline_grid(elements[0])
				shape_object = shape_classes.CanvasShape(self.solver_ctx,
					element["name"], element, selected_grid, selected_baseline_grid)
				shapes[shape_object.shape_id] = shape_object
			elif element_type == "group" and not is_alternate:
				shape_object = shape_classes.ContainerShape(self.solver_ctx, 
					element["name"], element, selected_grid, selected_baseline_grid, at_root=at_root)
				shapes[shape_object.shape_id] = shape_object
			else:
				shape_object = shape_classes.LeafShape(self.solver_ctx,
					element["name"], element, selected_grid, selected_baseline_grid, at_root=at_root)
				shapes[shape_object.shape_id] = shape_object

			is_at_root = True if element_type == "canvas" else False
			if "children" in element and not is_alternate: 
				children = element["children"]
				sub_hierarchy = self.construct_shape_hierarchy(children, shapes, parent_emphasis=element_emphasis, at_root=is_at_root, 
					selected_grid=selected_grid, selected_baseline_grid=selected_baseline_grid)

			if sub_hierarchy is not None: 
				shape_object.add_children(sub_hierarchy)

			shape_hierarchy.append(shape_object)

		return shape_hierarchy


	def init_variables(self):
		""" Initializes the list of variables to search in a specific order to make the search go faster """
		last = []
		first = []
		variables = []

		for shape in self.shapes.values():
			variables_to_search = shape.search_variables
			keys = [var.name for var in variables_to_search]
			filtered_keys = []

			if shape.locks is not None:
				for lock in shape.locks:
					locked_values = shape.keep_values[lock]
					if lock in keys:
						if len(locked_values) > 1: 
							# Prune the variable domain but still assign it
							variable = shape.variables[lock]
							domain_values = variable.domain 
							pruned_domain_values = locked_values
							variable.domain = pruned_domain_values
						else: 
							lock_index = keys.index(lock)
							filtered_keys.append(lock_index)
					elif lock in SIZE_PROPERTIES:						
						if "size_combo" in keys:
							locked_index = SIZE_PROPERTIES.index(lock)
							size_combo_domain = shape.variables["size_combo"].domain
							if len(size_combo_domain) <= 1:
								size_combo_var_index = keys.index("size_combo")
								filtered_keys.append(size_combo_var_index)

			if shape.prevents is not None: 
				for prevent in shape.prevents: 
					prevented_values = shape.prevent_values[prevent]

					if prevent in LAYOUT_GRID_PROPERTIES:
						prev_index = LAYOUT_GRID_PROPERTIES.index(prevent)

						grid_domain = shape.variables["grid_layout"].domain
						pruned_grid_layout = [val for val in grid_domain if val[prev_index] not in prevented_values]
						if len(pruned_grid_layout) > 1: 
							shape.variables["grid_layout"].domain = pruned_grid_layout

							marg_domain = [val[0] for val in pruned_grid_layout]
							shape.variables["margin"].domain = marg_domain

							cols_domain = [val[1] for val in pruned_grid_layout]
							shape.variables["columns"].domain = cols_domain

							gutter_width_domain = [val[2] for val in pruned_grid_layout]
							shape.variables["gutter_width"].domain = gutter_width_domain

							col_width_domain = [val[3] for val in pruned_grid_layout]
							shape.variables["column_width"].domain = col_width_domain
						else: 
							grid_layout_var_index = keys.index("grid_layout")
							filtered_keys.append(grid_layout_var_index)

					elif prevent in SIZE_PROPERTIES:
						prev_index = SIZE_PROPERTIES.index(prevent)
						size_combo_domain = shape.variables["size_combo"].domain
						if len(size_combo_domain) <= 1: 
							size_var_index = keys.index("size_combo")
							filtered_keys.append(size_var_index)
					else: 
						# Prune these values form the variables domain 
						variable = shape.variables[prevent]
						domain_values = variable.domain
						pruned_domain_values = [val for val in domain_values if val not in prevented_values]
						variable.domain = pruned_domain_values
						if len(variable.domain) <= 1: 
							prevent_index = keys.index(prevent)
							filtered_keys.append(prevent_index)

			# Remove filtered key indexes
			filtered_keys = list(set(filtered_keys)) #Ensure Unique
			keys = [k for i,k in enumerate(keys) if i not in filtered_keys]

			vars_to_search = [var for var in variables_to_search if var.name in keys]
			variables.extend(vars_to_search)

		# Later: Justification and alignment
		return variables

	def compute_search_space(self):
		# Compute the size of the search space. 
		total = 1
		for variable in self.variables:
			total *= len(variable.domain)
		return total	

	def init_output_variables(self):
		# Output variables are the x,y position of all leaf-node shapes. 
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
		# Pop the next variable off the stack to assign it 
		return self.unassigned.pop()

	def select_next_variable_random(self): 
		# Select a random index to assign
		random_index = random.randint(0, len(self.unassigned)-1)
		return random_index, self.unassigned.pop(random_index)

	def restore_variable(self, variable, index):
		# Reset a variable back to the unassigned state. 
		variable.assigned = None
		self.unassigned.insert(index, variable)

	def get_randomized_domain(self, variable):
		# Randomize the order of the domain for a given variable. 
		randomized_domain = variable.domain[0:len(variable.domain)]
		random.shuffle(randomized_domain)
		return randomized_domain

	def encode_assigned_variable(self, variable):
		""" Used by the search loops to create constraints to encode
		 an equality constraint for a variable value to the value it has been assigned by the search """
		constraints = smt.declare(variable.id, variable.type)
		if variable.name == "grid_layout":
			assigned_value = variable.domain[variable.assigned]

			marg_var = self.shapes[variable.shape_id].variables.margin
			constraints += smt.declare(marg_var.id, marg_var.type)
			marg = smt.eq(marg_var.id, str(assigned_value[0]))

			cols_var = self.shapes[variable.shape_id].variables.columns
			constraints += smt.declare(cols_var.id, cols_var.type)
			cols = smt.eq(cols_var.id, str(assigned_value[1]))

			gutter_width_var = self.shapes[variable.shape_id].variables.gutter_width
			constraints += smt.declare(gutter_width_var.id, gutter_width_var.type)
			gutter_width = smt.eq(gutter_width_var.id, str(assigned_value[2]))
			
			col_width_var = self.shapes[variable.shape_id].variables.column_width
			constraints += smt.declare(col_width_var.id, col_width_var.type)
			col_width = smt.eq(col_width_var.id, str(assigned_value[3]))
			and_expr = smt.and_expr([marg, cols, gutter_width, col_width])
			constraints += smt.assert_expr(and_expr, 
				"variable_" + variable.id + "_assigned_to_" + str(variable.assigned))
			self.override_solver.load_constraints(constraints)

		elif variable.name == "size_combo":
			assigned_value = variable.domain[variable.assigned]
			width_var = self.shapes[variable.shape_id].variables.width 
			constraints += smt.declare(width_var.id, width_var.type)
			width = smt.eq(width_var.id, str(assigned_value[0]))

			height_var = self.shapes[variable.shape_id].variables.height
			constraints += smt.declare(height_var.id, height_var.type)
			height = smt.eq(height_var.id, str(assigned_value[1]))

			size_factor = self.shapes[variable.shape_id].variables.size_factor
			constraints += smt.declare(size_factor.id, size_factor.type)
			size_fact = smt.eq(size_factor.id, str(assigned_value[2]))

			and_expr = smt.and_expr([width, height, size_fact])

			constraints += smt.assert_expr(and_expr, 
				"variable_" + variable.id + "_assigned_to_" + str(variable.assigned))
			self.override_solver.load_constraints(constraints)

		elif variable.index_domain:
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
		variables = solution.parse_variables_from_model(model)
		
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

	# Computes the number of variables that are different than the previous solution
	def num_variables_different(self):
		vars_diff = 0
		for var_i in range(0, len(self.variables)): 
			variable = self.variables[var_i]
			vars_diff += If(variable.z3 != self.previous_solution[var_i], 1, 0)
		return vars_diff

	def z3_solve(self): 
		# Solve for solutions only using Z3, rather than the branch and bound (experimental)
		solutions = []
		num_solutions = 1
		slns_found = 0
		while slns_found < num_solutions: 
			self.solver.push()

			result = self.solver.check()
			if str(result) == 'sat':
				solution = sln.Solution()
				model = self.solver.model()
				json_sln = solution.convert_to_json(self.root, model)
				solutions.append(json_sln)

				self.encode_previous_solution_from_model(model, json_sln['id'])

			slns_found += 1
		return solutions

	def branch_and_bound(self, state):
		# Main solving loop to find a valid solution 
		if len(self.unassigned) == 0:
			time_z3_start = time.time()
			result = self.solver.check()
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
				sln = state.convert_to_json(self.root, model)
				time_end = time.time()
				logging.debug("Time in converting solution to json: " + str(time_end-time_start))
				self.restore_state()

				# Encode the previous solution outputs into the model so we don't produce it again in the next iteration
				# self.encode_previous_solution_from_model(model, sln["id"])
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
		# Checks the result of the current set of constraints with
		result = self.solver.check()
		if str(result) == 'sat': 
			return True
		else: 
			return False

	def get_element_names(self, element_tree, element_names=[]):
		"""Get a list of all the names of elements in the tree hierarchy"""
		element_names.append(element_tree['name'])

		if 'children' in element_tree: 
			for child in element_tree['children']: 
				self.get_element_names(child, element_names)

	def check_added_or_removed_shapes(self, elements): 
		# Look for shapes that were added or removed in this solution from the c
		# Current set of shapes in the hierarchy. In that case, we dont' need to check validity 

		shapes_added = []
		shapes_removed = []

		element_ids = []
		self.get_element_names(elements, element_ids)

		for element_id in element_ids:
			if element_id not in self.shapes:
				shapes_removed.append(element_id)

		for shape_id in self.shapes:
			shape = self.shapes[shape_id]
			if shape_id not in element_ids and (shape.type != "container" or len(shape.children)):
				shapes_added.append(shape_id)

		return shapes_added, shapes_removed


	def get_parent_node(self, element_tree, element_id): 
		# Find the elements parent node in the tree
		if "children" in element_tree: 
			for child in element_tree["children"]: 
				if child["name"] == element_id: 
					return element_tree
				parent = self.get_parent_node(child, element_id)
				if parent: 
					return parent 

	def get_corresponding_items(self, element_tree, element_id): 
		parent = self.get_parent_node(element_tree, element_id)
		items = []
		for child in parent["children"]: 
			if child["item"] and child["name"] != element_id: 
				items.append(child)
		return items

	def relax_item_properties(self, element_tree, elements, changed_element_id, changed_property, relaxed_property_values): 
		# Find the corresponding items in the parent container 
		items = self.get_corresponding_items(element_tree, changed_element_id)
		for item in items:
			relaxed_property_values[item["name"]] = dict()
			relaxed_property_values[item["name"]][changed_property] = item[changed_property]
			self.relax_element_properties(elements, item["name"], changed_property, relaxed_property_values)

	def relax_child_properties(self, elements, element_id, changed_property, relaxed_property_values):
		# Relax child properties 
		element_shape = self.shapes[element_id]
		if hasattr(element_shape, 'children') and len(element_shape.children):
			for child in element_shape.children:
				solution_element = elements[child.shape_id]
				child_properties_to_relax = CHILDREN_RELAX_PROPERTIES[changed_property]

				if child.shape_id not in relaxed_property_values: 
					relaxed_property_values[child.shape_id] = dict()
	
				for i in range(0, len(child_properties_to_relax)): 
					property_group_to_relax = child_properties_to_relax[i]
					for property_to_relax in property_group_to_relax: 
						if property_to_relax in solution_element and property_to_relax not in relaxed_property_values[child.shape_id]:
							relaxed_property_values[child.shape_id][property_to_relax] = solution_element[property_to_relax]

			for child in element_shape.children: 
				self.relax_child_properties(elements, child.shape_id, changed_property, relaxed_property_values)

	def get_elements_dict(self, element_tree, elements): 
		"""Build a dictionary of the elements in the hierarchy for accessing elements directly"""
		elements[element_tree["name"]] = element_tree 

		if "children" in element_tree and len(element_tree["children"]): 
			for child in element_tree["children"]: 
				self.get_elements_dict(child, elements)

	def repair_solution(self, solution, changed_element_id, changed_property, changed_value, keep_or_prevent): 
		"""Repair loop for relaxing properties in order to make a solution consistent """ 
		relaxed_property_values = dict() 
		relaxed_property_values[changed_element_id] = dict()
		relaxed_property_values[changed_element_id][changed_property] = changed_value

		elements = dict() 
		element_tree = solution["elements"]
		self.get_elements_dict(element_tree, elements)

		repaired_solution = None
		more_variables_to_relax = True
		print("Begin repair")
		repair_tries = 0 
		while repair_tries < REPAIR_TRIES and repaired_solution is None: 
			# Remove variables from unassigned that should be assigned
			if repair_tries == 0: 
				self.relax_element_properties(elements, changed_element_id, changed_property, relaxed_property_values)
			else: 
				self.relax_canvas_properties(elements, changed_element_id, changed_property, relaxed_property_values)

			print(relaxed_property_values)

			if "item" in elements[changed_element_id] and elements[changed_element_id]["item"]: 
				self.relax_item_properties(element_tree, elements, changed_element_id, changed_property, relaxed_property_values)

			variables_unassigned = []
			variables_assigned = []
			for variable in self.unassigned: 
				if variable.shape_id in relaxed_property_values and variable.name in relaxed_property_values[variable.shape_id]: 
					variables_unassigned.append(variable)
				else: 
					variables_assigned.append(variable)

			self.unassigned = variables_unassigned
			state = sln.Solution()

			for assigned_variable in variables_assigned: 
				self.solver.push()
				state.add_assigned_variable(assigned_variable)
				
				value_to_assign = changed_value
				
				if assigned_variable.shape_id == changed_element_id and assigned_variable.name == changed_property: 
					value_to_assign = changed_value
				else: 
					if assigned_variable.name == "size_combo":
						domain_value = elements[assigned_variable.shape_id]["size_combo"]
						value_index = [i for i in range(0, len(assigned_variable.domain)) if assigned_variable.domain[i][0] == domain_value[0] and assigned_variable.domain[i][1] == domain_value[1]]
						value_to_assign = value_index[0]
					elif assigned_variable.name == "grid_layout":
						domain_value = elements[assigned_variable.shape_id]["grid_layout"]
						value_to_assign = assigned_variable.domain.index(domain_value)
					else: 
						value_to_assign = elements[assigned_variable.shape_id][assigned_variable.name]

				if assigned_variable.index_domain: 
					assigned_variable.assigned = value_to_assign
				else: 
					if assigned_variable.type != "String": 
						value_to_assign = int(value_to_assign)

					in_domain_index = assigned_variable.domain.index(value_to_assign)
					assigned_variable.assigned = in_domain_index
				self.encode_assigned_variable(assigned_variable)

			# Try to find a repaired soluition
			repaired_solution = self.branch_and_bound(state)

			if repaired_solution is None: 
				for variable in self.variables: 
					variable.assigned = None
		
				self.unassigned = copy.copy(self.variables)

				# Restore the stack context for the solver
				for i in range(0, len(variables_assigned)):
					self.solver.pop()

			repair_tries += 1

		if repaired_solution:
			print("Able to repair this solution. ")
			repaired_solution["id"] = uuid.uuid4().hex
			solution = repaired_solution
			solution["conflicts"] = []
			solution["valid"] = True
			solution["new"] = True
			return solution

		return None


	def restore_relaxed_properties(self, solution, element_id, relaxed_property_values): 
		""" Reset the properties that were relaxed back to their original values """
		solution_element = solution["elements"][element_id]
		relaxed_values = relaxed_property_values[element_id]
		for key,relaxed_value in relaxed_values.items(): 
			solution_element[key] = relaxed_value

		# Restore child prperty values
		self.restore_child_relaxed_properties(solution, element_id, relaxed_property_values)

	def restore_child_relaxed_properties(self, solution, element_id, relaxed_property_values): 
		""" Restore the values that were originally relaxed back to their original values """
		element_shape = self.shapes[element_id]
		if hasattr(element_shape, 'children') and len(element_shape.children):
			for child in element_shape.children: 
				solution_element = solution["elements"][child.shape_id]

				relaxed_values = relaxed_property_values[child.shape_id]
				for key,relaxed_value in relaxed_values.items(): 
					solution_element[key] = relaxed_value
			self.restore_child_relaxed_properties(solution, child.shape_id, relaxed_property_values)

	def relax_element_properties(self, elements, changed_element_id, changed_property, relaxed_property_values):
		""" Remove assignments for a given list of properties to relax in order to repair the solution. """ 
		element = elements[changed_element_id]
		properties_to_relax = RELAX_PROPERTIES[changed_property]
		for i in range(0, len(properties_to_relax)): 
			property_group_to_relax = properties_to_relax[i]
			for property_to_relax in property_group_to_relax: 
				if property_to_relax in element and property_to_relax not in relaxed_property_values[changed_element_id]: 
					relaxed_property_values[changed_element_id][property_to_relax] = element[property_to_relax]
		self.relax_child_properties(elements, changed_element_id, changed_property, relaxed_property_values)

	def relax_canvas_properties(self, elements, changed_element_id, changed_property, relaxed_property_values):
		""" Remove assignments for canvas properties in order to repair the solution """
		canvas_element = elements["canvas"]
		canvas_properties_to_relax = CANVAS_RELAX_PROPERTIES[changed_property]
		if "canvas" not in relaxed_property_values: 
			relaxed_property_values["canvas"] = dict()

		for i in range(0, len(canvas_properties_to_relax)): 
			canvas_property_group_to_relax = canvas_properties_to_relax[i]
			for canvas_property_to_relax in canvas_property_group_to_relax: 
				if canvas_property_to_relax not in relaxed_property_values["canvas"]: 
					relaxed_property_values["canvas"][canvas_property_to_relax] = canvas_element[canvas_property_to_relax]

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
				print("Solution could not be found.")

		return solution

	def print_solution(self):
		# Helper to print out the current solution
		print("------------Solution------------")
		for variable in self.variables:
			print(variable.shape_id)
			print(str(variable.domain[variable.assigned]))

	def print_partial_solution(self):
		# Helper to print out a partial solution. 
		for variable in self.variables:
			if variable.assigned is not None:
				print(variable.shape_id)
				print(str(variable.domain[variable.assigned]))
