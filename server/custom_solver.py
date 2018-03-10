import jsonpickle
import copy
import uuid
from z3 import *
import z3_helper
import shapes as shape_classes
import solver_helpers as sh
import time
import random
# What will we be solving for? 

# Steps
# 1. Design constructs initial design sketch
# 2. Designer creates initial set of constraints with relationships 
# 3. Solve


# What are the constraints? 
# Related Groups
# Related Collections
# Labels
# Captions
# Headers --> maybe
# Footers --> maybe
# Global -> No overlapping, no out of bounds

# What can we change just with labels relationship? 
# Labels 
# 	E1/G1 labels E2/G2
#   Element or group 1 labels element or group 2
#   Positions of the label: Top-Left, Center, Top-Right, Left
# 	Proximity of the label: GLOBAL value --> we should get this from somewhere

# Elements - N elements 
# Variables: X, Y, Width, Height, Position of the label (top-left, center, top-right,  left)
# The canvas
# - The overall layout canvas is an element that has constraints on alignment (left, center, right)
# Variables: Alignment (l,c,r)
# Arrangement: Vertical 
# Order unimportant -- Need to generate all of the possible orders  


# What positions make sense? 
	# The element is aligned to other elements on the page 
	# Or aligned globally (Left, Center, Right) or vertical position 

# Just one element (no changing size)
# Variables: X, Y
# Canvas Variables: Alignment, Justification
# Alignment values: Left, Center, Right
# Justification values: Top, Bottom, Center 

# With the label
# Variables for label placement: Left, Top-Left, Top-center, top-right
# Variables for canvas: 
# - Alignment - left, center, right
# - Justification - top, center, bottom
# - Order - The relative order of the elements

# 05/08/2018
# Variables so far
# Groups with alignment, arrangment (2 axes)
# Canvas alignment, and justification 
# What is left: 
#   Proximity 
#   Emphasis
#   More arrangment types 
#   Order not important
#.  Other label placements
#.  Captions
# Needs implemented 
#.  - Concept list
#.  - Task group (?)
#.  - Group hiearchies
#.  - Snapping to edges
#.  - Locking 
#.  - absolute positioning
#.  - Cost function & optimization 
#   - Search random through search space 
#.  - eliminating duplicates (looks the same even if variable assignments are different)

# 05/092018
# - Encoding done after variable assignment and push/pop in the loop greatly lowers the encoding time. 
# - What to evaluate next? 
# 	- Larger amount of items
# - What just adds to the search space size vs slowing down the time to a single solution? 
#    - Proximity -- Adds additional variable (with X amount of values)
#.   - Emphasis -- Adds additional variables (Size, Distance from center)
#.   - More arrangements (patterns) - Adds more values to arrangment variables (bigger search space), ** should't increase runtime as much?
# 	 - Order not important - Effects arrangments - More constraints 
#.   - More label placements - Adds additional values to variables
#.   - Captions - Just a different kind of group 
# - What is most important to evaluate? 
#.  - Evaluating goodness of solutions
#.  - Random search through space
#.     - Can branch and bound do this or do we need something else? *** left to evaluate
#      - Could do random walk through the solution space (but how do we prevent generating same solutions if designer asks for more?)
#.  - Proximity/Global variables and effect on search space
#.  - Larger amount of items in UI (Can search rico to find one possibly) -- Need to test out w/ more elements & groups
#.  - Can we pause solving and restart? (only show first 100, then solve for the rest if the designer doesn't like them) --> should be doable by engineering
#.- Optimizations 
#.  - If all of the children elements have same width/height, it doens't make sense to explore the alignments for the group since they will all be the same

# Facebook benchmark time: 100 solutions - .38s solving, .66s encoding (all solutions), .83s to 100 solutions
# Questions to resolve
# Group that sizes to its content vs available spaace
# For groups that are sizing to their contents, alignment and justification dont' make sense
# Just restricting to the canvas for now, refactor later


# evaluating goodness
#  Metrics - Balance, Alignment, Whitespace
#.  - I believe alignments should not be relevant since we are only iteration aligned axes? 
#.  - Balance - evaluate how symmetrical the layout is 

# 05/10/2018 
# Things to evaluate:
#.  - Goodness metric & ordering solutions by quality 
#.  - What is the effect of allowing ordering to change? 
#.  - Larger amount of items 
#.  - Think about random search 



GRID_CONSTANT = 5
GLOBAL_PROXIMITY = 5
NUM_SOLUTIONS = 100

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
	def __init__(self, elements, canvas_width, canvas_height): 
		self.solutions = [] # Initialize the variables somewhere
		self.invalid_solutions = 0 # Used to keep track of the number of invalid solutions
		self.num_solutions = 0
		self.unassigned = []
		self.elements = elements
		self.canvas_width = canvas_width
		self.canvas_height = canvas_height
		self.shapes, self.root = self.init_shape_hierarchy(canvas_width, canvas_height)

		# Canvas contains all the elements as direct children for now
		self.canvas_shape = shape_classes.CanvasShape("canvas", canvas_width, canvas_height)	
		self.canvas_shape.add_child(self.root)
		self.variables = self.init_variables()

		# Construct the solver instance we will use for Z3
		self.solver = z3.Solver()
		self.solver_helper = z3_helper.Z3Helper(self.solver, canvas_width, canvas_height)
		self.init_domains()

		# For debugging how large the search space isd
		size = self.compute_search_space()
		print("Total search space size: " + str(size))

		# To Do : Move elswhere
		self.init_container_constraints(self.canvas_shape)
		for shape in self.shapes: 
			if shape.type == "container": 
				self.init_container_constraints(shape)

		# Timing variables to measure performance for various parts
		self.time_z3 = 0
		self.time_encoding = 0


	def init_shape_hierarchy(self, canvas_width, canvas_height): 
		shapes = []

		# Place all the elements directly on the canvas in a group that is sizing to contents 
		# This will make it easier to manipulate alignment/justification at the canvas level
		root_id = uuid.uuid4().hex
		root = shape_classes.ContainerShape("canvas_root")
		shapes.append(root)

		# Root will contain the root  level shapes (just below the canvas)
		for element in self.elements: 
			element_shape = shape_classes.Shape(element["name"], element["size"]["width"], element["size"]["height"])
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

		groups = dict()
		for element in self.elements: 
			if "group" in element:
				group_name = element["group"]
				if group_name in groups: 
					groups[group_name].append(element)
				else: 
					groups[group_name] = [element]

		for group_name,group_items in groups.items():
			group_id = uuid.uuid4().hex
			group_shape = shape_classes.ContainerShape(group_name)
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
		variables = []
		variables.append(self.canvas_shape.alignment)
		variables.append(self.canvas_shape.justification)

		for child in self.root.children:
			if child.type == "container" and len(child.children): 
				variables.append(child.arrangement)
				variables.append(child.alignment)
				variables.append(child.proximity)

		variables.append(self.root.arrangement)
		variables.append(self.root.alignment)
		variables.append(self.root.proximity)

		# Later: Justification and alignment 
		return variables

	def compute_search_space(self): 
		total = 1 
		for variable in self.variables:
			total *= len(variable.domain)
		return total 

	def get_max_width_constraint(self, child_i, widest_i, child_shapes): 
		if child_i < len(child_shapes): 
			widest_child = child_shapes[widest_i]
			next_child = child_shapes[child_i]
			return If(widest_child.width > next_child.width, self.get_max_width_constraint(child_i+1, widest_i, child_shapes), self.get_max_width_constraint(child_i+1, child_i, child_shapes))
		else: 
			return child_shapes[widest_i].width

	def get_max_height_constraint(self, child_i, tallest_i, child_shapes): 
		if child_i < len(child_shapes): 
			tallest_child = child_shapes[tallest_i]
			next_child = child_shapes[child_i]
			return If(tallest_child.height > next_child.height, self.get_max_height_constraint(child_i+1, tallest_i, child_shapes), self.get_max_height_constraint(child_i+1, child_i, child_shapes))
		else: 
			return child_shapes[tallest_i].height

	# Intialize constraints on the containers for arrangment, ordering, justification, and alignment
	def init_container_constraints(self, container): 

		child_shapes = container.children
		if len(child_shapes) > 0: 
			# Every child shape should remain inside of its parent container
			for s_index in range(0, len(child_shapes)): 
				shape1 = child_shapes[s_index]
				self.solver.add(shape1.x.z3 >= container.x.z3)
				self.solver.add(shape1.y.z3 >= container.y.z3)
				self.solver.add((shape1.x.z3 + shape1.width) <= (container.x.z3 + container.width))
				self.solver.add((shape1.y.z3 + shape1.height) <= (container.y.z3 + container.height))

			if container.type == "container": 
				# ====== Arrangement constraints =======
				v_index = container.arrangement.domain.index("vertical")
				is_vertical = container.arrangement.z3 == v_index

				vertical_pairs = []
				horizontal_pairs = []
				for s_index in range(0, len(child_shapes)-1): 
					shape1 = child_shapes[s_index]
					shape2 = child_shapes[s_index+1]
					vertical_pair_y = (shape1.y.z3 + shape1.height + container.proximity.z3) == shape2.y.z3 
					vertical_pairs.append(vertical_pair_y)
					horizontal_pair_x = (shape1.x.z3 + shape1.width + container.proximity.z3) == shape2.x.z3
					horizontal_pairs.append(horizontal_pair_x)

				vertical_arrange = And(vertical_pairs)
				horizontal_arrange = And(horizontal_pairs)
				# self.solver.assert_and_track(If(is_vertical, vertical_arrange, horizontal_arrange), "arrangment_constraint_" + container.shape_id)
				self.solver.add(If(is_vertical, vertical_arrange, horizontal_arrange))

				# Sum up the widths and heights
				child_widths = container.proximity.z3
				child_heights = container.proximity.z3
				for child in child_shapes: 
					child_widths += child.width + container.proximity.z3
					child_heights += child.height + container.proximity.z3

				# Set the width and height of the container based on the arrangement axis 
				# self.solver.assert_and_track(If(is_vertical, container.height == child_heights, container.width == child_widths), "height_constraint_" + container.shape_id)
				self.solver.add(If(is_vertical, container.height == child_heights, container.width == child_widths))

				m_w_constraint = container.width == self.get_max_width_constraint(1,0,child_shapes)
				m_h_constraint = container.height == self.get_max_height_constraint(1,0,child_shapes)
				# self.solver.assert_and_track(If(is_vertical, m_w_constraint, m_h_constraint), "max_height_constraint_" + container.shape_id)
				self.solver.add(If(is_vertical, m_w_constraint, m_h_constraint))

			# ======== Alignment & Justification ========
			# The X,Y positions of the canvas are not adjustable
			first_child = child_shapes[0]
			last_child = child_shapes[len(child_shapes)-1]
			l_index = container.alignment.domain.index("left")
			c_index = container.alignment.domain.index("center")
			is_left = container.alignment.z3 == l_index
			is_center = container.alignment.z3 == c_index

			if container.shape_id == "canvas": 
				self.solver.add(container.x.z3 == container.orig_x)
				self.solver.add(container.y.z3 == container.orig_y)

				# Canvas justification (because the canvas is the only type of container right now not sizing to its contents)
				t_index = container.justification.domain.index("top")
				c_index = container.justification.domain.index("center")
				is_top = container.justification.z3 == t_index
				is_center = container.justification.z3 == c_index
				top_justified = first_child.y.z3 == container.y.z3
				bottom_justified = (first_child.y.z3 + first_child.height) == (container.y.z3 + container.height)
				center_justified = (first_child.y.z3 + (first_child.height/2)) == (container.y.z3 + (container.height/2))
				self.solver.add(If(is_top, top_justified, If(is_center, center_justified, bottom_justified)))

				# Canvas aligment is different than other containers since there is no concept of arrangement
				l_index = container.alignment.domain.index("left")
				c_index = container.alignment.domain.index("center")
				is_left = container.alignment.z3 == l_index
				is_center = container.alignment.z3 == c_index
				left_aligned = first_child.x.z3 == container.x.z3
				center_aligned = (first_child.x.z3 + (first_child.width/2)) == (container.x.z3 + (container.width/2))
				right_aligned = (first_child.x.z3 + first_child.width) == (container.x.z3 + container.width)
				self.solver.add(If(is_left, left_aligned, If(is_center, center_aligned, right_aligned)))
			else: 
				for child in child_shapes:
					left_aligned = child.x.z3 == container.x.z3
					right_aligned = (child.x.z3 + child.width) == (container.x.z3 + container.width)
					h_center_aligned = (child.x.z3 + (child.width/2)) == (container.x.z3 + (container.width/2))
					top_aligned = child.y.z3 == container.y.z3
					bottom_aligned = (child.y.z3 + child.height) == (container.y.z3 + container.height)
					v_center_aligned = (child.y.z3 + (child.height/2)) == (container.y.z3 + (container.height/2))
					horizontal = If(is_left, top_aligned, If(is_center, v_center_aligned, bottom_aligned))
					vertical = If(is_left, left_aligned, If(is_center, h_center_aligned, right_aligned))
					# self.solver.assert_and_track(If(is_vertical, vertical, horizontal), "alignment_constraint_" + container.shape_id + "_" + child.shape_id)
					self.solver.add(If(is_vertical, vertical, horizontal))

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
		print("Z3 time: " + str(self.time_z3))
		print("Encoding time: " + str(self.time_encoding))
		print("Amount of time taken: " + str(end_time-start_time))
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
		for variable in self.variables: 
			print(variable.shape_id)
			print(str(variable.domain[variable.assigned]))

	def branch_and_bound(self, time_start, state=sh.Solution()): 
		# Dumb this down so we are not optimizing for the cost right now
		# State keeps track of the variables assigned so far
		# print("Found: " + str(self.num_solutions + self.invalid_solutions))
		if self.num_solutions == NUM_SOLUTIONS:
			return

		if len(self.unassigned) == 0: 
			# Ask the solver for a solution to the X,Y location varibles
			# constraints = self.solver.sexpr()
			time_z3_start = time.time()
			result = self.solver.check();
			time_z3_end = time.time() 
			time_z3_total = time_z3_end - time_z3_start
			self.time_z3 += time_z3_total
			# unsat_core = self.solver.unsat_core()

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
				# print("-----Invalid solution------")
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
				self.branch_and_bound(time_start, state)

				# Remove the stack context after the branch for this assignment has been explored
				self.solver.pop()

			# Then unassign the value
			self.restore_variable(next_var, var_i)
		return 

# if __name__ == "__main__":
# 	# with open('specification/with_labels.json') as data_file:
# 	#     shapes = json.load(data_file)
# 	# shapes = dict() 
# 	# child1 = Shape("child1", 50, 50)
# 	# shapes["child1"] = child1
# 	# canvas = Shape("canvas", 375, 667)
# 	# canvas.add_child(child1)
# 	# shapes["canvas"] = canvas

# 	# # Create some variables
# 	# var1 = Variable("canvas", "alignment", ["left", "right", "center"])
# 	# var2 = Variable("canvas", "justification", ["top", "bottom", "center"])
# 	# variables = []
# 	# variables.append(var1)
# 	# variables.append(var2)
# 	# solver = Solver(shapes)
# 	# solver.solve(variables)

# 	# for shape_key, shape in shapes.items(): 
# 	# 	print("-----------------")
# 	# 	print(shape.shape_id)
# 	# 	print(shape.x, shape.y, shape.width, shape.height)

# 	for sln in solver.solutions: 
# 		print(sln)









