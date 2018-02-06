import uuid 
from z3 import *
import z3_shapes as shapes # Change here to use Z3
import time
import z3_solver

# Global constraint variables
MAX_SOLUTIONS = 10
GROUP_PROXIMITY = 5
GLOBAL_PROXIMITY = 5

# The global grid along which elements are aligned
GRID_CONSTANT = 5



def contains(a_list, a_id): 
	try: 
		a_list.index(a_id)
		return True
	except ValueError as e: 
		return False

class LayoutProblem(object): 
	def __init__(self, width, height): # Width and height are the size of the containing box
		self.box_width = width
		self.box_height = height

		# Individual shapes
		self.shapes = None

		# Grouping containers for shapes
		self.groups = None

class LayoutSolver(object): 
	def __init__(self, problem):
		self.problem = problem
		self.shapes = self.problem.shapes
		self.groups = self.problem.groups

	@classmethod
	def init_problem(cls, elements, area_width, area_height, tags=None): 
		problem_shapes = dict()
		layout_problem = LayoutProblem(area_width, area_height)

		for shape in elements: 
			# shape_id = uuid.uuid4().hex
			shape_id = shape["name"]
			new_shape = shapes.BasicShape(str(shape_id), shape)
			problem_shapes[shape_id] = new_shape

		# Add container elements for each of the tag groups
		groups = dict() 
		print(problem_shapes)
		for shape_id, shape_obj in problem_shapes.items(): 
			if shape_obj.tag is not None: 
				if shape_obj.tag in groups: 
					groups[shape_obj.tag].append(shape_id)
				else: 
					groups[shape_obj.tag] = [shape_id]

		group_shapes = dict()
		for group_name, grouped_shape_ids in groups.items():
			group_json = None
			if tags is not None:
				for tag_group in tags:
					if "tag" in tag_group:
						tag_name = tag_group["tag"]
						if tag_name == group_name:
							group_json = tag_group
						
			# Add new group element
			group_shape = shapes.GroupShape(group_name, group_json)
			group_shape.children = grouped_shape_ids
			group_shapes[group_name] = group_shape

		layout_problem.shapes = problem_shapes
		layout_problem.groups = group_shapes
		return cls(layout_problem)

	def solve(self): 
		self.solver = z3_solver.Z3Solver(self.problem) # set the value of this above. Can be
		time_start = time.time()

		# Build the initial set of constraints
		self.add_global_constraints()
		self.add_designer_constraints()

		# Evaluate the results
		results = []

		##### Incremental backtracking to find solutions
		backtrack = False
		while self.solver.solutions_found < MAX_SOLUTIONS:
			print("Number of solutions: " + str(self.solver.solutions_found))
			if not backtrack:
				# Add constraints
				# self.solver.increment_cost_constraint()
				self.solver.add_constraint_from_solution()

				# Now solve for a new solution
				sln = self.solver.get_solution()
				if not sln:
					unsat_core = self.solver.unsat_core()
					backtrack = True
				else:
					new_solution = self.get_next_solution()
					results.append(new_solution)
					self.solver.increment_solutions()
			else:
				can_backtrack = self.solver.backtrack()
				if can_backtrack:
					sln = self.solver.get_solution()
					if sln:
						new_solution = self.get_next_solution()
						results.append(new_solution)
						self.solver.increment_solutions()
				else:
					break

		time_end = time.time() 
		print("Total time taken: " + str(time_end-time_start))
		return results


	def add_designer_constraints(self): 
		# Add single shape constraints 
		for shp_id, shp in self.shapes.items():
			if shp.tag is not None and shp.tag in self.groups:
				tag_group = self.groups[shp.tag]
				self.solver.helper.add_grouping_constraints(shp, tag_group)

			# Add effect constraints
			if shp.effect and shp.effect in self.shapes: 
				effect_shape = self.shapes[shp.effect]
				self.solver.helper.add_effect_constraint(shp, effect_shape)

			if shp.locked:
				self.solver.helper.add_locked_position_constraint(shp)

			if shp.importance: 
				self.solver.helper.add_importance_constraints(shp)
			else: 
				self.solver.helper.add_locked_size_constraint(shp)


	def add_global_constraints(self): 
		# Add cost constraints
		# all_shapes = list(self.shapes.values())
		# self.solver.helper.add_alignment_cost(all_shapes)

		# Each shape should stay in bounds and be aligned to the pixel grid
		for shp_id1, shp1 in self.shapes.items():
			self.solver.helper.add_grid_constraints(shp1)
			self.solver.helper.add_bounds_constraints(shp1)
			self.solver.helper.add_size_constraints(shp1)

			for shp_id2, shp2 in self.shapes.items(): 
				if shp_id1 != shp_id2:
					print(shp_id1, shp_id2)
					# Non-overlappping constraints
					self.solver.helper.add_non_overlapping_constraints(shp1, shp2)
					# self.solver.add_alignment_constraint(shape1, shape2)

		# Group containers should also have a stay in bounds constraint
		for grp_id, grp in self.groups.items():
			self.solver.helper.add_bounds_constraints(grp)

	def add_group_constraints(self): 
		for grp_id, grp in self.groups.items():
			# Add constraints to set the max/min width and height
			vertical_height = 0
			horizontal_width = 0
			horizontal_height = []
			vertical_width = []
			for child_id in grp.children:
				child = self.shapes[child_id]
				vertical_height += child.adjusted_height + GLOBAL_PROXIMITY
				horizontal_width += child.adjusted_width + GLOBAL_PROXIMITY

				grp_h_eq = grp.adjusted_height == (child.adjusted_height + 2*GLOBAL_PROXIMITY)
				horizontal_height.append(grp_h_eq)

				grp_w_eq = grp.adjusted_width == (child.adjusted_width + 2*GLOBAL_PROXIMITY)
				vertical_width.append(grp_w_eq)

			bottom_align = []
			left_align = []
			for c_index in range(0, len(grp.children)): 
				id1 = grp.children[c_index]
				child1 = self.shapes[id1]
				for c_index2 in range(0, len(grp.children)): 
					id2 = grp.children[c_index2]
					child2 = self.shapes[id2]
					if c_index != c_index2: 
						align_left = child1.adjusted_x == child2.adjusted_x
						left_align.append(align_left)

						align_bottom = child1.adjusted_y + child1.adjusted_height == child2.adjusted_y + child2.adjusted_height
						bottom_align.append(align_bottom)

			left_alignments = And(left_align)
			bottom_alignments = And(bottom_align)

			set_alignment = If(grp.arrangement, bottom_alignments, left_alignments)


			vertical_height += GLOBAL_PROXIMITY
			horizontal_width += GLOBAL_PROXIMITY

			horizontal_arrange = And(grp.adjusted_width == horizontal_width, Or(horizontal_height))
			vertical_arrange = And(grp.adjusted_height == vertical_height, Or(vertical_width))
			constrain_size = If(grp.arrangement, horizontal_arrange, vertical_arrange)

			## Eventually move this into the constraint helpers class 
			self.solver.add_group_constraints(grp, constrain_size, set_alignment)

				# Add constraint to set the child sizes to be adjustable if the group importance is set
				# if grp.importance:
				# 	child.importance = grp.importance
				# 	self.ch.add_importance_constraints(child)

	def get_next_solution(self): 
		json_shapes = self.solver.get_json_shapes()

		new_solution = dict() 
		new_solution["elements"] = json_shapes
		new_solution["id"] = uuid.uuid4().hex

		return new_solution





