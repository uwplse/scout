import uuid 
from z3 import *
import shapes
import copy
import math
import time
import constraint_helpers

# Global constraint variables
MAX_SOLUTIONS = 500
GROUP_PROXIMITY = 5
GLOBAL_PROXIMITY = 5

# The global grid along which elements are aligned
GRID_CONSTANT = 5

def abs(x):
	return If(x>=0,x,-x)

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
		self.solver = z3.Optimize()
		self.ch = constraint_helpers.ConstraintHelper(self.solver, self.problem)
		self.shapes = self.problem.shapes
		self.groups = self.problem.groups

		print("num shapes: " + str(len(self.shapes)))
		print("Box size: " + str(self.problem.box_width) + "," + str(self.problem.box_height))

		time_start = time.time() 

		# Add single shape constraints 
		for shp_id, shp in self.shapes.items():
			self.ch.add_grid_constraints(shp)
			self.ch.add_bounds_constraints(shp)
		
			if shp.tag is not None and shp.tag in self.shapes:
				tag_group = self.shapes[shp.tag]
				self.ch.add_grouping_constraints(shp, tag_group)

			# # Add effect constraints
			if shp.effect and shp.effect in self.shapes: 
				effect_shape = self.shapes[shp.effect]
				self.ch.add_effect_constraint(shp, effect_shape)

			if shp.locked: 
				self.ch.add_locked_position_constraint(shp)

			if shp.importance: 
				self.ch.add_importance_constraints(shp)
			else: 
				self.ch.add_locked_size_constraint(shp)

		for grp_id, grp in self.groups.items(): 
			# Add constraints to set the max/min width and height
			min_width = 0
			min_height = 0
			max_height = 0
			max_width = 0
			for child_id in grp.children:
				child = self.shapes[child_id]
				max_height += child.adjusted_height + GLOBAL_PROXIMITY
				max_width += child.adjusted_width + GLOBAL_PROXIMITY

				# Add constraint to set the child sizes to be adjustable if the group importance is set
				if grp.importance: 
					child.importance = grp.importance
					self.ch.add_importance_constraints(child)

			self.ch.add_min_size_constraints(grp, min_width, min_height)
			self.ch.add_max_size_constraints(grp, max_width, max_height)

		# For each pair of shapes add non-overlapping constraints 
		all_shapes = list(self.shapes.values())
		for i in range(0, len(all_shapes)): 
			for j in range(0, len(all_shapes)): 
				if i != j: 
					shape1 = all_shapes[i]
					shape2 = all_shapes[j]

					# Non-overlappping constraints
					self.ch.add_proximity_constraints(shape1, shape2)
		
		# Evaluate the results
		solutions_found = 0
		results = []
		curr_model = None
		while solutions_found < MAX_SOLUTIONS: 
			if solutions_found > 0: 
				# Add constraints
				self.add_solution_to_constraints(curr_model)

			# Now solve for a new solution
			model = self.solve_and_check_solution()
			if model is None: 
				# When no results returned, stop solving for new solutions
				break	
			else: 
				json_shapes = self.translate_model_to_shapes(model)

				new_canvas = dict() 
				new_canvas["elements"] = json_shapes
				new_canvas["id"] = uuid.uuid4().hex
				results.append(new_canvas)

				solutions_found+=1
				print("Number of solutions: " + str(solutions_found))
				curr_model = model

		time_end = time.time() 
		print("Total time taken: " + str(time_end-time_start))
		print("Number of solutions: " + str(solutions_found))
				
		return results

	def solve_and_check_solution(self): 
		print("Looking for a solution.")
		# Pass in the cost function
		curr_shapes = list(self.shapes.values())
		# object_fun = self.solver.minimize(self.ch.maximize_alignments(curr_shapes))
		result = self.solver.check(); 
		if str(result) == 'sat': 
			# Find one solution for now
			model = self.solver.model()

			# print(model)
			# # shapes = self.translate_model_to_shapes(model, shapes)
			# print("-------Statistics-------")
			# #print self.solver.statistics()

			# Keep the solution to add to the set of constraints
			return model
		else: 
			print("No solution found :(")

	def translate_model_to_shapes(self, model): 
		# Convert the produced values back to the format of shapes to be drawn
		final_shapes_json = []
		for shape_id, shape in self.shapes.items(): 
			final_x = shape.adjusted_x
			final_y = shape.adjusted_y
			final_width = shape.adjusted_width
			final_height = shape.adjusted_height

			f_x = model[final_x]
			f_y = model[final_y]
			f_width = model[final_width]
			f_height = model[final_height]

			adj_x = f_x.as_string()
			adj_y = f_y.as_string()
			adj_width = f_width.as_string()
			adj_height = f_height.as_string()

			adj_x = int(adj_x)
			adj_y = int(adj_y)
			adj_width = int(adj_width)
			adj_height = int(adj_height)

			# TOODO later figure out why necessary or do something more efficient
			json_shape = copy.deepcopy(shape.json_shape)
			json_shape["location"]["x"] = adj_x
			json_shape["location"]["y"] = adj_y
			json_shape["size"]["width"] = adj_width
			json_shape["size"]["height"] = adj_height

			final_shapes_json.append(json_shape)

		return final_shapes_json
	
	def add_solution_to_constraints(self, model): 
		constraints = []
		for shape_id, shape in self.shapes.items():
			final_x = shape.adjusted_x
			final_y = shape.adjusted_y

			f_x = model[final_x]
			f_y = model[final_y]
			adj_x = f_x.as_string()
			adj_y = f_y.as_string()

			adj_x = int(adj_x)
			adj_y = int(adj_y)

			x_not_same = shape.adjusted_x != adj_x
			y_not_same = shape.adjusted_y != adj_y
			constraints.append(x_not_same)
			constraints.append(y_not_same)

			# Width and height can change but may be equal to original so only add these if width/height are adjustable
			if shape.size_adjustable: 
				final_width = shape.adjusted_width
				final_height = shape.adjusted_height
				f_width = model[final_width]
				f_height = model[final_height]
				adj_width = f_width.as_string()
				adj_height = f_height.as_string()
				adj_width = int(adj_width)
				adj_height = int(adj_height)
				width_not_same = shape.adjusted_width != adj_width
				height_not_same = shape.adjusted_height != adj_height
				constraints.append(width_not_same)
				constraints.append(height_not_same)

		if len(constraints):
			self.solver.add(Or(constraints))

