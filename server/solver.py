import uuid 
from z3 import *
import shapes
import copy

MAX_SOLUTIONS = 20

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

	@property 
	def box_width(self): 
		return self.box_width

	def box_width(self, width): 
		self.__box_width = width

	@property 
	def box_height(self): 
		return self.box_height

	def box_height(self, height): 
		self.__box_height = height

	@property 
	def shapes(self): 
		return self.shapes

	def shapes(self, shapes): 
		self.__shapes = shapes

class LayoutSolver(object): 
	def __init__(self, problem):
		self.problem = problem

	@classmethod
	def init_problem(cls, elements, area_width, area_height): 
		adj_shapes = []
		text_shapes = []
		layout_problem = LayoutProblem(area_width, area_height)
		for shape in elements: 
			# shape_id = uuid.uuid4().hex
			shape_id = shape["name"]
			new_shape = shapes.Shape(shape, str(shape_id))
			adj_shapes.append(new_shape)
		
		layout_problem.shapes = adj_shapes
		return cls(layout_problem)

	@property 
	def shapes(self): 
		return self.shapes

	def shapes(self, shapes):
		self.__shapes = shapes

	def solve(self): 
		self.solver = z3.Solver()
		self.shapes = self.problem.shapes
		print("num shapes: " + str(len(self.shapes)))

		for i in range(0, len(self.shapes)):
			shape1 = self.shapes[i] 

			# The height/width and position cannot exceed the available bounds
			self.solver.add((shape1.adjusted_x+shape1.width) <= self.problem.box_width)
			self.solver.add((shape1.adjusted_y+shape1.width) <= self.problem.box_height)

			# The x,y coordinates cannot be negative
			self.solver.add(shape1.adjusted_x >= 0)
			self.solver.add(shape1.adjusted_y >= 0)


		# For each pair of shapes add non-overlapping constraints 
		for i in range(0, len(self.shapes)): 
			for j in range(0, len(self.shapes)): 
				if i != j: 
					shape1 = self.shapes[i]
					shape2 = self.shapes[j]

					# Non-overlappping constraints 
					left = shape1.adjusted_x+shape1.width <= shape2.adjusted_x
					right = shape1.adjusted_x >= shape2.adjusted_x + shape2.width
					top = shape1.adjusted_y+shape1.height <= shape2.adjusted_y
					bottom = shape1.adjusted_y >= shape2.adjusted_y + shape2.height
					self.solver.add(Or(left, right, top, bottom))

		# Evaluate the results
		# print('Constraints: ')
		# print(self.solver.sexpr())
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
				curr_model = model
				
		return results

	def solve_and_check_solution(self): 
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

	def translate_model_to_shapes(self, model): 
		# Convert the produced values back to the format of shapes to be drawn
		final_shapes_json = []
		for shape in self.shapes: 
			final_x = shape.adjusted_x
			final_y = shape.adjusted_y

			adj_x = model[final_x].as_string()
			adj_y = model[final_y].as_string()

			adj_x = int(adj_x)
			adj_y = int(adj_y)

			# TOODO later figure out why necessary or do something more efficient
			json_shape = copy.deepcopy(shape.json_shape)
			json_shape["location"]["x"] = adj_x
			json_shape["location"]["y"] = adj_y
			final_shapes_json.append(json_shape)

		return final_shapes_json
	
	def add_solution_to_constraints(self, model): 
		for shape in self.shapes: 
			final_x = shape.adjusted_x
			final_y = shape.adjusted_y
			adj_x = model[final_x].as_string()
			adj_y = model[final_y].as_string()

			adj_x = int(adj_x)
			adj_y = int(adj_y)

			self.solver.add(shape.adjusted_x != adj_x)
			self.solver.add(shape.adjusted_y != adj_y)



