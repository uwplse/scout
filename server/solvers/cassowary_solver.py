from cassowary import SimplexSolver, REQUIRED
import copy

class CassowarySolver(object): 
	def __init__(self, shapes, groups): 
		self.shapes = shapes
		self.groups = groups
		self.is_solution = True
		self.solver = SimplexSolver()

	def add(self, constraint, strength=REQUIRED):
		self.solver.add_constraint(constraint, strength=strength)

	def get_solution(self): 
		print("Looking for a solution.")
		return self.is_solution

	def add_and_resolve(self): 
		return None

	def get_json_shapes(self): 
		final_json = []
		if self.shapes is not None: 
			for shape_id, shape in self.shapes.items(): 
				json_shape = copy.deepcopy(shape.json_shape)
				json_shape["location"]["x"] = shape.adjusted_x.value
				json_shape["location"]["y"] = shape.adjusted_y.value
				json_shape["size"]["width"] = shape.adjusted_width.value
				json_shape["size"]["height"] = shape.adjusted_height.value

				final_json.append(json_shape)

		return final_json