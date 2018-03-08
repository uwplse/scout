from z3 import Int
import copy 
import uuid 

class Variable(object): 
	def __init__(self, shape_id, name, domain=[]): 
		self.shape_id = shape_id
		self.name = name
		self.assigned = None
		self.domain = domain

		# Z3 Variable for testing (??)
		self.z3 = Int(shape_id + "_" + name)

	def domain(self, domain): 
		self.domain = domain

	def assign(self, value): 
		self.assigned = value

class Solution(object): 
	def __init__(self): 
		self.variables = []

	def add_assigned_variable(self, variable): 
		self.variables.append(variable)

	def convert_to_json(self, elements, shapes, model):
		# for shape in shapes:
		# 	if shape.type == "container":
		# 		print(shape.shape_id)
		# 		f_x = model[shape.x.z3]
		# 		f_y = model[shape.y.z3]
		# 		f_width = model[shape.width]
		# 		f_height = model[shape.height]
		# 		adj_x = f_x.as_string()
		# 		adj_y = f_y.as_string()
		# 		adj_x = int(adj_x)
		# 		adj_y = int(adj_y)
		# 		adj_width = f_width.as_string()
		# 		adj_height = f_height.as_string()
		# 		adj_width = int(adj_width)
		# 		adj_height = int(adj_height)
		# 		print(adj_x,adj_y,adj_width,adj_height)

		sln = dict()
		for e_index in range(0, len(elements)):  
			element = elements[e_index]
			shape = [shp for shp in shapes if shp.shape_id == element["name"]][0]

			f_x = model[shape.x.z3]
			f_y = model[shape.y.z3]
			adj_x = f_x.as_string()
			adj_y = f_y.as_string()
			adj_x = int(adj_x)
			adj_y = int(adj_y)

			# Copy the solved info back into the JSON shape
			element["location"]["x"] = adj_x
			element["location"]["y"] = adj_y

		new_elements = copy.deepcopy(elements);
		sln["elements"] = new_elements
		sln["id"] = uuid.uuid4().hex

		return sln