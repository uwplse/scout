from z3 import Int
import copy 
import uuid 
import numpy as np
import math

CANVAS_WIDTH = 375
CANVAS_HEIGHT = 667

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

	def compute_symmetry_cost(self, cost_matrix): 
		# Compute the symmetry cost
		mat_height = len(cost_matrix)
		mat_width = len(cost_matrix[0])
		right_i = math.ceil(mat_width/2)
		bottom_i = math.ceil(mat_height/2)

		# Split the matrix into two halves vertically
		first_half = cost_matrix[0:mat_height, 0:int(mat_width/2)]

		second_half = cost_matrix[0:mat_height, right_i:mat_width]
		top_half = cost_matrix[0:int(mat_height/2), 0:mat_width]
		bottom_half = cost_matrix[bottom_i:mat_height, 0:mat_width]

		# Then rotate the second half l to r
		second_half_rotated = np.fliplr(second_half)
		bottom_half_rotated = np.flipud(bottom_half)

		# Use bitwise XOR to find the bits that are still set
		results_lr = np.bitwise_xor(first_half, second_half_rotated)
		results_tb = np.bitwise_xor(top_half, bottom_half_rotated)

		total_lr = np.sum(results_lr)
		# total_tb = np.sum(results_tb)
		total = total_lr # + total_tb
		return int(total)

	def convert_to_json(self, shapes, model):
		# for shape in shapes:
		# 	if shape.type == "container":
		# 		print(shape.shape_id)
		# 		f_x = model[shape.x.z3]
		# 		f_y = model[shape.y.z3]
		# 		f_width = model[shape.width]
		# 		f_height = model[shape.height]
		# 		prox = model[shape.proximity.z3]

		# 		adj_x = f_x.as_string()
		# 		adj_y = f_y.as_string()
		# 		adj_prox = prox.as_string()
		# 		adj_prox = int(adj_prox)

		# 		adj_x = int(adj_x)
		# 		adj_y = int(adj_y)
		# 		adj_width = f_width.as_string()
		# 		adj_height = f_height.as_string()
		# 		adj_width = int(adj_width)
		# 		adj_height = int(adj_height)

		# 		print(adj_x,adj_y,adj_width,adj_height)
		# 		print(adj_prox)
		sln = dict()
		cost_matrix = np.zeros((CANVAS_HEIGHT, CANVAS_WIDTH), dtype=np.uint8)
		new_elements = []
		for s_index in range(0, len(shapes)):  
			shape = shapes[s_index]

			f_x = model[shape.x.z3]
			f_y = model[shape.y.z3]
			adj_x = f_x.as_string()
			adj_y = f_y.as_string()
			adj_x = int(adj_x)
			adj_y = int(adj_y)

			# Copy the solved info back into the JSON shape
			if shape.element is not None: 
				# Dont add any JSON for the canvas_root shape to the results
				# TODO: Figure out whether we should
				element = copy.deepcopy(shape.element)
				new_elements.append(element)

				if "location" in element: 
					element["location"]["x"] = adj_x
					element["location"]["y"] = adj_y

				height = shape.height
				width = shape.width
				if shape.type == "container": 
					# Also include the container properties in the element object for each container shape 
					# TODO: At some point when we have more properties than these we should make a collection and iterate instead
					# so we don't have to edit this place every time we add a property
					arrangement = model[shape.arrangement.z3].as_string()
					alignment = model[shape.alignment.z3].as_string()
					proximity = model[shape.proximity.z3].as_string()
					element["arrangement"] = int(arrangement)
					element["alignment"] = int(alignment)
					element["proximity"] = int(proximity)

					# For containers, retrieve the solved for height and width from the model 
					if "size" in element: 
						height = model[shape.height].as_string()
						width = model[shape.width].as_string()
						height = int(height)
						width = int(width)
						element["size"]["width"] = width
						element["size"]["height"] = height

				if "size" in element and "location" in element:
					print(adj_y)
					print(adj_x)
					print(width)
					print(height) 
					cost_matrix[adj_y:(adj_y+height-1),adj_x:(adj_x+width-1)] = 1

		cost = self.compute_symmetry_cost(cost_matrix)

		# print("Total cost: " + str(cost))
		sln["elements"] = new_elements
		sln["id"] = uuid.uuid4().hex
		sln["cost"] = cost

		return sln