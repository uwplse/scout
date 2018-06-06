from z3 import Int, String, StringVal
import copy 
import uuid 
import numpy as np
import math

CANVAS_WIDTH = 375
CANVAS_HEIGHT = 667
MAGNIFICATION_VALUES = [1,2,3,4,5,6,7,8,9,10]

def parse_unsat_core(unsat_core):
	# Parse the conflicting constraints out of the unsat core and return identifiers for each shape and the associated conflicting constraint
	conflicts = []
	for i in range(0, len(unsat_core)): 
		conflict = unsat_core[i]
		conflict_string = str(conflict)
		if len(conflict_string) >= 5 and conflict_string.find("lock_", 0, 5) > -1:
			parts = conflict_string.split("_")
			lock_id, shape_id, variable, value = parts
			conflict = dict()
			conflict["shape_id"] = shape_id
			conflict["variable"] = variable
			conflict["value"] = value
			conflicts.append(conflict)
	return conflicts

class Variable(object): 
	def __init__(self, shape_id, name, domain=[], varType="int"): 
		self.shape_id = shape_id
		self.name = name
		self.assigned = None
		self.domain = domain
		self.type = varType

		# Z3 Variable for testing (??)
		if self.type == "str": 
			self.z3 = String(shape_id + "_" + name)
		else: 
			self.z3 = Int(shape_id + "_" + name)

	def domain(self, domain): 
		self.domain = domain

	def assign(self, value): 
		self.assigned = value

	def get_value_from_element(self, element):
		# Return a Z3 expression or value to use in Z3 expressions from the element
		if self.type == "str": 
			return StringVal(element[self.name])

		elif self.name == "x" or self.name == "y":
			return element["location"][self.name]

		elif self.name == "width" or self.name == "height":
			return element["size"][self.name]

		return element[self.name]

class Solution(object): 
	def __init__(self): 
		self.variables = []
		self.id = uuid.uuid4().hex

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
		sln = dict()
		cost_matrix = np.zeros((CANVAS_HEIGHT, CANVAS_WIDTH), dtype=np.uint8)
		new_elements = dict()
		for shape in shapes.values():  
			f_x = model[shape.variables.x.z3]
			f_y = model[shape.variables.y.z3]
			adj_x = f_x.as_string()
			adj_y = f_y.as_string()
			adj_x = int(adj_x)
			adj_y = int(adj_y)

			# Copy the solved info back into the JSON shape
			if shape.element is not None: 
				# Dont add any JSON for the canvas_root shape to the results
				# TODO: Figure out whether we should
				element = copy.deepcopy(shape.element)
				new_elements[element["name"]] = element

				if "location" not in element:
					element["location"] = dict()

				element["location"]["x"] = adj_x
				element["location"]["y"] = adj_y

				height = shape.height()
				width = shape.width()

				if shape.type == "container": 
					height = model[shape.height()].as_string()
					width = model[shape.width()].as_string()
					height = int(height)
					width = int(width)
					element["size"]["width"] = width
					element["size"]["height"] = height

				if shape.importance_set: 
					if shape.importance == "most": 
						magnification = model[shape.variables.magnification.z3].as_string()
						magnification = int(magnification)
						height = height + ((1/magnification) * height)
						width = width + ((1/magnification) * width)
						height = int(round(height,0))
						width = int(round(width,0))
						element["size"]["height"] = height
						element["size"]["width"] = height
					elif shape.importance == "least": 
						minification = model[shape.variables.minification.z3].as_string()
						minification = int(minification)
						height = height - ((1/minification) * height)
						width = width - ((1/minification) * width)
						height = int(round(height,0))
						width = int(round(width, 0))
						element["size"]["height"] = height
						element["size"]["width"] = width

				if shape.type == "container": 
					# Also include the container properties in the element object for each container shape 
					# TODO: At some point when we have more properties than these we should make a collection and iterate instead
					# so we don't have to edit this place every time we add a property
					arrangement = model[shape.variables.arrangement.z3].as_string()
					alignment = model[shape.variables.alignment.z3].as_string()
					proximity = model[shape.variables.proximity.z3].as_string()
					distribution = model[shape.variables.distribution.z3].as_string()
					element["arrangement"] = int(arrangement)
					element["alignment"] = int(alignment)
					element["proximity"] = int(proximity)
					element["distribution"] = int(distribution)
				elif shape.type == "canvas": 
					alignment = model[shape.variables.alignment.z3].as_string()
					justification = model[shape.variables.justification.z3].as_string()
					margin = model[shape.variables.margin.z3].as_string()
					element["alignment"] = int(alignment)
					element["justification"] = int(justification)
					element["margin"] = int(margin)
				elif shape.type == "leaf":
					if shape.importance == "most":
						magnification = model[shape.variables.magnification.z3].as_string()
						element["magnification"] = int(magnification)
					elif shape.importance == "least":
						minification = model[shape.variables.minification.z3].as_string()
						element["minification"] = int(minification)
					else: 
						element["minification"] = 0
						element["magnification"] = 0

				if shape.type == "leaf": 
					# Only the locations of leaf level shapes to compute the symmetry cost
					cost_matrix[adj_y:(adj_y+height-1),adj_x:(adj_x+width-1)] = 1

		cost = self.compute_symmetry_cost(cost_matrix)

		# print("Total cost: " + str(cost))
		sln["elements"] = new_elements
		sln["id"] = self.id 
		sln["cost"] = cost
		sln["valid"] = True
		sln["saved"] = 0

		return sln