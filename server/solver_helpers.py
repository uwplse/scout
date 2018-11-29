from z3 import Int, String, StringVal, Real
import copy 
import uuid 
import numpy as np
import math
import shapes as shape_objects
from fractions import Fraction

CANVAS_WIDTH = 375
CANVAS_HEIGHT = 667
MAGNIFICATION_VALUES = [1.1,1.2,1.3,1.4,1.5,1.6,1.7,1.8,1.9,2]
MINIFICATION_VALUES = [0.1,0.2,0.3,0.4,0.5,0.6,0.7,0.8,0.9]

def get_row_column_values(num_siblings):
	values = []
	rows_or_columns = 2
	while rows_or_columns < num_siblings: 
		values.append(rows_or_columns)
		rows_or_columns += 1
	return values

def get_possible_row_column_values(num_rows): 
	values = []
	start = 1
	while start <= num_rows: 
		values.append(start)
		start += 1
	return values

def parse_unsat_core(unsat_core):
	# Parse the conflicting constraints out of the unsat core and return identifiers for each shape and the associated conflicting constraint
	conflicts = []
	for i in range(0, len(unsat_core)): 
		conflict = unsat_core[i]
		conflict_string = str(conflict)
		if len(conflict_string) >= 5 and conflict_string.find("lock_", 0, 5) > -1:
			parts = conflict_string.split("_")
			if len(parts) >= 4: 
				lock_id = parts[0]
				shape_id = parts[1]
				variable = parts[2]
				value = parts[3]

				if len(parts) > 4: 
					value = parts[4]
					variable = parts[2] + "_" + parts[3]				

				conflict = dict()
				conflict["shape_id"] = shape_id
				conflict["variable"] = variable
				conflict["value"] = value
				conflicts.append(conflict)
	return conflicts

class Variable(object): 
	def __init__(self, shape_id, name, domain=[], index_domain=True, var_type="int", ):
		self.shape_id = shape_id
		self.name = name
		self.assigned = None
		self.domain = domain
		self.type = var_type

		# If this is true, the domain values produced by the solver `
		# map directly to the indexes of the variables in the list
		# If it is false, the domain values the solver produces
		# will be the actual numerical or string values from the domain
		self.index_domain = index_domain

		# Z3 Variable for testing (??)
		if self.type == "str": 
			self.z3 = String(shape_id + "_" + name)

			if len(self.domain): 
				str_domain = []
				for dom_value in self.domain: 
					dom_value_str = StringVal(dom_value)
					str_domain.append(dom_value_str)
				self.domain = str_domain
		elif self.type == "real": 
			self.z3 = Real(shape_id + "_" + name)
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

	def compute_importance_cost(self, importance_change, importance_max): 
		# Cost is equal to the difference between the total amount of 
		# change of the sizes and the maximum amount of change in the sizes
		# The closer the change is to the maximum amount, this should decrease
		# the cost
		return importance_max - importance_change

	def compute_weighted_cost(self, importance_cost, symmetry_cost):
		return importance_cost + symmetry_cost

	def convert_to_json(self, shapes, model):
		sln = dict()
		cost_matrix = np.zeros((CANVAS_HEIGHT, CANVAS_WIDTH), dtype=np.uint8)
		new_elements = dict()

		# Cost variables
		importance_change = 0
		importance_max = 0
		distance_cost = 0

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

				element["x"] = adj_x
				element["y"] = adj_y

				height = shape.height()
				width = shape.width()

				if shape.importance_set: 
					if shape.importance == 'most':
						# Cost will be the distance from the maximum size
						importance_change += (height - shape.orig_height)
						importance_change += (width - shape.orig_width)
						importance_max += (shape_objects.maximum_sizes[shape.shape_type] - shape.orig_height)
						importance_max += (shape_objects.maximum_sizes[shape.shape_type] - shape.orig_width)

						# Compute the distance of the shape from the center of the canvas
						# distance_cost += self.compute_cost(shape, CANVAS_HEIGHT, CANVAS_WIDTH)
					elif shape.importance == 'least': 
						importance_change += (shape.orig_height - height)
						importance_change += (shape.orig_width - width)
						importance_max += (shape.orig_height - shapes.minimum_sizes[shape.shape_type])
						importance_max += (shape.orig_width - shapes.minimum_sizes[shape.shape_type])

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
						magnification = Fraction(magnification)
						magnification = float(magnification)
						element["magnification"] =  magnification

						# magnification_factor = 1/magnification if magnification > 0 else 0
						height = height * magnification
						width = width * magnification
						height = int(round(height,0))
						width = int(round(width,0))
						element["size"]["height"] = height
						element["size"]["width"] = height
					elif shape.importance == "least": 
						minification = model[shape.variables.minification.z3].as_string()
						minification = Fraction(minification)
						minification = float(minification)
						element["minification"] = minification

						# minification_factor = 1/minification if minification > 0 else 0
						height = height * minification
						width = width * minification
						height = int(round(height,0))
						width = int(round(width, 0))
						element["size"]["height"] = height
						element["size"]["width"] = width
					else: 
						element["minification"] = 0
						element["magnification"] = 0

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
					grid = model[shape.variables.grid.z3].as_string()
					background_color = model[shape.variables.background_color.z3].as_string()
					element["alignment"] = int(alignment)
					element["justification"] = int(justification)
					element["margin"] = int(margin)
					element["grid"] = int(grid)
					element["background_color"] = background_color.replace("\"", "")

				if shape.type == "leaf": 
					# Only the locations of leaf level shapes to compute the symmetry cost
					cost_matrix[adj_y:(adj_y+height-1),adj_x:(adj_x+width-1)] = 1

		symmetry_cost = self.compute_symmetry_cost(cost_matrix)
		importance_cost = self.compute_importance_cost(importance_change, importance_max)
		cost = self.compute_weighted_cost(symmetry_cost, importance_cost)

		# print("Total cost: " + str(cost))
		sln["elements"] = new_elements
		sln["id"] = self.id 
		sln["cost"] = cost
		sln["valid"] = True
		sln["saved"] = 0

		return sln