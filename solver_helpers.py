from z3 import *
import copy 
import uuid 
import numpy as np
import math
import shapes as shape_objects
from fractions import Fraction
import time

CANVAS_WIDTH = 375
CANVAS_HEIGHT = 667

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

def parse_variables_from_model(model):
	variables = dict()
	num_vars = len(model)

	decls = model.decls()
	for i in range(num_vars):
		var = decls[i]
		variables[var.name()] = var()
	return variables

class Variable(object):
	def __init__(self, shape_id, name, domain=[], index_domain=True, var_type="Int"):
		self.shape_id = shape_id
		self.name = name
		self.id = name + "_" + shape_id
		self.assigned = None
		self.domain = domain
		self.type = var_type

		# If this is true, the domain values produced by the solver `
		# map directly to the indexes of the variables in the list
		# If it is false, the domain values the solver produces
		# will be the actual numerical or string values from the domain
		self.index_domain = index_domain

	def domain(self, domain): 
		self.domain = domain

	def assign(self, value): 
		self.assigned = value

	def get_value_from_element(self, element):
		# Return a Z3 expression or value to use in Z3 expressions from the element
		value = element[self.name]
		if self.type == "String":
			return "\"" + value + "\""
		return value

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

	def compute_weighted_cost(self, importance_cost, symmetry_cost, distance_cost):
		return importance_cost + symmetry_cost + distance_cost

	def compute_distance_from_center(self, shape_x, shape_y, shape_width, shape_height): 
		center_x = CANVAS_WIDTH/2
		center_y = CANVAS_HEIGHT/2 

		shape_center_x = shape_x + (shape_width/2)
		shape_center_y = shape_y + (shape_height/2)

		# Euclidian distance from the center
		x_dist = int(abs(shape_center_x - center_x))
		y_dist = int(abs(shape_center_y - center_y))

		distance = math.sqrt(x_dist^2 + y_dist^2)
		return distance

	def compute_inverse_distance_from_center(self, shape_x, shape_y, shape_width, shape_height): 
		center_x = CANVAS_WIDTH/2
		center_y = CANVAS_HEIGHT/2 

		shape_center_x = shape_x + (shape_width/2)
		shape_center_y = shape_y + (shape_height/2)

		# Euclidian distance from the center
		x_dist = int(abs(shape_center_x - center_x))
		y_dist = int(abs(shape_center_y - center_y))

		# Subtract again from the center distance so we get distance from edge
		x_dist = int(abs(x_dist - center_x))
		y_dist = int(abs(y_dist - center_y))

		distance = math.sqrt(x_dist^2 + y_dist^2)
		return distance

	def convert_to_json(self, shapes, model, context):
		sln = dict()
		cost_matrix = np.zeros((CANVAS_HEIGHT, CANVAS_WIDTH), dtype=np.uint8)
		new_elements = dict()

		# Cost variables
		importance_change = 0
		importance_max = 0
		distance_cost = 0

		variables = parse_variables_from_model(model)
		for shape in shapes.values():
			f_x = model[variables[shape.variables.x.id]]
			f_y = model[variables[shape.variables.y.id]]
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

				if shape.type == "container": 
					height = model[variables[shape.computed_height()]].as_string()
					width = model[variables[shape.computed_width()]].as_string()
					height = int(height)
					width = int(width)
					element["width"] = width
					element["height"] = height

					# Also include the container properties in the element object for each container shape 
					# TODO: At some point when we have more properties than these we should make a collection and iterate instead
					# so we don't have to edit this place every time we add a property
					arrangement = model[variables[shape.variables.arrangement.id]].as_string()
					alignment = model[variables[shape.variables.alignment.id]].as_string()
					padding = model[variables[shape.variables.padding.id]].as_string()
					element["arrangement"] = int(arrangement)
					element["alignment"] = int(alignment)
					element["padding"] = int(padding)

					if shape.has_columns:
						column = model[variables[shape.variables.column.id]].as_string()
						element["column"] = int(column)
						element["canvas_child"] = True

				elif shape.type == "canvas": 
					margin = model[variables[shape.variables.margin.id]].as_string()
					baseline_grid = model[variables[shape.variables.baseline_grid.id]].as_string()
					gutter_width = model[variables[shape.variables.gutter_width.id]].as_string()
					column_width = model[variables[shape.variables.column_width.id]].as_string()
					columns = model[variables[shape.variables.columns.id]].as_string()
					element["margin"] = int(margin)
					element["baseline_grid"] = int(baseline_grid)
					element["columns"] = int(columns)
					element["column_width"] = int(column_width)
					element["gutter_width"] = int(gutter_width)
				elif shape.type == "leaf": 
					height = model[variables[shape.computed_height()]].as_string()
					width = model[variables[shape.computed_width()]].as_string()
					size_factor = model[variables[shape.variables.size_factor.id]].as_string()
					height = int(height)
					width = int(width)
					size_factor = int(size_factor)
					element["width"] = width
					element["height"] = height
					element["size_factor"] = size_factor

					if shape.has_columns:
						column = model[variables[shape.variables.column.id]].as_string()
						element["column"] = int(column)
						element["canvas_child"] = True

					if shape.is_alternate: 
						alternate = model[variables[shape.variables.alternate.id]].as_string()
						alt_value = int(alternate)
						alt_value = shape.variables.alternate.domain[alt_value]
						element["alternate"] = alt_value

					# Only consider emphassis for leaf node elements
					if shape.importance == "high": 
						# Cost will be the distance from the maximum size
						importance_change += (height - shape.orig_height)
						importance_change += (width - shape.orig_width)
						importance_max += (shape_objects.MAX_HEIGHT - shape.orig_height)
						importance_max += (shape_objects.MAX_WIDTH - shape.orig_width)

						# Compute the distance of the shape from the center of the canvas
						distance_cost += self.compute_distance_from_center(adj_x, adj_y, width, height)
					elif shape.importance == "low": 
						# Used for computing importance cost
						importance_change += (shape.orig_height - height)
						importance_change += (shape.orig_width - width)
						importance_max += (shape.orig_height - shape_objects.MIN_HEIGHT)
						importance_max += (shape.orig_width - shape_objects.MIN_WIDTH)

						distance_cost += self.compute_inverse_distance_from_center(adj_x, adj_y, width, height)

					# Only the locations of leaf level shapes to compute the symmetry cost
					cost_matrix[adj_y:(adj_y+height-1),adj_x:(adj_x+width-1)] = 1

		symmetry_cost = self.compute_symmetry_cost(cost_matrix)
		importance_cost = self.compute_importance_cost(importance_change, importance_max)
		cost = self.compute_weighted_cost(symmetry_cost, importance_cost, distance_cost)

		# print("Total cost: " + str(cost))
		sln["elements"] = new_elements
		sln["id"] = self.id 
		sln["cost"] = cost
		sln["valid"] = True
		sln["saved"] = 0

		return sln