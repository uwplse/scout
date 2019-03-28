from z3 import *
import solver_helpers as sh
import cost as ch
import uuid
import shapes as shape_objects
import numpy as np
import cost_model

CANVAS_WIDTH = 360
CANVAS_HEIGHT = 640

class Solution(object): 
	def __init__(self):
		self.variables = []
		self.id = uuid.uuid4().hex

	def add_assigned_variable(self, variable): 
		self.variables.append(variable)

	def parse_position_values(self, shape, element, variables, model):
		f_x = model[variables[shape.variables.x.id]]
		f_y = model[variables[shape.variables.y.id]]
		adj_x = f_x.as_string()
		adj_y = f_y.as_string()
		adj_x = int(adj_x)
		adj_y = int(adj_y)		
		element["x"] = adj_x
		element["y"] = adj_y

	def parse_grid_values(self, shape, element, variables, model):
		# Parse out the grid variables from the model.  
		margin = int(model[variables[shape.variables.margin.id]].as_string())
		baseline_grid = int(model[variables[shape.variables.baseline_grid.id]].as_string())
		gutter_width = int(model[variables[shape.variables.gutter_width.id]].as_string())
		column_width = int(model[variables[shape.variables.column_width.id]].as_string())
		columns = int(model[variables[shape.variables.columns.id]].as_string())

		element["margin"] = margin
		element["baseline_grid"] = baseline_grid
		element["columns"] = columns
		element["column_width"] = column_width
		element["gutter_width"] = gutter_width
		element["grid_layout"] = [margin, columns, gutter_width, column_width]

	def parse_size_values(self, shape, element, variables, model):
		# Parse the size related variables from the model 
		height = model[variables[shape.computed_height()]].as_string()
		width = model[variables[shape.computed_width()]].as_string()
		height = int(height)
		width = int(width)
		element["width"] = width
		element["height"] = height

	def parse_container_values(self, shape, element, variables, model):
		# Also include the container properties in the element object for each container shape 
		# TODO: At some point when we have more properties than these we should make a collection and iterate instead
		# so we don't have to edit this place every time we add a property
		arrangement = model[variables[shape.variables.arrangement.id]].as_string()
		alignment = model[variables[shape.variables.alignment.id]].as_string()
		padding = model[variables[shape.variables.padding.id]].as_string()
		element["arrangement"] = int(arrangement)
		element["alignment"] = int(alignment)
		element["padding"] = int(padding)

	def parse_column_values(self, shape, element, variables, model):
		# Parse the left, right column values for elements on the root of the canvas. 
		left_column = model[variables[shape.variables.left_column.id]].as_string()
		element["left_column"] = int(left_column)

		right_column = model[variables[shape.variables.right_column.id]].as_string()
		element["right_column"] = int(right_column)

	def parse_alternate_values(self, shape, element, variables, model):
		alternate = model[variables[shape.variables.alternate.id]].as_string()
		element["alternate"] = alternate

	def parse_size_multiplier_values(self, shape, element, variables, model):
		size_factor = model[variables[shape.variables.size_factor.id]].as_string()
		size_factor = int(size_factor)
		element["size_factor"] = size_factor

	def parse_values(self, shape, element, variables, model): 
		# Parse solved varivalbe values from the model object  
		self.parse_position_values(shape, element, variables, model)

		if shape.type == "canvas": 
			self.parse_grid_values(shape, element, variables, model)
		elif shape.type == "container" or shape.type == "leaf": 
			self.parse_size_values(shape, element, variables, model)

			if shape.has_columns:
				self.parse_column_values(shape, element, variables, model)
				element["canvas_child"] = True

			if shape.type == "container": 
				self.parse_container_values(shape, element, variables, model)
			elif shape.type == "leaf": 
				self.parse_size_multiplier_values(shape, element, variables, model)
				element["size_combo"] = [element["width"], element["height"], element["size_factor"]]

				if shape.is_alternate: 
					self.parse_alternate_values(shape, element, variables, model)

	def compute_cost(self, tree):
		# Relevant variables: 
			# children = tree["children"]
			# x = tree["x"]
			# y = tree["y"]
			# width = tree["width"]
			# height = tree["height"]
			# type = tree["type"]

		# Returns the computed cost
		return 0 

	def process_hierarchy(self, tree, variables, model, cost_matrix, cost_metrics, elements_dict):
		if tree.element is not None: 
			element = copy.deepcopy(tree.element)
			elements_dict[element["name"]] = element; 

			# Get the computed values from the model 
			self.parse_values(tree, element, variables, model)

			# Emphasis cost function calculations
			if tree.type != "canvas":
				height = element["height"]
				width = element["width"]
				x = element["x"]
				y = element["y"]
				if tree.importance == "high":
					# Cost will be the distance from the maximum size
					cost_metrics['importance_change'] += (height - tree.orig_height)
					cost_metrics['importance_change'] += (width - tree.orig_width)
					cost_metrics['importance_max'] += (shape_objects.MAX_HEIGHT - tree.orig_height)
					cost_metrics['importance_max'] += (shape_objects.MAX_WIDTH - tree.orig_width)

					# Compute the distance of the shape from the center of the canvas
					cost_metrics['distance_cost'] += ch.compute_distance_from_center(x, y, width, height)
				elif tree.importance == "low":
					# Used for computing importance cost
					cost_metrics['importance_change'] += (tree.orig_height - height)
					cost_metrics['importance_change'] += (tree.orig_width - width)
					cost_metrics['importance_max'] += (tree.orig_height - shape_objects.MIN_HEIGHT)
					cost_metrics['importance_max'] += (tree.orig_width - shape_objects.MIN_WIDTH)

					cost_metrics['distance_cost'] += ch.compute_inverse_distance_from_center(x, y, width, height)

				# Only the locations of leaf level shapes to compute the symmetry cost
				cost_matrix[y:(y+height-1),x:(x+width-1)] = 1

			if hasattr(tree, "children") and len(tree.children):
				element['children'] = []
				for child in tree.children: 
					child_element = self.process_hierarchy(child, variables, model, cost_matrix, cost_metrics, elements_dict)
					if child_element is not None: 
						element['children'].append(child_element)

			return element

	def convert_to_json(self, tree, model):
		sln = dict()
		cost_matrix = np.zeros((CANVAS_HEIGHT, CANVAS_WIDTH), dtype=np.uint8)
		new_elements = dict()

		# Cost variables
		cost_metrics = dict()
		cost_metrics['importance_change'] = 0 
		cost_metrics['distance_cost'] = 0 
		cost_metrics['importance_max'] = 0

		variables = sh.parse_variables_from_model(model)

		elements_dict = dict()
		element_tree = self.process_hierarchy(tree, variables, model, cost_matrix, cost_metrics, elements_dict)

		# Current cost function metrics. 
		symmetry_cost = ch.compute_symmetry_cost(cost_matrix)
		importance_change = cost_metrics['importance_change']
		importance_max = cost_metrics['importance_max']
		distance_cost = cost_metrics['distance_cost']

		importance_cost = ch.compute_importance_cost(importance_change, importance_max)
		cost = ch.compute_weighted_cost(symmetry_cost, importance_cost, distance_cost)

		# New cost function
		# We can remove the above when we implement the new function 
		# Alnd also the related cost matrix for computing the symmetry (cost_matrix)
		# tree is a hierarchy structure of nodes with computed values 
		# for the variables (x,y,width,height, etc) and other metadata (type)
		cost = self.compute_cost(tree)

		new_cost = cost_model.compute_cost(element_tree)
		cost = new_cost

		print("Total cost: " + str(cost))
		sln["elements_dict"] = elements_dict
		sln["elements"] = element_tree
		sln["id"] = self.id 
		sln["cost"] = cost # Assign the computed cost here. 
		sln["valid"] = True
		sln["saved"] = 0
		sln["conflicts"] = []

		return sln