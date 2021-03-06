from z3 import *
import cost as ch
import uuid
import numpy as np
import cost_model
from size_domains import MAX_HEIGHT, MAX_WIDTH, MIN_HEIGHT, MIN_WIDTH

CANVAS_WIDTH = 360
CANVAS_HEIGHT = 640

class Solution(object): 
	""" Solution class keeps track of the variables and assigned values for a given design solution """
	def __init__(self):
		self.variables = []
		self.id = uuid.uuid4().hex

	def add_assigned_variable(self, variable): 
		""" Add variable to the list of assigned variables """ 
		self.variables.append(variable)

	def parse_position_values(self, shape, element, variables, model):
		""" Parse values out of the Z3 model for x, y position and store them on the element object """
		f_x = model[variables[shape.variables.x.id]]
		f_y = model[variables[shape.variables.y.id]]
		adj_x = f_x.as_string()
		adj_y = f_y.as_string()
		adj_x = int(adj_x)
		adj_y = int(adj_y)		
		element["x"] = adj_x
		element["y"] = adj_y

	def parse_grid_values(self, shape, element, variables, model):
		""" Parse values out of the Z3 model for layout grid variables and store them on the element object """
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
		""" Parse values out of the Z3 model for height,width and store them on the element object """
		height = model[variables[shape.computed_height()]].as_string()
		width = model[variables[shape.computed_width()]].as_string()
		height = int(height)
		width = int(width)
		element["width"] = width
		element["height"] = height
		element["size"] = [width, height]

	def parse_container_values(self, shape, element, variables, model):
		""" Parse values out of the Z3 model for container properties and store them on the element object """
		arrangement = model[variables[shape.variables.arrangement.id]].as_string()
		alignment = model[variables[shape.variables.alignment.id]].as_string()
		padding = model[variables[shape.variables.padding.id]].as_string()
		group_alignment = model[variables[shape.variables.group_alignment.id]].as_string()

		element["arrangement"] = int(arrangement)
		element["alignment"] = int(alignment)
		element["padding"] = int(padding)
		element["group_alignment"] = int(group_alignment)

	def parse_column_values(self, shape, element, variables, model):
		""" Parse values out of the Z3 model for left_column, right_column, and canvas_alignment 
		 and store them on the element object """
		left_column = model[variables[shape.variables.left_column.id]].as_string()
		element["left_column"] = int(left_column)

		right_column = model[variables[shape.variables.right_column.id]].as_string()
		element["right_column"] = int(right_column)

		canvas_alignment = model[variables[shape.variables.canvas_alignment.id]].as_string()
		element["canvas_alignment"] = int(canvas_alignment)

	def parse_alternate_values(self, shape, element, variables, model):
		""" Parse values out of the Z3 model for alternate variable and store it on the element object """
		alternate = model[variables[shape.variables.alternate.id]].as_string()
		element["alternate"] = alternate

	def parse_size_multiplier_values(self, shape, element, variables, model):
		""" Parse values out of the Z3 model for size_factor multiplier variable and store it on the element object """
		size_factor = model[variables[shape.variables.size_factor.id]].as_string()
		size_factor = int(size_factor)
		element["size_factor"] = size_factor

	def parse_values(self, shape, element, variables, model): 
		""" Parses values out of the stored Z3 model and stores them on the element object.
			What gets parsed depends on the element/shape type """
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

	def parse_variables_from_model(self, model):
		""" Return a collection of variables parsed out of the Z3 model """ 
		variables = dict()
		num_vars = len(model)

		decls = model.decls()
		for i in range(num_vars):
			var = decls[i]
			name = var.name()
			if name != 'div0' and name != 'mod0':
				variables[var.name()] = var()
		return variables

	def process_hierarchy(self, tree, variables, model, cost_matrix, cost_metrics):
		""" Process element tree to get the solved variable values out of the model into corresponding elements 
			And compute corresponding cost metrics """ 
		if tree.element is not None: 
			element = copy.deepcopy(tree.element)

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
					cost_metrics['importance_max'] += (MAX_HEIGHT - tree.orig_height)
					cost_metrics['importance_max'] += (MAX_WIDTH - tree.orig_width)

					# Compute the distance of the shape from the center of the canvas
					cost_metrics['distance_cost'] += ch.compute_distance_from_center(x, y, width, height)
				elif tree.importance == "low":
					# Used for computing importance cost
					cost_metrics['importance_change'] += (tree.orig_height - height)
					cost_metrics['importance_change'] += (tree.orig_width - width)
					cost_metrics['importance_max'] += (tree.orig_height - MIN_HEIGHT)
					cost_metrics['importance_max'] += (tree.orig_width - MIN_WIDTH)

					cost_metrics['distance_cost'] += ch.compute_inverse_distance_from_center(x, y, width, height)

				# Only the locations of leaf level shapes to compute the symmetry cost
				cost_matrix[y:(y+height-1),x:(x+width-1)] = 1

			if hasattr(tree, "children") and len(tree.children):
				element['children'] = []
				for child in tree.children: 
					child_element = self.process_hierarchy(child, variables, model, cost_matrix, cost_metrics)
					if child_element is not None: 
						element['children'].append(child_element)

			return element



	def convert_to_json(self, tree, model):
		""" Given the element tree and the Z3 model, parse the assigned values out of the model and store them 
			in a JSON object for the solution 

			Parameters: 
				tree: Element 
		"""
		sln = dict()
		cost_matrix = np.zeros((CANVAS_HEIGHT, CANVAS_WIDTH), dtype=np.uint8)
		new_elements = dict()

		# Cost variables
		cost_metrics = dict()
		cost_metrics['importance_change'] = 0 
		cost_metrics['distance_cost'] = 0 
		cost_metrics['importance_max'] = 0

		variables = self.parse_variables_from_model(model)

		element_tree = self.process_hierarchy(tree, variables, model, cost_matrix, cost_metrics)

		# Old cost function metrics. 
		# symmetry_cost = ch.compute_symmetry_cost(cost_matrix)
		# importance_change = cost_metrics['importance_change']
		# importance_max = cost_metrics['importance_max']
		# distance_cost = cost_metrics['distance_cost']

		# importance_cost = ch.compute_importance_cost(importance_change, importance_max)
		# cost = ch.compute_weighted_cost(symmetry_cost, importance_cost, distance_cost)

		# Compute the cost model score for the element tree. 
		new_cost = cost_model.compute_cost(element_tree)
		cost = new_cost

		print("Total cost: " + str(cost))
		sln["elements"] = element_tree
		sln["id"] = self.id 
		sln["cost"] = cost # Assign the computed cost here. 
		sln["valid"] = True
		sln["saved"] = 0
		sln["conflicts"] = []

		return sln