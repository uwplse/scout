""" Utilities used by the Solver class. 
"""
from z3 import *
import copy 
import uuid 
import numpy as np
import math
import shapes as shape_objects
from fractions import Fraction
import time

def get_element_names(element_tree, element_names=[]):
	"""Get a list of all the names of elements in the tree hierarchy"""
	element_names.append(element_tree['name'])

	if 'children' in element_tree: 
		for child in element_tree['children']: 
			get_element_names(child, element_names)

# def get_row_column_values(num_siblings):
# 	values = []
# 	rows_or_columns = 2
# 	while rows_or_columns < num_siblings: 
# 		values.append(rows_or_columns)
# 		rows_or_columns += 1
# 	return values

# def get_possible_row_column_values(num_rows): 
# 	values = []
# 	start = 1
# 	while start <= num_rows: 
# 		values.append(start)
# 		start += 1
# 	return values

def parse_unsat_core(unsat_core):
	""" Parse the conflicting constraints out of the unsat core and 
		return identifiers for each shape and the associated conflicting constraint """ 
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
	""" Return a collection of variables parsed out of the Z3 model """ 
	variables = dict()
	num_vars = len(model)

	decls = model.decls()
	for i in range(num_vars):
		var = decls[i]
		variables[var.name()] = var()
	return variables

def repair_solution_from_model(shapes, model, solution, relaxed_element_properties): 
	""" Update the values to the model values for the properties that were repaired by the repair loop """
	model_variables = parse_variables_from_model(model)

	for element_key,properties in relaxed_element_properties.items():
		element = solution["elements"][element_key]

		shape = shapes[element_key]

		variables = shape.variables.toDict()
		for variable_key in variables.keys(): 
			variable = variables[variable_key]		
			if variable.name in properties: 
				variable_value = model[model_variables[variable.id]].as_string()
				variable_value = int(variable_value)
				element[variable.name] = variable_value		

		# Also copy the x,y positions of the child elements recursively, as they don't need to 
		# explictily be relaxed
		if shape.children and len(shape.children): 
			repair_child_xy_values(model_variables, model, solution, shape)
	return solution

def repair_child_xy_values(model_variables, model, solution, shape): 
	""" Update the x, y position sof child element values when parent values were repaired, because they may have changed
		based on the parent's new arrangement """
	for child in shape.children:  
		x_variable = child.variables.x.id
		y_variable = child.variables.y.id 

		x_value = model[model_variables[x_variable]].as_string()
		y_value = model[model_variables[y_variable]].as_string()

		x_value = int(x_value)
		y_value = int(y_value)

		solution["elements"][child.shape_id]["x"] = x_value
		solution["elements"][child.shape_id]["y"] = y_value

		if hasattr(child, "children") and len(child.children):
			repair_child_xy_values(model_variables, model, solution, shape)