import numpy as np
import math

CANVAS_WIDTH = 360
CANVAS_HEIGHT = 640

def compute_symmetry_cost(cost_matrix):
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

def compute_importance_cost(importance_change, importance_max):
	# Cost is equal to the difference between the total amount of 
	# change of the sizes and the maximum amount of change in the sizes
	# The closer the change is to the maximum amount, this should decrease
	# the cost
	return importance_max - importance_change

def compute_weighted_cost(importance_cost, symmetry_cost, distance_cost):
	return importance_cost + symmetry_cost + distance_cost

def compute_distance_from_center(shape_x, shape_y, shape_width, shape_height):
	center_x = CANVAS_WIDTH/2
	center_y = CANVAS_HEIGHT/2 

	shape_center_x = shape_x + (shape_width/2)
	shape_center_y = shape_y + (shape_height/2)

	# Euclidian distance from the center
	x_dist = int(abs(shape_center_x - center_x))
	y_dist = int(abs(shape_center_y - center_y))

	distance = math.sqrt(x_dist^2 + y_dist^2)
	return distance

def compute_inverse_distance_from_center(shape_x, shape_y, shape_width, shape_height):
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