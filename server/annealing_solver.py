from __future__ import print_function
import math
import random
import json
import sys
from simanneal import Annealer

class LayoutAnnealingProblem(Annealer):

	"""Test annealer with a travelling salesman problem.
	"""

	# pass extra data (the distance matrix) into the constructor
	def __init__(self, state, box_width, box_height):
		self.box_width = box_width
		self.box_height = box_height
		super(LayoutAnnealingProblem, self).__init__(state)  # important!

	def move(self):
		# Randomly choose a shape to mutate
		num_shapes = len(self.state)
		shape_i = random.randint(0, num_shapes-1)
		shape_to_mutate = self.state[shape_i]
		x,y,width,height = shape_to_mutate

		# Choose a random axis to modify 
		x_or_y = random.randint(0, 2)
		if x_or_y == 0: 
			# Modify the X value 
			# Randomly choose a value on the canvas
			max_x = self.box_width - width 
			shape_x = random.randint(0, max_x)
			shape_to_mutate[0] = shape_x
		else: 
			max_y = self.box_height - height
			shape_y = random.randint(0, max_y)
			shape_to_mutate[1] = shape_y

	def aligned(self, shape1, shape2): 
		x1,y1,width1,height1 = shape1
		x2,y2,width2,height2 = shape2

		top = y1 == y2
		bottom = (y1 + height1) == (y2 + height2)
		left = x1 == x2
		right = (x1 + width1) == (x2 + width2)
		y_center = (y1 + (height1/2)) == (y2 + (height2/2))
		x_center = (x1 + (width1/2)) == (x2 + (width2/2))
		return top or bottom or left or right or x_center or y_center

	def num_alignments(self): 
		total = 0
		total_pairs = 0
		# Compute the number of aligned pairs in the current state
		for i in range(0, len(self.state)): 
			for j in range(0, len(self.state)): 
				if i != j: 
					shape1 = self.state[i]
					shape2 = self.state[j]
					if self.aligned(shape1, shape2):  
						total += 1
					total_pairs += 1
		return (total_pairs - total) 


	def energy(self):
		"""Calculates the length of the route."""
		# e = 0
		# for i in range(len(self.state)):
		#     e += self.distance_matrix[self.state[i-1]][self.state[i]]
		# return e
		return self.num_alignments()

def read_shapes_from_json(spec):
	shapes = []
	box_width = 300
	box_height = 300
	with open(spec) as data_file:
		config = json.load(data_file)
		elements = config["elements"]
		box_width = config["canvas_size"]["width"]
		box_height = config["canvas_size"]["height"]

		for element in elements: 
			x = element["location"]["x"]
			y = element["location"]["y"]
			width = element["size"]["width"]
			height = element["size"]["height"]
			shapes.append([x,y,width,height])

	return [box_width, box_height, shapes]

def randomize_initial_positions(state, box_width, box_height): 
	for shape in state: 
		max_x = box_width - shape[2]
		max_y = box_height - shape[3]
		rand_x = random.randint(0, max_x)
		rand_y = random.randint(0, max_y)
		shape[0] = rand_x
		shape[1] = rand_y 
	return state
	
if __name__ == '__main__':

	# latitude and longitude for the twenty largest U.S. cities
	spec = sys.argv[1]
	box_width, box_height, init_state = read_shapes_from_json(spec)
	init_state = randomize_initial_positions(init_state, box_width, box_height)
	num_shapes = len(init_state) 
	total_pairs = num_shapes * (num_shapes - 1)# The total number of possible alignment pairs
	tmax = total_pairs * 0.98
	tmin = 0

	tsp = LayoutAnnealingProblem(init_state, box_width, box_height)
	tsp.steps = 25000
	tsp.Tmax = tmax
	tsp.Tmin = tmin
	# since our state is just a list, slice is the fastest way to copy
	# tsp.copy_strategy = "slice"
	state, e = tsp.anneal()

	# for shape in shapes:
	#     print("\t", shape)