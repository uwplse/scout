import uuid 
from z3 import *
import shapes

def abs(x):
	return If(x>=0,x,-x)

def contains(a_list, a_id): 
	try: 
		a_list.index(a_id)
		return True
	except ValueError as e: 
		return False

class LayoutProblem(object): 
	def __init__(self, width, height): # Width and height are the size of the containing box
		self.box_width = width
		self.box_height = height

	@property 
	def box_width(self): 
		return self.box_width

	def box_width(self, width): 
		self.__box_width = width

	@property 
	def box_height(self): 
		return self.box_height

	def box_height(self, height): 
		self.__box_height = height

	@property 
	def shapes(self): 
		return self.shapes

	def shapes(self, shapes): 
		self.__shapes = shapes

class LayoutSolver(object): 
	def __init__(self, problem):
		self.problem = problem

	@classmethod
	def init_problem(cls, elements, area_width, area_height): 
		adj_shapes = []
		text_shapes = []
		layout_problem = LayoutProblem(area_width, area_height)
		for shape in elements: 
			x = shape["location"]["x"]
			y = shape["location"]["y"]
			width = shape["size"]["width"]
			height = shape["size"]["height"]
			new_shape = None

			shape_id = uuid.uuid4().hex
			new_shape = shapes.Shape(x, y, width, height, str(shape_id))
			adj_shapes.append(new_shape)
		
		layout_problem.shapes = adj_shapes
		return cls(layout_problem)

	@property 
	def shapes(self): 
		return self.shapes

	def shapes(self, shapes):
		self.__shapes = shapes

	def solve(self): 
		self.solver = z3.Solver()
		shapes = self.problem.shapes

		for i in range(0, len(shapes)):
			shape1 = shapes[i] 

			# The height/width and position cannot exceed the available bounds
			self.solver.add((shape1.adjusted_x+shape1.width) <= self.problem.box_width)
			self.solver.add((shape1.adjusted_y+shape1.width) <= self.problem.box_height)

			# The x,y coordinates cannot be negative
			self.solver.add(shape1.adjusted_x >= 0)
			self.solver.add(shape1.adjusted_y >= 0)


		# For each pair of shapes add non-overlapping constraints 
		for i in range(0, len(shapes)): 
			for j in range(0, len(shapes)): 
				if i != j: 
					shape1 = shapes[i]
					shape2 = shapes[j]

					# Non-overlappping constraints 
					left = shape1.adjusted_x+shape1.width <= shape2.adjusted_x
					right = shape1.adjusted_x >= shape2.adjusted_x + shape2.width
					top = shape1.adjusted_y+shape1.height <= shape2.adjusted_y
					bottom = shape1.adjusted_y >= shape2.adjusted_y + shape2.height
					self.solver.add(Or(left, right, top, bottom))



		# Evaluate the results
		print('Constraints: ')
		print(self.solver.sexpr())
		result = self.solver.check()

		if str(result) == 'sat': 
			# Find one solution for now
			model = self.solver.model()
			print(model)
			# shapes = self.translate_model_to_shapes(model, shapes)
			print("-------Statistics-------")
			#print self.solver.statistics()
			return shapes
		else: 
			print('solution could not be found :(')
			#print self.solver.unsat_core()

	def translate_model_to_shapes(model, shapes): 
		# Convert the produced values back to the format of shapes to be drawn
		print("converting")
