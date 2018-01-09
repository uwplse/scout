from z3 import *

# Adjustable shape position class
class Shape(object):
	def __init__(self, json_shape, shape_id):
		self.json_shape = json_shape
		self.orig_x = self.json_shape["location"]["x"]
		self.orig_y = self.json_shape["location"]["y"]
		self.id = shape_id

		self.width = self.json_shape["size"]["width"]
		self.height = self.json_shape["size"]["height"] 

		# Adjusted values are Z3 variables
		self.adjusted_x = Int(self.id + '_adjusted_x')
		self.adjusted_y = Int(self.id + '_adjusted_y')

	@property
	def orig_x(self):
		return self.orig_x

	def orig_x(self, x):
		self.__orig_x = x

	@property
	def adjusted_x(self): 
		return self.adjusted_x

	def adjusted_x(self, x): 
		self.__adjusted_x = x

	@property
	def orig_y(self): 
		return self.orig_y

	def orig_y(self, y):
		self.__orig_y = y

	@property
	def adjusted_y(self): 
		return self.adjusted_y

	def adjusted_y(self, y): 
		self.__adjusted_y = y

	@property 
	def width(self): 
		return self.width

	def width(self, width): 
		self.__width = width

	@property 
	def height(self): 
		return self.height

	def height(self, height): 
		self.__height = height

	@property 
	def id(self): 
		return self.id

	def id(self, shape_id): 
		self.__id = shape_id
