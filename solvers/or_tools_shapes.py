from ortools.constraint_solver import pywrapcp

# Adjustable shape position class
class Shape(object):
	def __init__(self, solver, shape_id, json_shape=None, dims=[]):
		self.id = shape_id
		self.importance = None
		self.size_adjustable = False
		self.json_shape = None

		if json_shape is not None: 
			self.json_shape = json_shape
			if "importance" in self.json_shape: 
				self.importance = self.json_shape["importance"]

			if self.importance == "most" or self.importance == "least": 
				self.size_adjustable = True

		# Adjusted values are Z3 variables
		max_width = 200
		max_height = 200
		if len(dims):
			max_width,max_height = dims

		self.adjusted_x = solver.IntVar(0, max_width, self.id + '_adjusted_x')
		self.adjusted_y = solver.IntVar(0, max_height, self.id + '_adjusted_y')
		self.adjusted_width = solver.IntVar(10, max_width, self.id + '_adjusted_width')
		self.adjusted_height = solver.IntVar(10, max_height, self.id + '_adjusted_height')

class BasicShape(object): 
	def __init__(self, solver, shape_id, json_shape=None, dims=[]):
		Shape.__init__(self, solver, shape_id, json_shape, dims)

		self.tag = None
		self.effect = None
		self.locked = False

		if json_shape is not None: 
			self.type = self.json_shape["type"]
			self.orig_width = self.json_shape["size"]["width"]
			self.orig_height = self.json_shape["size"]["height"] 
			self.orig_x = self.json_shape["location"]["x"]
			self.orig_y = self.json_shape["location"]["y"]

			# Tag
			if "tag" in self.json_shape: 
				self.tag = self.json_shape["tag"]

			# Effect
			if "effect" in self.json_shape: 
				self.effect = self.json_shape["effect"]

			if "locked" in self.json_shape: 
				self.locked = self.json_shape["locked"]

			# Set the current values to the original values to start
			# These are used to keep track of the current value of the variable after solving
			self.curr_x = self.orig_x
			self.curr_y = self.orig_y 
			self.curr_width = self.orig_width
			self.curr_height = self.orig_height

# Group shapes can have an adjustable width and height
class GroupShape(Shape): 
	def __init__(self, solver, shape_id, json_shape=None, dims=[]): 
		Shape.__init__(self, solver, shape_id, json_shape, dims)

		# Children contained within this group
		self.children = []

		# Arrangement - Horizontal (True) or Vertical (False)
		self.arrangement = solver.BoolVar(self.id + '_arrangement')

		self.vertical_alignments = ['left', 'right', 'x-center']
		self.horizontal_alignments = ['top', 'bottom', 'y-center']
		# self.alignment = Int(self.id + '_alignment')

		self.type = "group"
