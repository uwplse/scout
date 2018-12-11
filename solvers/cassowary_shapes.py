from cassowary import Variable

# Adjustable shape position class
class Shape(object):
	def __init__(self, shape_id, json_shape=None, solver="z3"):
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
		self.adjusted_x = Variable(self.id + '_adj')
		self.adjusted_y = Variable(self.id + '_adjusted_y')
		self.adjusted_width = Variable(self.id + '_adjusted_width')
		self.adjusted_height = Variable(self.id + '_adjusted_height')

class BasicShape(object): 
	def __init__(self, shape_id, json_shape=None):
		Shape.__init__(self, shape_id, json_shape)

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


# Group shapes can have an adjustable width and height
class GroupShape(Shape): 
	def __init__(self, shape_id, json_shape=None): 
		Shape.__init__(self, shape_id, json_shape)

		# Children contained within this group
		self.children = []

		self.type = "group"
