from z3 import * 
import solver_helpers as sh
from dotmap import DotMap

# Shape classes for constructing the element hierarchy 
class Shape(object):
	def __init__(self, shape_id, element=None): 
		self.shape_id = shape_id
		self.element = element
		self.variables = DotMap() 
		self.variables.x = sh.Variable(shape_id, "x")
		self.variables.y = sh.Variable(shape_id, "y")

		self.order = "important"
		self.locks = None

		if element is not None:
			if "locks" in element:
				self.locks = element["locks"]

			if "order" in element:
				self.order = element["order"]

			if "size" in element:
				self.width = element["size"]["width"]
				self.height = element["size"]["height"]

			if "location" in element:
				self.orig_x = element["location"]["x"]
				self.orig_y = element["location"]["y"]

class LeafShape(Shape): 
	def __init__(self, shape_id, element): 
		Shape.__init__(self, shape_id, element)
		self.type = "leaf"

class ContainerShape(Shape): 
	def __init__(self, shape_id, element=None): 
		Shape.__init__(self, shape_id, element)
		self.type = "container"
		self.children = []
		self.variables.arrangement = sh.Variable(shape_id, "arrangement", ["horizontal", "vertical"])
		self.variables.proximity = sh.Variable(shape_id, "proximity", [10,20,30,40,50])
		self.variables.alignment = sh.Variable(shape_id, "alignment", ["left", "center", "right"])

		# Width and Height will be adjustable for container shapes since their contents can change arrangements
		self.width = Int(shape_id + "_width")
		self.height = Int(shape_id + "_height")

		# values for locked variables
		self.variable_values = dict()

		if self.locks is not None: 
			for lock in self.locks:
				# Keep track of the actual value of the locked property on the container instance so we can set the constraint later
				self.variable_values[lock] = element[lock]

	def add_child(self, child): 
		self.children.append(child)

	def add_children(self, children):
		self.children.extend(children)

	def remove_child(self, child):
		self.children.remove(child)

class CanvasShape(Shape):
	def __init__(self, shape_id, width, height): 
		Shape.__init__(self, shape_id)
		self.children = []
		self.type = "canvas"
		self.variables.alignment = sh.Variable("canvas", "alignment", ["left", "center", "right"])
		self.variables.justification = sh.Variable("canvas", "justification", ["top", "center", "bottom"])

		self.width = width
		self.height = width
		self.orig_x = 0
		self.orig_y = 0

	def add_child(self, child): 
		self.children.append(child)

	def add_children(self, children): 
		self.children.extend(children)