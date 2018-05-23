from z3 import * 
import solver_helpers as sh
from dotmap import DotMap

# Types of shapes that have labels
label_types = ["label", "button", "field"]

# Shape classes for constructing the element hierarchy 
class Shape(object):
	def __init__(self, shape_id, element): 
		self.shape_id = shape_id
		self.shape_type = element["type"]
		self.element = element
		self.variables = DotMap() 
		self.variables.x = sh.Variable(shape_id, "x")
		self.variables.y = sh.Variable(shape_id, "y")

		if self.shape_type in label_types:
			self.variables.label = sh.Variable(shape_id, "label", varType="str")

		self.order = "important"
		self.locks = None

		self.variable_values = dict()
		if element is not None:
			if "locks" in element:
				self.locks = element["locks"]
				
				# values for locked variables
				for lock in self.locks:
					if lock == "label": 
						self.variable_values[lock] = StringVal(element[lock])
					elif lock != "location":  
						# Keep track of the actual value of the locked property on the container instance so we can set the constraint later
						self.variable_values[lock] = element[lock]

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

	def add_child(self, child): 
		self.children.append(child)

	def add_children(self, children):
		self.children.extend(children)

	def remove_child(self, child):
		self.children.remove(child)

class CanvasShape(Shape):
	def __init__(self, shape_id, element): 
		Shape.__init__(self, shape_id, element)
		self.children = []
		self.type = "canvas"
		self.variables.alignment = sh.Variable("canvas", "alignment", ["left", "center", "right"])
		self.variables.justification = sh.Variable("canvas", "justification", ["top", "center", "bottom"])
		self.variables.margin = sh.Variable("canvas", "margin", [10,20,30,40,50])
		self.orig_x = 0
		self.orig_y = 0

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