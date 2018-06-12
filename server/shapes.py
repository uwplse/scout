from z3 import * 
import solver_helpers as sh
from dotmap import DotMap

# Types of shapes that have labels
label_types = ["label", "button", "field"]
minimum_sizes = {
	"label": 11, 
	"image": 44,
	"field": 44
}

maximum_sizes = {
	"image": 335, # Need to tweak later
	"label": 36,
	"field": 335
}

# Shape classes for constructing the element hierarchy 
class Shape(object):
	def __init__(self, shape_id, element, shape_type, num_siblings): 
		self.shape_id = shape_id
		self.shape_type = element["type"]
		self.element = element
		self.typed = False
		self.importance_set = False
		self.variables = DotMap() 
		self.variables.x = sh.Variable(shape_id, "x")
		self.variables.y = sh.Variable(shape_id, "y")
		self.type = shape_type

		if self.shape_type in label_types:
			self.variables.label = sh.Variable(shape_id, "label", varType="str")

		# self.variables.row = sh.Variable(shape_id, "row", [sh.get_row_column_values(num_siblings)])
		# self.variables.column = sh.Variable(shape_id, "columns", [sh.get_row_column_values(num_siblings)])

		self.locks = None
		self.order = -1
		self.importance = "normal"
		self.correspondingIDs = []

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

			if "importance" in element: 
				self.importance = element["importance"]
				self.importance_set = True

			if "order" in element:
				self.order = element["order"]

			if "size" in element:
				self.orig_width = element["size"]["width"]
				self.orig_height = element["size"]["height"]

				if self.importance == "most":
					# Make height and width into variables so that the solver can change them
					magnification_values = sh.MAGNIFICATION_VALUES
					self.variables.magnification = sh.Variable(shape_id, "magnification", magnification_values)

				if self.importance == "least": 
					minification_values = sh.MAGNIFICATION_VALUES
					self.variables.minification = sh.Variable(shape_id, "minification", minification_values)

			if "location" in element:
				self.orig_x = element["location"]["x"]
				self.orig_y = element["location"]["y"]

			if "typed" in element: 
				self.typed = element["typed"]

			if "correspondingIDs" in element: 
				self.correspondingIDs = element["correspondingIDs"]


	def width(self): 
		if self.type == "container": 
			return self.flex_width
		return self.orig_width

	def height(self): 
		if self.type == "container": 
			return self.flex_height
		return self.orig_height


	def computed_width(self): 
		# TAkes the current scaling value into account
		if self.importance_set: 
			if self.importance == "most": 
				return self.width() + ((1/self.variables.magnification.z3) * self.width())
			elif self.importance == "least": 
				return self.width() - ((1/self.variables.minification.z3) * self.width())
		return self.width()

	def computed_height(self, scale=1): 
		if self.importance_set: 
			if self.importance == "most": 
				return self.height() + ((1/self.variables.magnification.z3) * self.height())
			elif self.importance == "least": 
				return self.height() - ((1/self.variables.minification.z3) * self.height())
		return self.height()

class LeafShape(Shape): 
	def __init__(self, shape_id, element, num_siblings): 
		Shape.__init__(self, shape_id, element, "leaf", num_siblings)

class ContainerShape(Shape): 
	def __init__(self, shape_id, element, num_siblings): 
		Shape.__init__(self, shape_id, element, "container", num_siblings)
		self.children = []
		self.variables.arrangement = sh.Variable(shape_id, "arrangement", ["horizontal", "vertical"])
		self.variables.proximity = sh.Variable(shape_id, "proximity", [10,20,30,40,50])
		self.variables.alignment = sh.Variable(shape_id, "alignment", ["left", "center", "right"])

		# TODO: Have some reasoning why we are picking this range of values
		self.variables.distribution = sh.Variable(shape_id, "distribution", [20,40,60,80,100,120,140,160,180,200])

		self.container_order = "unimportant"
		if element is not None: 
			if "containerOrder" in element: 
				self.container_order = element["containerOrder"]

		# Width and Height for container is determined by their contents so allow these values to change
		self.flex_width = Int(shape_id + "_width")
		self.flex_height = Int(shape_id + "_height")

	def add_child(self, child): 
		self.children.append(child)

	def add_children(self, children):
		self.children.extend(children)

	def remove_child(self, child):
		self.children.remove(child)
		

class CanvasShape(Shape):
	def __init__(self, shape_id, element, num_siblings): 
		Shape.__init__(self, shape_id, element, "canvas", num_siblings)
		self.children = []
		self.variables.alignment = sh.Variable("canvas", "alignment", ["left", "center", "right"])
		self.variables.justification = sh.Variable("canvas", "justification", ["top", "center", "bottom"])
		self.variables.margin = sh.Variable("canvas", "margin", [10,20,30,40,50])
		self.orig_x = 0
		self.orig_y = 0

		self.container_order = "unimportant"
		if element is not None: 
			if "containerOrder" in element: 
				self.container_order = element["containerOrder"]

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