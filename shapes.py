from z3 import * 
import solver_helpers as sh
from dotmap import DotMap

label_types = ["text"]
minimum_sizes = {
	"text": 44, 
	"element": 44, 
	"group": 44
}

maximum_sizes = {
	"text": 335, 
	"element": 335, 
	"group": 335
}

# Shape classes for constructing the element hierarchy 
class Shape(object):
	def __init__(self, solver_ctx, shape_id, element, shape_type, num_siblings): 
		self.shape_id = shape_id
		self.shape_type = element["type"]
		self.element = element
		self.typed = False
		self.has_baseline = False
		self.variables = DotMap() 
		self.variables.x = sh.Variable(shape_id, "x")
		self.variables.y = sh.Variable(shape_id, "y")
		self.type = shape_type 
		self.ctx = solver_ctx
		self.locks = None
		self.order = -1
		self.importance = "normal"
		self.correspondingIDs = []

		self.variable_values = dict()

		if element is not None:
			self.x = element["x"]
			self.y = element["y"]

			if "locks" in element:
				self.locks = element["locks"]
				
				# values for locked variables
				for lock in self.locks:
					self.variable_values[lock] = element[lock]

			if "baseline" in element: 
				self.has_baseline = True
				self.orig_baseline = element["baseline"]
				self.variables.baseline = sh.Variable(shape_id, "baseline")

			if "importance" in element: 
				self.importance = element["importance"]

			if "order" in element:
				self.order = element["order"]

			if "height" in element and "width" in element:
				self.orig_width = element["width"]
				self.orig_height = element["height"]

				if self.importance == "most":
					# Make height and width into variables so that the solver can change them
					magnification_values = sh.MAGNIFICATION_VALUES
					self.variables.magnification = sh.Variable(shape_id, "magnification", 
						magnification_values, index_domain=False, var_type="Real")

				if self.importance == "least": 
					minification_values = sh.MINIFICATION_VALUES
					self.variables.minification = sh.Variable(shape_id, "minification", 
						minification_values, index_domain=False, var_type="Real")

			if "typed" in element: 
				self.typed = element["typed"]

			if "correspondingIDs" in element: 
				self.correspondingIDs = element["correspondingIDs"]


	def width(self): 
		if self.type == "container": 
			return self.variables.width.id
		return self.orig_width

	def height(self): 
		if self.type == "container": 
			return self.variables.height.id
		return self.orig_height

	def computed_width(self): 
		# Emphasis should be propagated to leaf level nodes
		if self.type == "container": 
			return self.width()

		# TAkes the current scaling value into account
		if self.importance == "most": 
			return self.width() * self.variables.magnification.name
		elif self.importance == "least": 
			return self.width() * self.variables.minification.name
		return self.width()

	def computed_height(self):
		# Emphasis should be propagated to leaf level nodes
		if self.type == "container": 
			return self.height()

		if self.importance == "most": 
			return self.height() * self.variables.magnification.name
		elif self.importance == "least": 
			return self.height() * self.variables.minification.name
		return self.height()

class LeafShape(Shape): 
	def __init__(self, solver_ctx, shape_id, element, num_siblings):
		Shape.__init__(self, solver_ctx, shape_id, element, "leaf", num_siblings)

class ContainerShape(Shape): 
	def __init__(self, solver_ctx, shape_id, element, num_siblings):
		Shape.__init__(self, solver_ctx, shape_id, element, "container", num_siblings)
		self.children = []
		self.variables.arrangement = sh.Variable(shape_id, "arrangement", 
			["horizontal", "vertical", "rows", "columns"])
		self.variables.proximity = sh.Variable(shape_id, "proximity", 
			[5,10,15,20,25,30,35,40,45,50,55,60], index_domain=False)
		self.variables.alignment = sh.Variable(shape_id, "alignment", ["left", "center", "right"])

		# TODO: Have some reasoning why we are picking this range of values
		self.variables.distribution = sh.Variable(shape_id, "distribution",
												  [20,40,60,80,100,120,140,160,180,200,220,240,
												   260,280,300,320,340,360,380,400], index_domain=False)

		self.variables.width = sh.Variable(shape_id, "width")
		self.variables.height = sh.Variable(shape_id, "height")

		self.container_order = "unimportant"
		self.container_type = "group"
		if element is not None: 
			if "containerOrder" in element: 
				self.container_order = element["containerOrder"]
			self.container_type = element["type"]

	def add_child(self, child): 
		self.children.append(child)

	def add_children(self, children):
		self.children.extend(children)

	def remove_child(self, child):
		self.children.remove(child)

	def num_rows_or_columns(self): 
		return 1 if len(self.children) <= 2 else 2

class CanvasShape(Shape):
	def __init__(self, solver_ctx, shape_id, element, num_siblings):
		Shape.__init__(self, solver_ctx, shape_id, element, "canvas", num_siblings)
		self.children = []
		self.variables.alignment = sh.Variable("canvas", "alignment", ["left", "center", "right"])
		self.variables.justification = sh.Variable("canvas", "justification", ["top", "center", "bottom"])
		self.variables.margin = sh.Variable("canvas", "margin", [5,10,20,30,40,50,60,70,80,90,100], 
			index_domain=False)
		self.variables.grid = sh.Variable("canvas", "grid", [5,8,12,16,20], index_domain=False)
		# self.variables.background_color = sh.Variable("canvas", "background_color", element["colors"], 
		# 	var_type="String", index_domain=False)

		self.x = 0
		self.y = 0

		if element is not None: 
			if "containerOrder" in element: 
				self.container_order = element["containerOrder"]

		# values for locked variables
		self.variable_values = dict()

		if self.locks is not None: 
			for lock in self.locks:
				self.variable_values[lock] = element[lock]

	def add_child(self, child): 
		self.children.append(child)

	def add_children(self, children): 
		self.children.extend(children)