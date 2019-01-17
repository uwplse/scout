from z3 import * 
import solver_helpers as sh
from dotmap import DotMap
import smtlib_builder as smt

label_types = ["text"]

MAX_SIZE = 350
MIN_SIZE = 50
MAGNIFICATION_VALUES = [1.1,1.2,1.3,1.4,1.5,1.6,1.7,1.8,1.9,2]
MINIFICATION_VALUES = [0.1,0.2,0.3,0.4,0.5,0.6,0.7,0.8,0.9]
LAYOUT_COLUMNS = [2,3,4,6,12]
GUTTERS = [10,10,10,10,10] # TODO can introduce a variable value for these at some point
COLUMN_WIDTHS = [146,94,68,53,42,16]
COLUMNS = [1,2,3,4,5,6,7,8,9,10,11,12]

def compute_size_domain(importance, width, height): 
	domain = []
	factor_id = 0

	for i in range(0, len(MINIFICATION_VALUES)):
		if importance != "most": 
			min_value = MINIFICATION_VALUES[i] 
			computed_width = int(round(width*min_value,0))
			computed_height = int(round(height*min_value,0))
			if computed_height >= MIN_SIZE and computed_width >= MIN_SIZE: 
				domain.append([computed_width, computed_height, factor_id])
		factor_id += 1

	domain.append([width, height, factor_id])
	factor_id += 1

	for i in range(0, len(MAGNIFICATION_VALUES)):
		if importance != "least": 
			max_value = MAGNIFICATION_VALUES[i] 
			computed_width = int(round(width*max_value,0))
			computed_height = int(round(height*max_value,0))
			if computed_width <= MAX_SIZE and computed_height <= MAX_SIZE: 
				domain.append([computed_width, computed_height, factor_id])
		factor_id += 1 

	return domain

# Shape classes for constructing the element hierarchy 
class Shape(object):
	def __init__(self, solver_ctx, shape_id, element, shape_type, num_siblings, at_root=False): 
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
		self.has_columns = False
		
		self.orig_width = element["width"]
		self.orig_height = element["height"]

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

		if "typed" in element: 
			self.typed = element["typed"]

		if "correspondingIDs" in element: 
			self.correspondingIDs = element["correspondingIDs"]

		if self.type == "leaf": 
			size_domain = compute_size_domain(self.importance, self.orig_width, self.orig_height)
			self.variables.height = sh.Variable(shape_id, "height", 
				[x[1] for x in size_domain], index_domain=False)
			self.variables.width = sh.Variable(shape_id, "width", 
				[x[0] for x in size_domain], index_domain=False)
			self.variables.size_factor = sh.Variable(shape_id, "size_factor",
				[x[2] for x in size_domain], index_domain=False)


		if at_root:
			# Add the column variable if the element is at the root of the canvas. 
			# The canvas will use this variable to place it in its correct column 
			self.has_columns = True
			self.variables.column = sh.Variable(shape_id, "column", COLUMNS, index_domain=False)

	def computed_width(self): 
		if self.type == "canvas": 
			return self.orig_width
		return self.variables.width.id

	def computed_height(self):
		if self.type == "canvas": 
			return self.orig_height
		return self.variables.height.id

class LeafShape(Shape): 
	def __init__(self, solver_ctx, shape_id, element, num_siblings, at_root=False):
		Shape.__init__(self, solver_ctx, shape_id, element, "leaf", num_siblings, at_root)

class ContainerShape(Shape): 
	def __init__(self, solver_ctx, shape_id, element, num_siblings, at_root=False):
		Shape.__init__(self, solver_ctx, shape_id, element, "container", num_siblings, at_root)
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
		Shape.__init__(self, solver_ctx, shape_id, element, "canvas", num_siblings, at_root=False)
		self.children = []
		self.variables.alignment = sh.Variable("canvas", "alignment", ["left", "center", "right"])
		self.variables.justification = sh.Variable("canvas", "justification", ["top", "center", "bottom"])
		self.variables.margin = sh.Variable("canvas", "margin", [5,10,20,30,40,50,60,70,80,90,100],
			index_domain=False)
		self.variables.grid = sh.Variable("canvas", "grid", [5,8,12,16,20], index_domain=False)
		self.variables.columns = sh.Variable("canvas", "columns", LAYOUT_COLUMNS, index_domain=False)
		self.variables.gutter_width = sh.Variable("canvas", "gutter_width", GUTTERS, index_domain=False) # TODO: What should the domain be? 
		self.variables.column_width = sh.Variable("canvas", "column_width", COLUMN_WIDTHS, index_domain=False)


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