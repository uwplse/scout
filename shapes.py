from z3 import * 
import solver_helpers as sh
from dotmap import DotMap
import smtlib_builder as smt

label_types = ["text"]

CANVAS_HEIGHT = 667
CANVAS_WIDTH = 375
MAX_WIDTH = 367 # Largest while subtracting the smallest amount of padding
MAX_HEIGHT = 659 # Largest while subtracting the smallest amount of padding
MIN_WIDTH = 48 # sort of arbitrary now, but could 
MIN_HEIGHT = 48
GRID_CONSTANT = 4
MAGNIFICATION_VALUES = [1.1,1.2,1.3,1.4,1.5,1.6,1.7,1.8,1.9,2]
MINIFICATION_VALUES = [0.1,0.2,0.3,0.4,0.5,0.6,0.7,0.8,0.9]
LAYOUT_COLUMNS = [2,3,4,6,12]
GUTTERS = [10] # TODO can introduce a variable value for these at some point
COLUMNS = [1,2,3,4,5,6,7,8,9,10,11,12]
BASELINE_GRIDS = [4,8,16]
MARGINS = [4,8,12,16,20,24,28,32,36,40,44,48,52,56,60]
PADDINGS = [4,8,12,16,20,24,28,32,36,40]

def compute_y_domain(): 
	y_values = range(0, CANVAS_HEIGHT)
	y_values = [y for y in y_values if y > 0 and (y % GRID_CONSTANT) == 0]
	return y_values

def compute_layout_grid_domains(): 
	# We precompute these values all ahead of time to avoid
	# needing to use multiplication or division in the solver as 
	# the performance generally tends to be slow for these operators
	domain = []
	for margin_value in MARGINS: 
		for column_value in COLUMNS: 
			for gutter_value in GUTTERS: 
				column_width = (CANVAS_WIDTH - (2*margin_value) - ((column_value-1)*gutter_value))/column_value
				column_width = int(round(column_width,0))
				domain.append([margin_value, column_value, gutter_value, column_width])

	return domain

def compute_size_domain(importance, width, height): 
	domain = []
	factor_id = 0
	aspect_ratio = width/height

	for i in range(0, len(MINIFICATION_VALUES)):
		if importance != "high": 
			min_value = MINIFICATION_VALUES[i] 
			computed_height = int(round(height*min_value,0))

			height_diff = computed_height % GRID_CONSTANT 
			computed_height -= height_diff

			# Compute width as a function of height
			computed_width = computed_height * aspect_ratio
			computed_width = int(round(computed_width,0))

			if computed_height >= MIN_HEIGHT and computed_width >= MIN_WIDTH: 
				domain.append([computed_width, computed_height, factor_id])

		factor_id += 1

	height_diff = height % GRID_CONSTANT
	squared_height = height - height_diff 
	squared_width = squared_height * aspect_ratio
	squared_width = int(round(squared_width,0))
	domain.append([squared_width, squared_height, factor_id])

	factor_id += 1

	for i in range(0, len(MAGNIFICATION_VALUES)):
		if importance != "low": 
			max_value = MAGNIFICATION_VALUES[i] 
			computed_height = int(round(height*max_value,0))

			height_diff = computed_height % GRID_CONSTANT 
			computed_height -= height_diff

			# Compute width as a function of height
			computed_width = computed_height * aspect_ratio
			computed_width = int(round(computed_width,0))

			if computed_width <= MAX_WIDTH and computed_height <= MAX_HEIGHT: 
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
		self.prevents = None
		self.order = -1
		self.importance = "normal"
		self.correspondingIDs = []
		self.variable_values = dict()
		self.has_columns = False
		self.is_container = False
		self.at_root = at_root
		self.is_alternate = False
		
		self.orig_width = element["orig_width"]
		self.orig_height = element["orig_height"]

		if "locks" in element:
			self.locks = element["locks"]
			
			# values for locked variables
			for lock in self.locks:
				self.variable_values[lock] = element[lock]

		if "prevents" in element: 
			self.prevents = element["prevents"]

			for prev in self.prevents: 
				self.variable_values[prev] = element[prev]

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


		size_height = self.orig_height
		size_width = self.orig_width
		if "alternate" in element and element["alternate"]:
			self.is_alternate = True
			domain = element["representations"] 
			size_width = element["alternate_width"]
			size_height = element["alternate_height"]
			self.variables.alternate = sh.Variable(shape_id, "alternate", domain)

		if self.type == "leaf": 
			size_domain = compute_size_domain(self.importance, size_width, size_height)
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

			# The y position should have a computed domain so they can be part of the variable search 
			# Elements at the root level of the canvas will be aligned by the baseline grid and columns
			y_domain = compute_y_domain()
			self.variables.y = sh.Variable(shape_id, "y", y_domain, index_domain=False)

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
		self.variables.padding = sh.Variable(shape_id, "padding", 
			PADDINGS, index_domain=False)
		self.variables.alignment = sh.Variable(shape_id, "alignment", ["left", "center", "right"])
		self.variables.width = sh.Variable(shape_id, "width")
		self.variables.height = sh.Variable(shape_id, "height")

		self.container_order = "unimportant"
		self.container_type = "group"
		self.is_container = True
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

		self.variables.baseline_grid = sh.Variable("canvas", "baseline_grid", BASELINE_GRIDS, index_domain=False)

		layout_grid_domains = compute_layout_grid_domains()
		marg_domain = [x[0] for x in layout_grid_domains]
		cols_domain = [x[1] for x in layout_grid_domains]
		gutter_domain = [x[2] for x in layout_grid_domains]
		col_width_domain = [x[3] for x in layout_grid_domains]
		self.variables.margin = sh.Variable("canvas", "margin", marg_domain, index_domain=False)
		self.variables.columns = sh.Variable("canvas", "columns", cols_domain, index_domain=False)
		self.variables.gutter_width = sh.Variable("canvas", "gutter_width", gutter_domain, index_domain=False) # TODO: What should the domain be? 
		self.variables.column_width = sh.Variable("canvas", "column_width", col_width_domain, index_domain=False)
		self.min_spacing = str(GRID_CONSTANT)
		self.is_container = True

		self.x = 0
		self.y = 0
		self.orig_width = CANVAS_WIDTH
		self.orig_height = CANVAS_HEIGHT

		if element is not None: 
			if "containerOrder" in element: 
				self.container_order = element["containerOrder"]

	def add_child(self, child): 
		self.children.append(child)

	def add_children(self, children): 
		self.children.extend(children)