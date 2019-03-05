from z3 import * 
import solver_helpers as sh
from dotmap import DotMap
import smtlib_builder as smt

label_types = ["text"]


TOUCH_TARGETS = ["button", "field"]
CANVAS_HEIGHT = 640
CANVAS_WIDTH = 360
MAX_WIDTH = 356 # Largest while subtracting the smallest amount of padding
MAX_HEIGHT = 636 # Largest while subtracting the smallest amount of padding
MIN_WIDTH = 48 # sort of arbitrary now, but could 
MIN_WIDTH_TOUCH_TARGET = 120
MIN_HEIGHT_ASPECT_RATIO = 24
GRID_CONSTANT = 4
MAGNIFICATION_VALUES = [1.1,1.2,1.3,1.4,1.5,1.6,1.7,1.8,1.9,2]
MINIFICATION_VALUES = [0.1,0.2,0.3,0.4,0.5,0.6,0.7,0.8,0.9]
LAYOUT_COLUMNS = [2,3,4,6]
GUTTERS = [4,8,16] # TODO can introduce a variable value for these at some point
COLUMNS = [1,2,3,4,5,6,7,8,9,10,11,12]
BASELINE_GRIDS = [4,8,16]
# MARGINS = [4,8,12,16,20,24,28,32,36,40,44,48,52,56,60]
MARGINS = [4,8,12,16,20,24,28,32,36,40]
# PADDINGS = [4,8,12,16,20,24,28,32,36,40,44,48,52,56,60,64,68,72,76,80,84,88,92,96,100]
PADDINGS = [4,8,12,16,20,24,28,32,36,40,44,48,52,56,60]

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
		for column_value in LAYOUT_COLUMNS:
			for gutter_value in GUTTERS: 
				column_width = float((CANVAS_WIDTH - (2*margin_value) - ((column_value-1)*gutter_value)))/float(column_value)
				int_column_width = int(round(column_width,0))
				if column_width - int_column_width == 0: 
					domain.append([margin_value, column_value, gutter_value, int_column_width])

	return domain

def compute_size_domain_touch_target_at_root(importance, width, height, layout_grids): 
	# For touch targets, the calcuated sizes should only 
	# increase/decrease the width (buttons, fields) 
	domain = []
	factor_id = 0

	# First, round the values down to a mult of the grid constant
	height_diff = height % GRID_CONSTANT
	orig_height = height -  height_diff
	orig_width = width 

	for grid in layout_grids: 
		margin = grid[0]
		columns = grid[1]
		gutter_width = grid[2]
		column_width = grid[3] 

		num_columns = 1
		while num_columns <= columns: 
			width_value = (column_width * num_columns) + (gutter_width * (num_columns-1))
			if width_value >= MIN_WIDTH_TOUCH_TARGET and width_value <= MAX_WIDTH: 
				if (width_value > width and importance != "low") or (width_value <= width and importance != "high"):
					hw_values = [width_value, orig_height]
					if hw_values not in domain:
						domain.append([width_value, orig_height])
						factor_id += 1
			num_columns += 1

	domain_with_factor = []
	for i in range(0, len(domain)): 
		domain_with_factor.append([domain[i][0], domain[i][1], i])
	return domain_with_factor

def compute_size_domain_aspect_ratio_at_root(importance, width, height, layout_grids):
	# For touch targets, the calcuated sizes should only
	# increase/decrease the width (buttons, fields)
	domain = []
	factor_id = 0
	aspect_ratio = height/width

	for grid in layout_grids:
		margin = grid[0]
		columns = grid[1]
		gutter_width = grid[2]
		column_width = grid[3]

		num_columns = 1
		while num_columns <= columns:
			width_value = (column_width * num_columns) + (gutter_width * (num_columns-1))
			height_value = int(width_value * aspect_ratio)
			if width_value >= MIN_WIDTH_TOUCH_TARGET and width_value <= MAX_WIDTH \
					and height_value >= MIN_HEIGHT_ASPECT_RATIO and height_value <= MAX_HEIGHT:
				if (width_value > width and importance != "low") or (width_value <= width and importance != "high"):
					hw_values = [width_value, height_value]
					if hw_values not in domain:
						domain.append(hw_values)
						factor_id += 1
			num_columns += 1

	domain_with_factor = []
	for i in range(0, len(domain)):
		domain_with_factor.append([domain[i][0], domain[i][1], i])
	return domain_with_factor

def compute_size_domain_touch_target(importance, width, height): 
	# For touch targets, the calcuated sizes should only 
	# increase/decrease the width (buttons, fields) 
	domain = []
	factor_id = 0

	# First, round the values down to a mult of the grid constant
	height_diff = height % GRID_CONSTANT
	orig_height = height -  height_diff
	
	width_diff = width % GRID_CONSTANT
	orig_width = width - width_diff

	domain.append([orig_width, orig_height, factor_id])

	computed_width = orig_width
	minimum_element_width = MIN_WIDTH_TOUCH_TARGET
	shrink_factor_id = 0

	if importance != "high": 
		while computed_width > minimum_element_width: 
				shrink_factor_id -= 1

				computed_width -= GRID_CONSTANT
				if computed_width >= minimum_element_width: 
					domain.append([computed_width, orig_height, shrink_factor_id])

	computed_width = orig_width
	increase_factor_id = 0
	maximum_element_width = MAX_WIDTH
	if importance != "low": 
		while computed_width < maximum_element_width: 
				increase_factor_id += 1

				computed_width += GRID_CONSTANT
				if computed_width <= maximum_element_width: 
					domain.append([computed_width, orig_height, increase_factor_id])

	return domain	

def compute_size_domain_maintain_aspect_ratio(importance, width, height): 
	domain = []
	factor_id = 0
	aspect_ratio = width/height

	# First, round the values down to a mult of the grid constant
	height_diff = height % GRID_CONSTANT
	orig_height = height -  height_diff

	orig_width = orig_height * aspect_ratio
	orig_width = int(round(orig_width, 0))

	domain.append([orig_width, orig_height, factor_id])

	computed_height = orig_height
	computed_width = orig_width

	# Don't reduce height greater than half from the original 
	# minimum_element_height = MIN_HEIGHT if MIN_HEIGHT > (orig_height/2) else (orig_height/2)
	# minimum_element_width = MIN_WIDTH if MIN_WIDTH > (orig_width/2)  else (orig_width/2)
	minimum_element_height = MIN_HEIGHT_ASPECT_RATIO
	minimum_element_width = MIN_WIDTH
	shrink_factor_id = 0

	if importance != "high": 
		while computed_height > minimum_element_height and computed_width > minimum_element_width: 
				shrink_factor_id -= 1

				computed_height -= GRID_CONSTANT
				computed_width = computed_height * aspect_ratio
				computed_width = int(round(computed_width, 0))

				if computed_height >= minimum_element_height and computed_width >= minimum_element_width: 
					domain.append([computed_width, computed_height, shrink_factor_id])

	computed_width = orig_width
	computed_height = orig_height
	increase_factor_id = 0

	# maximum_element_height = MAX_HEIGHT if MAX_HEIGHT < (orig_height * 2) else (orig_height * 2)
	# maximum_element_width = MAX_WIDTH if MAX_WIDTH < (orig_width * 2) else (orig_width * 2)
	maximum_element_height = MAX_HEIGHT
	maximum_element_width = MAX_WIDTH
	if importance != "low": 
		while computed_width < maximum_element_width and computed_height < maximum_element_height: 
				increase_factor_id += 1

				computed_height += GRID_CONSTANT
				computed_width = computed_height * aspect_ratio
				computed_width = int(round(computed_width, 0))

				if computed_width <= maximum_element_width and computed_height <= maximum_element_height: 
					domain.append([computed_width, computed_height, increase_factor_id])

	return domain

# Shape classes for constructing the element hierarchy 
class Shape(object):
	def __init__(self, solver_ctx, shape_id, element, shape_type, num_siblings, at_root=False): 
		self.shape_id = shape_id
		self.semantic_type = element["type"]
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
		self.prevent_values = dict()
		self.keep_values = dict()
		self.has_columns = False
		self.is_container = False
		self.at_root = at_root
		self.is_alternate = False
		self.search_variables = []
		
		self.orig_width = element["orig_width"]
		self.orig_height = element["orig_height"]

		if "locks" in element:
			self.locks = element["locks"]
			
			# values for locked variables
			for lock in self.locks:
				self.keep_values[lock] = element["locked_values"][lock]

		if "prevents" in element: 
			self.prevents = element["prevents"]

			for prev in self.prevents: 
				self.prevent_values[prev] = element["prevented_values"][prev]

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
			self.variables.alternate = sh.Variable(shape_id, "alternate", domain, var_type="String", index_domain=False)
			self.search_variables.append(self.variables.alternate)

		if self.type == "leaf": 
			size_domain = []
			if self.at_root:
				layout_grid_domains = compute_layout_grid_domains()
				if self.semantic_type in TOUCH_TARGETS: 
					size_domain = compute_size_domain_touch_target_at_root(self.importance, size_width, size_height,
																		   layout_grid_domains)
				else: 
					size_domain = compute_size_domain_aspect_ratio_at_root(self.importance, size_width, size_height,
																		   layout_grid_domains)
			else: 
				if self.semantic_type in TOUCH_TARGETS:
					size_domain = compute_size_domain_touch_target(self.importance, size_width, size_height)
				else: 
					size_domain = compute_size_domain_maintain_aspect_ratio(self.importance, size_width, size_height)
				
			self.variables.height = sh.Variable(shape_id, "height", 
				[x[1] for x in size_domain], index_domain=False)
			self.variables.width = sh.Variable(shape_id, "width", 
				[x[0] for x in size_domain], index_domain=False)
			self.variables.size_factor = sh.Variable(shape_id, "size_factor",
				[x[2] for x in size_domain], index_domain=False)

			self.variables.size_combo = sh.Variable(shape_id, "size_combo", 
				size_domain)
			self.search_variables.append(self.variables.size_combo)

		if at_root:
			# Add the column variable if the element is at the root of the canvas. 
			# The canvas will use this variable to place it in its correct column 
			self.has_columns = True
			self.variables.left_column = sh.Variable(shape_id, "left_column", COLUMNS, index_domain=False)
			self.variables.right_column = sh.Variable(shape_id, "right_column", COLUMNS, index_domain=False)
			self.search_variables.append(self.variables.left_column)
			self.search_variables.append(self.variables.right_column)

			# The y position should have a computed domain so they can be part of the variable search 
			# Elements at the root level of the canvas will be aligned by the baseline grid and columns
			y_domain = compute_y_domain()
			self.variables.y = sh.Variable(shape_id, "y", y_domain, index_domain=False)
			self.search_variables.append(self.variables.y)

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
		self.search_variables.append(self.variables.alignment)
		self.search_variables.append(self.variables.arrangement)
		self.search_variables.append(self.variables.padding)

		self.variables.extra_in_first = sh.Variable(shape_id, "extra_in_first", var_type="Bool")
		self.variables.width = sh.Variable(shape_id, "width")
		self.variables.height = sh.Variable(shape_id, "height")

		self.container_order = "unimportant"
		self.container_type = "group"
		self.is_container = True
		if element is not None: 
			if "containerOrder" in element: 
				self.container_order = element["containerOrder"]
			self.container_type = element["type"]

		if self.at_root: 
			self.variables.outside_padding = sh.Variable(shape_id, "outside_padding")

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
		self.search_variables.append(self.variables.baseline_grid)

		layout_grid_domains = compute_layout_grid_domains()
		marg_domain = [x[0] for x in layout_grid_domains]
		cols_domain = [x[1] for x in layout_grid_domains]
		gutter_domain = [x[2] for x in layout_grid_domains]
		col_width_domain = [x[3] for x in layout_grid_domains]
		self.variables.grid_layout = sh.Variable("canvas", "grid_layout", layout_grid_domains)
		self.search_variables.append(self.variables.grid_layout)

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