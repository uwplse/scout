from z3 import * 
import solver_helpers as sh
import variable as var
from dotmap import DotMap
import smtlib_builder as smt
import size_domains as sizes

TOUCH_TARGETS = ["button", "field"]
SEPARATOR_TARGETS = ["separator"]
from size_domains import COLUMNS, CANVAS_ALIGNMENT, PADDINGS, BASELINE_GRIDS, GRID_CONSTANT, CANVAS_WIDTH, CANVAS_HEIGHT

# Shape classes for constructing the element hierarchy
class Shape(object):
	def __init__(self, solver_ctx, shape_id, element, selected_layout_grid, selected_baseline_grid, shape_type, at_root=False): 
		self.shape_id = shape_id
		self.semantic_type = element["type"]
		self.element = element
		self.typed = False
		self.item = False
		self.has_baseline = False
		self.variables = DotMap() 
		self.variables.x = var.Variable(shape_id, "x")
		self.variables.y = var.Variable(shape_id, "y")
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
			self.variables.baseline = var.Variable(shape_id, "baseline")

		if "importance" in element: 
			self.importance = element["importance"]

		if "order" in element:
			self.order = element["order"]

		if "typed" in element: 
			self.typed = element["typed"]

		if "item" in element: 
			self.item = element["item"]

		if "correspondingIDs" in element: 
			self.correspondingIDs = element["correspondingIDs"]


		size_height = self.orig_height
		size_width = self.orig_width
		if "alternate" in element and element["alternate"]:
			self.is_alternate = True
			domain = element["representations"] 
			size_width = element["alternate_width"]
			size_height = element["alternate_height"]
			self.variables.alternate = var.Variable(shape_id, "alternate", domain, var_type="String", index_domain=False)
			self.search_variables.append(self.variables.alternate)

		if self.type == "leaf": 
			size_domain = []
			if self.at_root:

				if self.semantic_type in TOUCH_TARGETS or self.semantic_type in SEPARATOR_TARGETS: 
					is_sep = self.semantic_type in SEPARATOR_TARGETS
					size_domain = sizes.compute_size_domain_change_width_only_root(self.importance, size_width, size_height,
																		   selected_layout_grid, is_sep)
				else: 
					size_domain = sizes.compute_size_domain_maintain_aspect_ratio_root(self.importance, size_width, size_height,
																		   selected_layout_grid)
			else: 
				if self.semantic_type in TOUCH_TARGETS or self.semantic_type in SEPARATOR_TARGETS:
					is_sep = self.semantic_type in SEPARATOR_TARGETS
					size_domain = sizes.compute_size_domain_change_width_only(self.importance, size_width, size_height, selected_baseline_grid, is_sep)
				else: 
					size_domain = sizes.compute_size_domain_maintain_aspect_ratio(self.importance, size_width, size_height, selected_baseline_grid)
				
			# Select only a subset of the size values to search here: 
			self.variables.height = var.Variable(shape_id, "height", 
				[x[1] for x in size_domain], index_domain=False)
			self.variables.width = var.Variable(shape_id, "width", 
				[x[0] for x in size_domain], index_domain=False)
			self.variables.size_factor = var.Variable(shape_id, "size_factor",
				[x[2] for x in size_domain], index_domain=False)

			self.variables.size_combo = var.Variable(shape_id, "size_combo", 
				size_domain)
			self.search_variables.append(self.variables.size_combo)

		if at_root:
			# Add the column variable if the element is at the root of the canvas. 
			# The canvas will use this variable to place it in its correct column 
			self.has_columns = True
			self.variables.left_column = var.Variable(shape_id, "left_column", COLUMNS, index_domain=False)
			self.variables.right_column = var.Variable(shape_id, "right_column", COLUMNS, index_domain=False)
			self.variables.canvas_alignment = var.Variable(shape_id, "canvas_alignment", CANVAS_ALIGNMENT)
			self.search_variables.append(self.variables.left_column)
			self.search_variables.append(self.variables.right_column)

			# The y position should have a computed domain so they can be part of the variable search 
			# Elements at the root level of the canvas will be aligned by the baseline grid and columns
			y_domain = sizes.compute_y_domain()
			self.variables.y = var.Variable(shape_id, "y", y_domain, index_domain=False)
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
	def __init__(self, solver_ctx, shape_id, element, selected_layout_grid, selected_baseline_grid, at_root=False):
		Shape.__init__(self, solver_ctx, shape_id, element, selected_layout_grid, selected_baseline_grid, "leaf", at_root)

class ContainerShape(Shape): 
	def __init__(self, solver_ctx, shape_id, element, selected_layout_grid, selected_baseline_grid, at_root=False):
		Shape.__init__(self, solver_ctx, shape_id, element, selected_layout_grid, selected_baseline_grid, "container", at_root)
		self.children = []
		self.variables.arrangement = var.Variable(shape_id, "arrangement", 
			["horizontal", "vertical", "rows", "columns"])
		self.variables.padding = var.Variable(shape_id, "padding", 
			PADDINGS, index_domain=False)
		self.variables.alignment = var.Variable(shape_id, "alignment", ["left", "center", "right"])
		self.variables.group_alignment = var.Variable(shape_id, "group_alignment", ["left", "center", "right"])
		self.search_variables.append(self.variables.alignment)
		self.search_variables.append(self.variables.arrangement)
		self.search_variables.append(self.variables.padding)
		self.search_variables.append(self.variables.group_alignment)

		self.variables.extra_in_first = var.Variable(shape_id, "extra_in_first", var_type="Bool")
		self.variables.width = var.Variable(shape_id, "width")
		self.variables.height = var.Variable(shape_id, "height")

		self.container_order = "unimportant"
		self.container_type = "group"
		self.is_container = True
		if element is not None: 
			if "containerOrder" in element: 
				self.container_order = element["containerOrder"]
			self.container_type = element["type"]

		if self.at_root: 
			self.variables.outside_padding = var.Variable(shape_id, "outside_padding")

	def add_child(self, child): 
		self.children.append(child)

	def add_children(self, children):
		self.children.extend(children)

	def remove_child(self, child):
		self.children.remove(child)

	def num_rows_or_columns(self): 
		return 1 if len(self.children) <= 2 else 2

class CanvasShape(Shape):
	def __init__(self, solver_ctx, shape_id, element, selected_layout_grid, selected_baseline_grid):
		Shape.__init__(self, solver_ctx, shape_id, element, selected_layout_grid, selected_baseline_grid, "canvas", at_root=False)
		self.children = []

		self.variables.baseline_grid = var.Variable("canvas", "baseline_grid", selected_baseline_grid, index_domain=False)
		self.search_variables.append(self.variables.baseline_grid)

		marg_domain = [x[0] for x in selected_layout_grid]
		cols_domain = [x[1] for x in selected_layout_grid]
		gutter_domain = [x[2] for x in selected_layout_grid]
		col_width_domain = [x[3] for x in selected_layout_grid]
		self.variables.grid_layout = var.Variable("canvas", "grid_layout", selected_layout_grid)
		self.search_variables.append(self.variables.grid_layout)

		self.variables.margin = var.Variable("canvas", "margin", marg_domain, index_domain=False)
		self.variables.columns = var.Variable("canvas", "columns", cols_domain, index_domain=False)
		self.variables.gutter_width = var.Variable("canvas", "gutter_width", gutter_domain, index_domain=False) # TODO: What should the domain be? 
		self.variables.column_width = var.Variable("canvas", "column_width", col_width_domain, index_domain=False)

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