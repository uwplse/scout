import random

# Constants that Scout uses to compute domains for element sizes. 
CANVAS_HEIGHT = 640
CANVAS_WIDTH = 360
CANVAS_ALIGNMENT = ["left", "center", "right", "other"]
MAX_WIDTH = 360 # Largest while subtracting the smallest amount of padding
MAX_HEIGHT = 640 # Largest while subtracting the smallest amount of padding
MIN_WIDTH = 12 # sort of arbitrary now, but could 
MIN_HEIGHT = 12
MIN_WIDTH_TOUCH_TARGET = 120
MIN_WIDTH_SEPARATOR = 24
MIN_HEIGHT_ASPECT_RATIO = 16
GRID_CONSTANT = 4
SNAP_GRID_CONSTANT = 16
MAGNIFICATION_VALUES = [1.1,1.2,1.3,1.4,1.5,1.6,1.7,1.8,1.9,2]
MINIFICATION_VALUES = [0.1,0.2,0.3,0.4,0.5,0.6,0.7,0.8,0.9]
LAYOUT_COLUMNS = [2,3,4,6]
GUTTERS = [4,8,16] 
COLUMNS = [1,2,3,4,5,6,7,8,9,10,11,12]
BASELINE_GRIDS = [4,8,16]
MARGINS = [0,4,8,12,16,20,24,28,32,36,40]
PADDINGS = [4,8,12,16,20,24,28,32,36,40,44,48,52,56,60,64,68,72,76,80,84,88,92,96,100]
LAYOUT_GRID_PROPERTIES = ["margin", "columns", "column_width", "gutter_width"]
SIZE_PROPERTIES = ["width", "height", "size_factor"]

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

def baseline_grid_consistent_with_prevents(baseline_grid, element, at_root=False):
	""" Checks whether the baseline grid is not prevented by the locks an on element """
	if "prevents" in element and "baseline_grid" in element["prevents"]: 
		bg_value = element["prevented_values"]["baseline_grid"]
		if baseline_grid in bg_value: 
			return False
	return True

def is_consistent_with_prevents(layout_grid, element, at_root=False):
	""" Checks whether the layout grid is not prevented by the locks on an element """
	if "prevents" in element: 
		for prevent in element["prevents"]: 
			if prevent in LAYOUT_GRID_PROPERTIES: 
				if prevent == "margin": 
					margin_value = element["prevented_values"]["margin"]
					for marg_value in margin_value: 
						if layout_grid[0] == marg_value: 
							return False

				if prevent == "columns": 
					columns_value = element["prevented_values"]["columns"]
					for col_value in columns_value: 
						if layout_grid[1] == col_value: 
							return False

				if prevent == "gutter_width": 
					gutter_width_value = element["prevented_values"]["gutter_width"]
					for gut_value in gutter_width_value: 
						if layout_grid[2] == gut_value: 
							return False

				if prevent == "column_width": 
					column_width_value = element["prevented_values"]["column_width"]
					for col_width_value in column_width_value: 
						if layout_grid[3] == col_width_value: 
							return False

	return True

def baseline_grid_consistent_with_locks(baseline_grid, element, at_root=False): 
	# Check if the baseline grid is consistent with the locks on the element
	if "locks" in element: 
		for lock in element["locks"]: 
			if lock == "size":
				print(element["locked_values"]["size"])
				# Consistency of the height values with the baseline grid value 
				size = element["locked_values"]["size"]
				for size_val in size: 
					height_val = size_val[1]
					if height_val % baseline_grid != 0: 
						return False	

			if lock == "baseline_grid": 
				bg_value = element["locked_values"]["baseline_grid"]
				if baseline_grid not in bg_value: 
					return False
	return True

def is_consistent_with_locks(layout_grid, element, at_root=False): 
	""" Checks whether a layout grid is consistesnt with locks on an element. """
	margin = layout_grid[0]
	columns = layout_grid[1]
	gutter_width = layout_grid[2]
	column_width = layout_grid[3] 

	# Check if the layout grid combination is consistent with the locks on the element
	if "locks" in element: 
		for lock in element["locks"]: 
			if lock == "size" and at_root:
				# Consistency of the width values with the margins 
				size_values = element["locked_values"]["size"]
				cons = False
				width_values = []
				for size_value in size_values: 
					width_value = size_value[0]
					width_values.append(width_value)
					if width_value <= (CANVAS_WIDTH  -  margin * 2): 
						cons = True

				if not cons: 
					return False

				cons = False
				cols = 1
				while cols <= columns: 
					width = column_width * cols + (gutter_width * (cols-1))
					if width in width_values: 
						cons = True
					cols += 1

				if not cons: 
					return False

			# TODO - check consistency of height values wrt width values in columns
			if lock in LAYOUT_GRID_PROPERTIES: 
				if lock == "margin": 
					margin_value = element["locked_values"]["margin"]
					matches = False
					for marg_value in margin_value: 
						if layout_grid[0] == marg_value:
							matches = True
					if not matches: 
						return False 

				if lock == "columns": 
					columns_value = element["locked_values"]["columns"]
					matches = False
					for col_value in columns_value: 
						if layout_grid[1] == col_value: 
							matches = True
					if not matches: 
						return False 

				if lock == "gutter_width": 
					gutter_width_value = element["locked_values"]["gutter_width"]
					matches = False
					for gut_value in gutter_width_value: 
						if layout_grid[2] == gut_value: 
							matches = True
					if not matches: 
						return False 

				if lock == "column_width": 
					column_width_value = element["locked_values"]["column_width"]
					matches = False
					for col_width_value in column_width_value: 
						if layout_grid[3] == col_width_value: 
							matches = True
					if not matches: 
						return False 
	return True

def grid_consistent_with_element_locks(layout_grid, element_tree, at_root=False): 
	""" Checks whether a layout grid value is consistent with locks on elements in the element tree """
	cons = is_consistent_with_locks(layout_grid, element_tree, at_root)
	if not cons: 
		return False

	cons = is_consistent_with_prevents(layout_grid, element_tree, at_root)
	if not cons: 
		return False

	if "children" in element_tree: 
		for child in element_tree["children"]: 
			at_root = element_tree["type"] == "canvas"
			cons = grid_consistent_with_element_locks(layout_grid, child, at_root)
			if not cons:
				return False

	return True

def baseline_grid_consistent_with_element_locks(baseline_grid, element_tree, at_root=False): 
	""" Checks whether a baseline grid value is consistent with locks on elements in the element tree """
	cons = baseline_grid_consistent_with_locks(baseline_grid, element_tree, at_root)
	if not cons: 
		return False

	cons = baseline_grid_consistent_with_prevents(baseline_grid, element_tree, at_root)
	if not cons: 
		return False

	if "children" in element_tree: 
		for child in element_tree["children"]: 
			at_root = element_tree["type"] == "canvas"
			cons = baseline_grid_consistent_with_element_locks(baseline_grid, child, at_root)
			if not cons:
				return False

	return True

def select_consistent_layout_grid(element_tree): 
	""" Selects a layout grid value to use based on the current set of element locks """
	layout_grids = compute_layout_grid_domains()
	filtered_grids = []
	for grid in layout_grids:
		if grid_consistent_with_element_locks(grid, element_tree):
			filtered_grids.append(grid)

	# Now, randomly sample one to use
	if len(filtered_grids):
		selected_grid = random.sample(filtered_grids, 1)
		return selected_grid
	else:
		# Return any grid if we could not select a consistent one
		selected_grid = random.sample(layout_grids, 1)
		return selected_grid

def select_consistent_baseline_grid(element_tree): 
	"""Select a consistent baseline grid with the values that are locked"""
	filtered_grids = []
	for grid in BASELINE_GRIDS:
		if baseline_grid_consistent_with_element_locks(grid, element_tree):
			filtered_grids.append(grid)

	# Now, randomly sample one to use
	if len(filtered_grids):
		selected_grid = random.sample(filtered_grids, 1)
		return selected_grid
	else:
		# Return any grid if we could not select a consistent one
		selected_grid = random.sample(BASELINE_GRIDS, 1)
		return selected_grid

def get_layout_grids():
	"""Return the full set of layout grids"""
	layout_grids = compute_layout_grid_domains()
	return layout_grids

def compute_size_domain_change_width_only_root(importance, width, height, layout_grids, is_separator=False): 
	""" Computes the size domain a priori for elements that will change their width only and are 
		also located on the root of the tree. 

		Attributes: 
			importance: Current emphasis value 
			width: original width 
			height: original height 
			layout_grids: possible set of layout grids that we will compute the sizes from. Root elements have to be placed on a column. 
	"""
	# For touch targets, the calcuated sizes should only 
	# increase/decrease the width (buttons, fields) 
	domain = []
	factor_id = 0

	# First, round the values down to a mult of the grid constant
	orig_height = height
	orig_width = width 
	if not is_separator: 
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
				# if (width_value > width and importance != "low") or (width_value <= width and importance != "high"):
				hw_values = [width_value, orig_height]
				if hw_values not in domain:
					domain.append([width_value, orig_height])
					factor_id += 1
			num_columns += 1

	domain_with_factor = []
	for i in range(0, len(domain)): 
		domain_with_factor.append([domain[i][0], domain[i][1], i])
	return domain_with_factor

def compute_size_domain_maintain_aspect_ratio_root(importance, width, height, layout_grids):
	""" Computes the size domain a priori for elements that will change width and height to maintain their aspect ratio. 
		also located on the root of the tree. 

		Attributes: 
			importance: Current emphasis value 
			width: original width 
			height: original height 
			layout_grids: possible set of layout grids that we will compute the sizes from. Root elements have to be placed on a column. 
	"""
	# For touch targets, the calcuated sizes should only
	# increase/decrease the width (buttons, fields)
	domain = []
	factor_id = 0

	# First, round the values down to a mult of the grid constant
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
			if width_value <= MAX_WIDTH \
					and height_value >= MIN_HEIGHT_ASPECT_RATIO and height_value <= MAX_HEIGHT:
				# if (width_value >= width and importance != "low") or (width_value <= width and importance != "high"):
				hw_values = [width_value, height_value]
				if hw_values not in domain:
					domain.append(hw_values)
					factor_id += 1
			num_columns += 1

	domain_with_factor = []
	for i in range(0, len(domain)):
		domain_with_factor.append([domain[i][0], domain[i][1], i])
	return domain_with_factor

def compute_size_domain_change_width_only(importance, width, height, baseline_grid, is_separator=False): 
	""" Computes the size domain a priori for elements that will change their width only, and are 
		not located on the root of the tree. 

		Attributes: 
			importance: Current emphasis value 
			width: original width 
			height: original height 
			layout_grids: possible set of layout grids that we will compute the sizes from. Root elements have to be placed on a column. 
	"""
	# For touch targets, the calcuated sizes should only 
	# increase/decrease the width (buttons, fields) 
	domain = []
	factor_id = 0

	# First, round the values down to a mult of the grid constant
	grid = baseline_grid[0] if len(baseline_grid) > 0 else GRID_CONSTANT
	orig_height = height
	orig_width = width 
	if not is_separator: 
		height_diff = height % grid
		orig_height = height -  height_diff
		orig_height = orig_height if orig_height > SNAP_GRID_CONSTANT else SNAP_GRID_CONSTANT
	
	width_diff = width % GRID_CONSTANT
	orig_width = width - width_diff

	domain.append([orig_width, orig_height, factor_id])

	computed_width = orig_width
	minimum_element_width = MIN_WIDTH_SEPARATOR if is_separator else MIN_WIDTH_TOUCH_TARGET
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

def get_nearest_grid_size(size, grid): 

	floor_grid = (size // grid) * grid
	ceil_grid = floor_grid + grid
	return (ceil_grid if size - floor_grid >= ceil_grid - size else floor_grid)

def compute_size_domain_maintain_aspect_ratio(importance, width, height, baseline_grid):
	""" Computes the size domain a priori for elements that will change their width and height in order
		to maintain their aspect ratio, and are not located on the root of the tree. 

		Attributes: 
			importance: Current emphasis value 
			width: original width 
			height: original height 
			layout_grids: possible set of layout grids that we will compute the sizes from. Root elements have to be placed on a column. 
	""" 
	domain = []
	factor_id = 0
	aspect_ratio = width/height

	# First, round the values down to a mult of the grid constant
	# height_diff = height % SNAP_GRID_CONSTANT
	grid = baseline_grid[0] if len(baseline_grid) == 1 else GRID_CONSTANT
	orig_height = get_nearest_grid_size(height, SNAP_GRID_CONSTANT)
	orig_height = orig_height if orig_height > SNAP_GRID_CONSTANT else SNAP_GRID_CONSTANT

	orig_width = orig_height * aspect_ratio
	orig_width = int(round(orig_width, 0))
	width_diff = orig_width % 2
	orig_width = orig_width - width_diff

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

				computed_height -= grid
				computed_width = computed_height * aspect_ratio
				computed_width = int(round(computed_width, 0))
				width_diff = computed_width % 2
				computed_width = computed_width - width_diff

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

				computed_height += grid
				computed_width = computed_height * aspect_ratio
				computed_width = int(round(computed_width, 0))
				width_diff = computed_width % 2
				computed_width = computed_width - width_diff

				if computed_width <= maximum_element_width and computed_height <= maximum_element_height: 
					domain.append([computed_width, computed_height, increase_factor_id])

	return domain