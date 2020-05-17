import random 
from size_domains import LAYOUT_GRID_PROPERTIES, SIZE_PROPERTIES, BASELINE_GRIDS

DOMAIN_SIZE_REDUCTION = 4

class DomainReducer(object): 
	def __init__(self, shapes):
		""" Class to reduce the domain sizes of the variable values based on already selected layout grids and domains 
			Removes inconsistent values before starting the search process. 

			Attributes: 
				shapes: The shape hierarchy 
		""" 
		self.shapes = shapes 

	def prune_container_child_sizes(self, container):
		""" For a given container, prune size variables to reduce the search space """ 
		groups = dict()
		for child in container.children:
			if child.semantic_type != "group" or child.is_alternate:
				if child.semantic_type not in groups:
					groups[child.semantic_type] = []

				groups[child.semantic_type].append(child)

		# Prune/reduce the size of the domain for size_factor and size variables to reduce the search space 
		for key,group_children in groups.items():
			size_factors = [set(child.variables.size_factor.domain) for child in group_children if child.type == "leaf"]
			size_factors = list(set.intersection(*size_factors)) if len(size_factors) else size_factors

			# Further reduce the size of the domain
			if len(size_factors) > 0:
				if len(size_factors) > DOMAIN_SIZE_REDUCTION:
					num_to_select = int(len(size_factors)/DOMAIN_SIZE_REDUCTION)
					if num_to_select > 0:
						size_factors = random.sample(size_factors, num_to_select)

				for child in group_children:
					if child.type == "leaf": 
						size_combos = [val for val in child.variables.size_combo.domain if val[2] in size_factors]

						child.variables.size_combo.domain = size_combos
						child.variables.size_factor.domain = [val[2] for val in size_combos]
						child.variables.width.domain = [val[0] for val in size_combos]
						child.variables.height.domain = [val[1] for val in size_combos]

		# # Further reduce the size of the domain
		# if len(size_factors) > 0:
		# 	if len(size_factors) > DOMAIN_SIZE_REDUCTION:
		# 		num_to_select = int(len(size_factors)/DOMAIN_SIZE_REDUCTION)
		# 		if num_to_select > 0:
		# 			size_factors = random.sample(size_factors, num_to_select)

		# 	for child in container.children:
		# 		if child.type == 'leaf':
		# 			size_combos = [val for val in child.variables.size_combo.domain if val[2] in size_factors]

		# 			child.variables.size_combo.domain = size_combos
		# 			child.variables.size_factor.domain = [val[2] for val in size_combos]
		# 			child.variables.width.domain = [val[0] for val in size_combos]
		# 			child.variables.height.domain = [val[1] for val in size_combos]

	def prune_repeat_group_child_sizes(self, container): 
		""" For a given repeat group, prune the child size domains to reduce the search space """ 
		if len(container.children): 
			first_item = container.children[0]

			# Prune the domains for the first group randomly. 
			# Then apply the domains to the corresponding children 
			self.prune_container_child_sizes(first_item)

			if len(first_item.children): 
				for item_child in first_item.children: 
					# Update the size domains on the coreesponding shapes 
					item_corresponding_ids = item_child.correspondingIDs
					for corresponding_child_id in item_corresponding_ids: 
						corresponding_child_shape = self.shapes[corresponding_child_id]

						size_combos = corresponding_child_shape.variables.size_combo.domain
						size_combos_filtered = [combo for combo in size_combos if combo[2] in item_child.variables.size_factor.domain]

						corresponding_child_shape.variables.size_combo.domain = size_combos_filtered
						corresponding_child_shape.variables.size_factor.domain = [combo[2] for combo in size_combos]
						corresponding_child_shape.variables.width.domain = [combo[0] for combo in size_combos]
						corresponding_child_shape.variables.height.domain = [combo[1] for combo in size_combos]

	def prune_size_domains(self): 
		""" Prune the size domains for repeat group children and container children to reduce the search space. """ 
		for shape in self.shapes.values(): 
			if shape.type == "container" and not shape.item:
				if shape.typed: 
					# Prune domain for child elements
					# based on the size_factor values of each 
					# to ensure that the rules are maintained regarding child 
					# sizing. (Increase/Decrease size of elements with same semantic type proporotionally)
					self.prune_repeat_group_child_sizes(shape)
				else: 
					# Prune domain for child elements
					# based on the size_factor values of each 
					# to ensure that the rules are maintained regarding child 
					# sizing. (Increase/Decrease size of elements with same semantic type proporotionally)
					self.prune_container_child_sizes(shape)

	def prune_layout_grid_domains(self): 
		""" Randomly select a subset of the search space to search to find a 
		    design in this iteration. For performance. 
		    Prune based on variable values selected intelligently """ 
		canvas_shape = self.shapes["canvas"]

		# Select a baseline grid, and remove child variable values based on the selected baseline grid. 
		# BAsed on the baseline grid chosen. 
		baseline_grid = canvas_shape.variables.baseline_grid
		selected_grid = random.choice(baseline_grid.domain)
		canvas_shape.variables.baseline_grid.domain = [selected_grid]

		for shape in self.shapes.values(): 
			if shape.type == "leaf": # Only prune for leaf node shapes as groups size is a function of the child layout
				if not shape.at_root:
					height = shape.variables.height
					width = shape.variables.width
					size_factor = shape.variables.size_factor
					size_combo = shape.variables.size_combo

					size_combos = [val for val in size_combo.domain if val[1] % selected_grid == 0]
					if len(size_combos) > 0:
						# Prune the pre-computed size values based on the selected baseline grid 
						size_combo.domain = size_combos
						height.domain = [val[1] for val in size_combos]
						width.domain = [val[0] for val in size_combos]
						size_factor.domain = [val[2] for val in size_combos]

				# Prune the y-coordinate values by the selected baseline grid
				if shape.at_root:
					y = shape.variables.y
					y_values = [val for val in y.domain if val % selected_grid == 0]
					y.domain = y_values

		# Prune left column and right column values based on the selected number of columns. 
		columns = canvas_shape.variables.columns
		max_cols = max(columns.domain)
		for shape in self.shapes.values(): 
			if shape.at_root: # It should have the column variable if it is on the root of the canvas
				left_column = shape.variables.left_column
				left_column_pruned = [val for val in left_column.domain if val <= max_cols]
				left_column.domain = left_column_pruned

				right_column = shape.variables.right_column
				right_column_pruned = [val for val in right_column.domain if val <= max_cols]
				right_column.domain = right_column_pruned

	def prune_size_variable_domains_for_locks(self): 
		""" Prune size variable domains based on which variable values have locks/keeps. If those values or fixed, the domain can 
			be pruned entirely just to the fixed value. """ 
		for shape in self.shapes.values():
			if shape.locks is not None:
				for lock in shape.locks:
					locked_values = shape.keep_values[lock]
					if lock in SIZE_PROPERTIES: 					
						locked_index = SIZE_PROPERTIES.index(lock)

						size_combo_domain = shape.variables["size_combo"].domain
						pruned_size = [val for val in size_combo_domain if val[locked_index] in locked_values]

						shape.variables["size_combo"].domain = pruned_size

						width_domain = [val[0] for val in pruned_size]
						shape.variables["width"].domain = width_domain

						height_domain = [val[1] for val in pruned_size]
						shape.variables["height"].domain = height_domain

						size_factor_domain = [val[0] for val in pruned_size]
						shape.variables["size_factor"].domain = size_factor_domain 

			if shape.prevents is not None: 
				for prevent in shape.prevents: 
					prevented_values = shape.prevent_values[prevent]
					if prevent in SIZE_PROPERTIES:
						prev_index = SIZE_PROPERTIES.index(prevent)

						size_combo_domain = shape.variables["size_combo"].domain
						pruned_size_combos = [val for val in size_combo_domain if val[prev_index] not in prevented_values]
						if len(pruned_size_combos) > 1: 
							shape.variables["size_combo"].domain = pruned_size_combos

							width_domain = [val[0] for val in pruned_size_combos]
							shape.variables["width"].domain = width_domain

							height_domain = [val[1] for val in pruned_size_combos]
							shape.variables["height"].domain = height_domain

							size_factor_domain = [val[2] for val in pruned_size_combos]
							shape.variables["size_factor"].domain = size_factor_domain
