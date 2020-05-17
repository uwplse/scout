import size_constraint_helpers 

class Columnizer(object): 
	def __init__(self):
		""" Class to create constraints for rows and column behavior 
		""" 
		self.constraints = ""

	def balanced_row_column_arrangement(self, is_rows, is_columns, container, rows_index, columns_index, spacing):
		# Columns/Rows arrangement constraints
		# Only apply if there are > 2 children elements
		arrangement = container.variables.arrangement
		extra_in_first = container.variables.extra_in_first

		if len(container.children) > 2:
			num_children_even = len(container.children) % 2 == 0
			if num_children_even: 
				groups = self.split_children_into_groups(container, True)
				constraints = self.row_column_layout(is_rows, is_columns, groups, container, spacing)
				self.constraints += cb.assert_expr(cb.and_expr(constraints), "container_" + container.shape_id + "_rows_columns")
			else: 
				print("Rows and columns!!")
				groups_one = self.split_children_into_groups(container, True)
				const1 = self.row_column_layout(is_rows,  is_columns, groups_one, container, spacing, "1")

				groups_two = self.split_children_into_groups(container, False) 
				const2 = self.row_column_layout(is_rows,  is_columns, groups_two, container, spacing, "2")

				self.constraints += cb.assert_expr(cb.ite(extra_in_first.id, cb.and_expr(const1), cb.and_expr(const2)), "container_" + container.shape_id + "_rows_columns")
		else:
			# Prevent columnns and rows variables if there are 2 children or less
			self.constraints += cb.assert_expr(cb.neq(arrangement.id, str(rows_index)), 
				"container_" + container.shape_id + "_arrangement_neq_rows")
			self.constraints += cb.assert_expr(cb.neq(arrangement.id, str(columns_index)), 
				"container_" + container.shape_id + "_arrangement_neq_columns")


	def row_column_layout(self, is_rows, is_columns, groups, container, spacing, id_str=""): 
		""" Perform either row or column layout """
		row_column_constraints = []
		row_column_constraints.append(cb.ite(is_rows, self.align_rows_or_columns(container, spacing, groups, "row", "y", "height", "x", "width"), "true"))
		row_column_constraints.append(cb.ite(is_columns, self.align_rows_or_columns(container, spacing, groups, "column", "x", "width", "y", "height"), "true"))
		row_column_constraints.append(cb.ite(is_rows, self.align_left_or_top(groups, spacing, "row", "x", "y", "height"), "true"))
		row_column_constraints.append(cb.ite(is_columns, self.align_left_or_top(groups, spacing, "column", "y", "x", "width"), "true"))
		row_column_constraints.append(cb.ite(is_rows, self.set_container_size_main_axis(container, spacing, groups, "height"), "true"))
		row_column_constraints.append(cb.ite(is_columns, self.set_container_size_main_axis(container, spacing, groups, "width"), "true"))
		row_column_constraints.append(cb.ite(is_rows, self.set_container_size_cross_axis(container, spacing, groups, "width"), "true"))
		row_column_constraints.append(cb.ite(is_columns, self.set_container_size_cross_axis(container, spacing, groups, "height"), "true"))
		return row_column_constraints

	def set_container_size_main_axis(self, container, padding, rows_or_columns, width_or_height):
		""" Constraint for the main axis size of the container """ 
		size = ""
		num_rows_or_columns = len(rows_or_columns)
		outside_padding = container.variables.outside_padding.id if container.at_root else "0"
		for i in range(0, num_rows_or_columns):
			row_or_column = rows_or_columns[i]
			if len(row_or_column):
				spacing = padding if i < num_rows_or_columns - 1 else 0
				m_height_or_width = None
				if width_or_height == "width": 
					m_height_or_width = size_constraint_helpers.get_max_width_constraint(1,0,row_or_column)
				else: 
					m_height_or_width = size_constraint_helpers.get_max_height_constraint(1,0,row_or_column)
				
				if len(size): 
					size = cb.add(size, cb.add(m_height_or_width, str(spacing)))
				else: 
					size = cb.add(m_height_or_width, str(spacing))

		container_size = cb.add(cb.mult("2", outside_padding), str(container.computed_width())) if width_or_height == "width" else str(container.computed_height())
		return cb.eq(container_size, size)

	def set_container_size_cross_axis(self, container, padding, rows_or_columns, width_or_height):
		""" Constraint for the cross axis size of the container """
		outside_padding = container.variables.outside_padding.id if container.at_root else "0"
		size = self.get_widest_row_constraint(1, 0, rows_or_columns, padding) if width_or_height == "width" else self.get_tallest_column_constraint(1, 0, rows_or_columns, padding)
		container_size = cb.add(cb.mult("2", outside_padding), str(container.computed_width())) if width_or_height == "width" else str(container.computed_height())
		return cb.eq(container_size, size)

	def split_children_into_groups(self, container, extra_in_first):  
		""" Columnize child elements of container before building constraints on each column """
		num_rows = container.num_rows_or_columns()
		child_shapes = container.children
		
		num_in_first = 0
		num_in_second = 0
		if extra_in_first: 
			num_in_first = math.ceil(len(child_shapes)/2)
			num_in_second = math.floor(len(child_shapes)/2) 
		else: 
			num_in_first = math.floor(len(child_shapes)/2) 
			num_in_second = math.ceil(len(child_shapes)/2)

		rows = []
		num_in_row = 0
		child_index = 0
		first_row = []
		while num_in_row < num_in_first: 
			first_row.append(child_shapes[child_index])
			num_in_row += 1
			child_index += 1

		second_row = []
		num_in_row = 0
		while num_in_row < num_in_second:
			second_row.append(child_shapes[child_index])
			num_in_row += 1
			child_index += 1
		rows.append(first_row)
		rows.append(second_row)
		return rows

	def align_left_or_top(self, rows, padding, column_or_row, aligned_axis, below_or_right_axis, width_or_height):
		""" Align columns or rows to the left or top edge """
		constraints = []
		for i in range(0, len(rows)-1):
			row1 = rows[i] 
			row2 = rows[i+1]
			if len(row1) > 0 and len(row2) > 0: 
				shape1 = row1[0]
				shape2 = row2[0]

				# Width or height of shape1 
				w_or_h = str(shape1.computed_width()) if width_or_height == "width" else str(shape1.computed_height())

				# Shape1 row is left or top aligned to shape2 row
				constraints.append(cb.eq(shape1.variables[aligned_axis].id, shape2.variables[aligned_axis].id))

				# shape2 row is below or to the right of shape1 row
				constraints.append(cb.lte(cb.add(shape1.variables[below_or_right_axis].id, cb.add(w_or_h, padding)), shape2.variables[below_or_right_axis].id))
		if len(constraints):
			return cb.and_expr(constraints)
		return True


	def align_rows_or_columns(self, container, padding, rows, column_or_row,
							  aligned_axis, aligned_axis_size, layout_axis, layout_axis_size):
		""" Align rows or columns elements with a column or row to the alignment of the parent container """
		constraints = []
		l_index = container.variables.alignment.domain.index("left")
		c_index = container.variables.alignment.domain.index("center")
		is_left = cb.eq(container.variables.alignment.id, str(l_index))
		is_center = cb.eq(container.variables.alignment.id, str(c_index))

		for row in rows: 
			for i in range(len(row)-1): 
				shape1 = row[i]
				shape2 = row[i+1]

				aligned_axis_size_value = str(shape1.computed_width()) if aligned_axis_size == "width" else str(shape1.computed_height())
				aligned_axis_size_value2 = str(shape2.computed_width()) if aligned_axis_size == "width" else str(shape2.computed_height())

				left_top_aligned = cb.eq(shape1.variables[aligned_axis].id, shape2.variables[aligned_axis].id)
				right_bottom_aligned = cb.eq(cb.add(shape1.variables[aligned_axis].id, aligned_axis_size_value), 
					cb.add(shape2.variables[aligned_axis].id, aligned_axis_size_value2))
				center_aligned = cb.eq(cb.add(shape1.variables[aligned_axis].id, cb.div(aligned_axis_size_value, "2")), 
					cb.add(shape2.variables[aligned_axis].id, cb.div(aligned_axis_size_value2, "2")))

				constraints.append(cb.ite(is_left, left_top_aligned, 
					cb.ite(is_center, center_aligned, right_bottom_aligned)))

				# Shape 2 is exactly to the right of shape 1 or to the bottom if in a column 
				layout_axis_size_value = str(shape1.computed_width()) if layout_axis_size == "width" else str(shape1.computed_height())
				constraints.append(cb.eq(cb.add(shape1.variables[layout_axis].id, cb.add(layout_axis_size_value, padding)), 
					shape2.variables[layout_axis].id))

		if len(constraints):
			return cb.and_expr(constraints)
		return True

	def get_row_width(self, row, spacing):
		""" Constraint to compute the width of a row, including spacing (margin) """
		width = ""
		for i in range(0, len(row)):
			if i < len(row) - 1:
				if len(width): 
					width = cb.add(width, cb.add(str(row[i].computed_width()), str(spacing)))
				else: 
					width = cb.add(str(row[i].computed_width()), str(spacing))
			else:
				if len(width): 
					width = cb.add(width, str(row[i].computed_width()))
				else: 
					width = str(row[i].computed_width())
		return width

	def get_column_height(self, column, spacing):
		""" Constraint to compute the height of a column, including spacing (margin) """
		height = ""
		for i in range(0, len(column)):
			if i < len(column) - 1:
				if len(height): 
					height = cb.add(height, cb.add(str(column[i].computed_height()), str(spacing)))
				else: 
					height = cb.add(str(column[i].computed_height()), str(spacing))
			else:
				if len(height): 
					height = cb.add(height, str(column[i].computed_height()))
				else: 
					height = str(column[i].computed_height())
		return height

	def get_widest_row_constraint(self, row_i, widest_i, rows, spacing):
		""" Constraint to compute the widest row in a row arranged container, 
			which will be used to set the width on the parent container """ 
		widest_row = rows[widest_i]
		widest_row_width = self.get_row_width(widest_row, spacing)

		if row_i < len(rows):
			next_row = rows[row_i]
			next_row_width = self.get_row_width(next_row, spacing)
			return cb.ite(cb.gt(widest_row_width, next_row_width), 
				self.get_widest_row_constraint(row_i+1, widest_i, rows, spacing), 
				self.get_widest_row_constraint(row_i+1, row_i, rows, spacing))
		else:
			return widest_row_width

	def get_tallest_column_constraint(self, column_i, tallest_i, columns, spacing):
		""" Constraint to compute the tallest column in a column arranged container, 
			which will be used to set the height on the parent container """
		tallest_column = columns[tallest_i]
		tallest_column_height = self.get_column_height(tallest_column, spacing)
		if column_i < len(columns):
			next_column = columns[column_i]
			next_column_height = self.get_column_height(next_column, spacing)
			return cb.ite(cb.gt(tallest_column_height, next_column_height), 
				self.get_tallest_column_constraint(column_i+1, tallest_i, columns, spacing), 
				self.get_tallest_column_constraint(column_i+1, column_i, columns, spacing))
		else:
			return tallest_column_height