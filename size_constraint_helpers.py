def get_max_width_constraint(child_i, widest_i, child_shapes): 
	""" Get the width value of the widest element in a set of shapes (child_shapes) """
	if child_i < len(child_shapes): 
		widest_child = child_shapes[widest_i]
		widest_child_width = str(widest_child.computed_width())

		next_child = child_shapes[child_i]
		next_child_width = str(next_child.computed_width())
		return cb.ite(cb.gt(widest_child_width, next_child_width),
			get_max_width_constraint(child_i+1, widest_i, child_shapes), 
			get_max_width_constraint(child_i+1, child_i, child_shapes))
	else: 
		child_shape_width = str(child_shapes[widest_i].computed_width())
		return child_shape_width

def get_min_width_constraint(child_i, thinnest_i, child_shapes): 
	""" Get the width value of the smallest width element in a set of shapes (child_shapes) """
	if child_i < len(child_shapes): 
		thinnest_child = child_shapes[thinnest_i]
		thinnest_child_width = str(thinnest_child.computed_width())

		next_child = child_shapes[child_i]
		next_child_width = str(next_child.computed_width())
		return cb.ite(cb.lt(thinnest_child_width, next_child_width),
			get_min_width_constraint(child_i+1, thinnest_i, child_shapes),
			get_max_width_constraint(child_i+1, child_i, child_shapes))
	else: 
		child_shape_width = str(child_shapes[thinnest_i].computed_width())
		return child_shape_width

def get_max_height_constraint(child_i, tallest_i, child_shapes): 
	""" Get the height value of the tallest element in a set of shapes (child_shapes) """
	if child_i < len(child_shapes): 
		tallest_child = child_shapes[tallest_i]
		tallest_child_height = str(tallest_child.computed_height())

		next_child = child_shapes[child_i]
		next_child_height = str(next_child.computed_height())
		return cb.ite(cb.gt(tallest_child_height, next_child_height),
			get_max_height_constraint(child_i+1, tallest_i, child_shapes), 
			get_max_height_constraint(child_i+1, child_i, child_shapes))
	else: 
		child_shape_height = str(child_shapes[tallest_i].computed_height())
		return child_shape_height

def get_min_height_constraint(child_i, shortest_i, child_shapes): 
	""" Get the height value of the smallest height element in a set of shapes (child_shapes) """
	if child_i < len(child_shapes): 
		shortest_child = child_shapes[shortest_i]
		shortest_child_height = str(shortest_child.computed_height())

		next_child = child_shapes[child_i]
		next_child_height = str(next_child.computed_height())
		return cb.ite(cb.lt(shortest_child_height, next_child_height),
			get_max_height_constraint(child_i+1, shortest_i, child_shapes), 
			get_max_height_constraint(child_i+1, child_i, child_shapes))
	else: 
		child_shape_height = str(child_shapes[shortest_i].computed_height())
		return child_shape_height