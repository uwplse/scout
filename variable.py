class Variable(object):
	def __init__(self, shape_id, name, domain=[], index_domain=True, var_type="Int"):
		self.shape_id = shape_id
		self.name = name
		self.id = name + "_" + shape_id
		self.assigned = None
		self.domain = domain
		self.type = var_type

		# If this is true, the domain values produced by the solver `
		# map directly to the indexes of the variables in the list
		# If it is false, the domain values the solver produces
		# will be the actual numerical or string values from the domain
		self.index_domain = index_domain

	def domain(self, domain): 
		self.domain = domain

	def assign(self, value): 
		self.assigned = value

	def get_value_from_element(self, element):
		# Return a Z3 expression or value to use in Z3 expressions from the element
		value = element[self.name]
		if self.type == "String":
			return "\"" + value + "\""
		return value