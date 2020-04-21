class Variable(object):
	def __init__(self, shape_id, name, domain=[], index_domain=True, var_type="Int"):
		""" Class for representing a Z3 variable. 
      
	    Attributes: 
	        shape_id: ID of shape the variable is associated with 
	        name: Name of the variable 
	        id: Variable ID to give it a unique ID in the SMT lib constraints
	        assigned: Holds the assigned value if the variable is currently assigned 
	        domain: Values the variable can be assigned 
	        type: Variable type - e.g., Bool, Int, Real, etc. 
	    """
		self.shape_id = shape_id
		self.name = name
		self.id = name + "_" + shape_id
		self.assigned = None
		self.domain = domain
		self.type = var_type

		# If this is true, the domain values produced by the solver `
		# map to indices in the domain list, from which the actual values will be retrieved. This is 
		# used in the case of variables where the domain consists of strings ["vertical", "horizontal"]. 

		# If it is false, the domain values the solver assigns to the variable
		# will be the actual numerical or string values from the domain
		self.index_domain = index_domain

	def domain(self, domain): 
		""" Sets the variable's domain"""
		self.domain = domain

	def assign(self, value): 
		""" Assigns a value to the variable """
		self.assigned = value

	def get_value_from_element(self, element):
		""" Return a Z3 expression or value to use in Z3 expressions from the element 

			Parameters: 
				element: The element object to retrieve the current value of the variable from
        ----------
        """
		if self.name in element: 
			value = element[self.name]
			if self.type == "String":
				return "\"" + value + "\""
			return value
		return None