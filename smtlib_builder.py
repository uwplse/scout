""" Helper methods for converting constraint expressions into SMT lib formatted strings. 
	We use this because using the Z3Py objects to create the expressions was too slow. So we built up these expressions instead
	And then call Z3 on the SMTLIB formatted string when we have built up all the expressions. 
"""
def add(x, y): 
	"""Creates an SMTLIB addition statement formatted string

	Parameters
        ----------
        x, y: float 
        	First and second numerical arguments to include in the expression 
    """
	return "(+ " + x + " " + y + ")"

def sub(x, y): 
	"""Creates an SMTLIB subtraction statement formatted string

	Parameters
        ----------
        x, y: float 
        	First and second numerical arguments to include in the expression 
    """
	return "(- " + x + " " + y + ")"

def gte(x, y): 
	"""Creates an SMTLIB greater than or equal to statement formatted string

	Parameters
        ----------
        x, y: float 
        	First and second numerical arguments to include in the expression 
    """
	return "(>= " + x + " " + y + ")"

def gt(x, y): 
	"""Creates an SMTLIB greater than statement formatted string

	Parameters
        ----------
        x, y: float 
        	First and second numerical arguments to include in the expression 
    """
	return "(> " + x + " " + y + ")"

def lte(x, y):
	"""Creates an SMTLIB less than or equal to statement formatted string

	Parameters
        ----------
        x, y: float 
        	First and second numerical arguments to include in the expression 
    """ 
	return "(<= " + x + " " + y + ")"

def lt(x, y): 
	"""Creates an SMTLIB less than statement formatted string

	Parameters
        ----------
        x, y: float 
        	First and second numerical arguments to include in the expression 
    """
	return "(< " + x + " " + y + ")"

def eq(x, y): 
	"""Creates an SMTLIB equal to statement formatted string

	Parameters
        ----------
        x, y: float 
        	First and second numerical arguments to include in the expression 
    """
	return "(= " + x + " " + y + ")"

def neq(x, y): 
	"""Creates an SMTLIB not equal to statement formatted string

	Parameters
        ----------
        x, y: float 
        	First and second numerical arguments to include in the expression 
    """
	return "(not (= " + x + " " + y + "))"

def ite(cond, x, y): 
	"""Creates an SMTLIB not equal to statement formatted string

	Parameters
        ----------
        x, y: float 
        	First and second numerical arguments to include in the expression 
    """
	return "(ite " + cond +  " " + x + " " + y + ")\n"

def div(x, y): 
	"""Creates an SMTLIB division statement formatted string

	Parameters
        ----------
        x, y: float 
        	First and second numerical arguments to include in the expression 
    """
	return "(div " + x + " " + y + ")"

def mod(x, y): 
	"""Creates an SMTLIB modulo statement formatted string

	Parameters
        ----------
        x, y: float 
        	First and second numerical arguments to include in the expression 
    """
	return "(mod " + x + " " + y + ")"

def mult(x, y):
	"""Creates an SMTLIB multiplication statement formatted string

	Parameters
        ----------
        x, y: float 
        	First and second numerical arguments to include in the expression 
    """
	return "(* " + x + " " + y + ")"

def or_expr(terms): 
	"""Creates an SMTLIB or statement formatted string

	Parameters
        ----------
        terms: A list  of float values to include in the expression
    """
	expr = "(or"
	for term in terms: 
		expr += "\n " + term
	expr += ")"
	return expr

def and_expr(terms):
	"""Creates an SMTLIB and statement formatted string

	Parameters
        ----------
        terms: A list  of float values to include in the expression
    """
	expr = "(and"
	for term in terms: 
		expr += "\n " + term
	expr += ")"
	return expr

def not_expr(term): 
	"""Creates an SMTLIB not statement formatted string

	Parameters
        ----------
        terms: A list  of float values to include in the expression
    """
	return "(not " + term + ")"

def assert_expr(term, name = ""): 
	"""Creates an SMTLIB assert stateuemnt formatted string

	Parameters
        ----------
        terms: A list  of float values to include in the expression
    """
	expr = "(assert (! " + term + "))\n"
	return expr

def declare(var_name, var_type): 
	"""Creates an SMTLIB declaration formatted string

	Parameters
        ----------
        var_name: string
        	The name of the variable
        var_type: 
        	The type of the variable (Int, Bool, etc.)
    """
	return "(declare-fun " + var_name + " () " + var_type + ")\n"