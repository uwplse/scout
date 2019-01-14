def add(x, y): 
	return "(+ " + x + " " + y + ")"

def sub(x, y): 
	return "(- " + x + " " + y + ")"

def gte(x, y): 
	return "(>= " + x + " " + y + ")"

def gt(x, y): 
	return "(> " + x + " " + y + ")"

def lte(x, y): 
	return "(<= " + x + " " + y + ")"

def lt(x, y): 
	return "(< " + x + " " + y + ")"

def eq(x, y): 
	return "(= " + x + " " + y + ")"

def neq(x, y): 
	return "(not (= " + x + " " + y + "))"

def ite(cond, x, y): 
	return "(ite " + cond +  " " + x + " " + y + ")\n"

def div(x, y): 
	return "(div " + x + " " + y + ")"

def or_expr(terms): 
	expr = "(or"
	for term in terms: 
		expr += "\n " + term
	expr += ")"
	return expr

def and_expr(terms):
	expr = "(and"
	for term in terms: 
		expr += "\n " + term
	expr += ")"
	return expr

def not_expr(term): 
	return "(not " + term + ")"

def assert_expr(term, name = ""): 
	# Creates an implication for the label
	# expr = "(declare-fun " + name + " () Bool)\n" 
	# expr += "(assert (= " + name + " true))\n"
	expr = "(assert (! " + term + "))\n"
	return expr

def declare(var_name, var_type): 
	return "(declare-fun " + var_name + " () " + var_type + ")\n"