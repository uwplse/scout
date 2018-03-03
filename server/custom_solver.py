import jsonpickle
# What will we be solving for? 

# Steps
# 1. Design constructs initial design sketch
# 2. Designer creates initial set of constraints with relationships 
# 3. Solve


# What are the constraints? 
# Related Groups
# Related Collections
# Labels
# Captions
# Headers --> maybe
# Footers --> maybe
# Global -> No overlapping, no out of bounds

# What can we change just with labels relationship? 
# Labels 
# 	E1/G1 labels E2/G2
#   Element or group 1 labels element or group 2
#   Positions of the label: Top-Left, Center, Top-Right, Left
# 	Proximity of the label: GLOBAL value --> we should get this from somewhere

# Elements - N elements 
# Variables: X, Y, Width, Height, Position of the label (top-left, center, top-right,  left)
# The canvas
# - The overall layout canvas is an element that has constraints on alignment (left, center, right)
# Variables: Alignment (l,c,r)
# Arrangement: Vertical 
# Order unimportant -- Need to generate all of the possible orders  


# What positions make sense? 
	# The element is aligned to other elements on the page 
	# Or aligned globally (Left, Center, Right) or vertical position 

# Just one element (no changing size)
# Variables: X, Y
# Canvas Variables: Alignment, Justification
# Alignment values: Left, Center, Right
# Justification values: Top, Bottom, Center 

class Shape(object):
	def __init__(self, shape_id, width, height): 
		self.shape_id = shape_id
		self.width = width 
		self.height = height
		self.x = 0
		self.y = 0
		self.children = []

	def x(self, x): 
		self.x = x_val 

	def y(self, y): 
		self.y = y_val 

	def add_child(self, child): 
		self.children.append(child)

class Variable(object): 
	def __init__(self, shape_id, name, domain): 
		self.shape_id = shape_id
		self.name = name
		self.assigned = None
		self.domain = domain

	def domain(self, domain): 
		self.domain = domain

	def assign(self, value): 
		self.assigned = value

class Solution(object): 
	def __init__(self): 
		self.variables = []

	def add_assigned_variable(self, variable): 
		self.variables.append(variable)

	def convert_to_json(self, shapes): 
		for variable in self.variables: 
			if variable.shape_id == "canvas":
				shapes[variable.shape_id].x = 0
				shapes[variable.shape_id].y = 0
				for child in shapes[variable.shape_id].children: 
					if variable.name == "alignment": 
						if variable.assigned == "right": 
							child.x = shapes[variable.shape_id].width - child.width
						elif variable.assigned == "center": 
							child.x = shapes[variable.shape_id].width/2 - child.width/2
						else: 
							child.x = 0

					if variable.name == "justification": 
						if variable.assigned == "top": 
							child.y = 0
						elif variable.assigned == "center": 
							child.y = shapes[variable.shape_id].height/2 - child.height/2
						else: 
							child.y = shapes[variable.shape_id].height - child.height

		return jsonpickle.encode(shapes)

class Solver(object): 
	def __init__(self, shapes): 
		self.solutions = [] # Initialize the variables somewhere
		self.unassigned = []
		self.shapes = shapes

	def solve(self, variables): 
		self.unassigned = variables
		self.branch_and_bound()

	def select_next_variable(self):
		return self.unassigned.pop()

	def restore_variable(self, variable): 
		variable.assigned = None
		self.unassigned.append(variable)

	def branch_and_bound(self, state=Solution()): 
		# Dumb this down so we are not optimizing for the cost right now
		# State keeps track of the variables assigned so far
		if len(self.unassigned) == 0: 
			# Keep the solution 
			sln = state.convert_to_json(self.shapes)
			self.solutions.append(sln)
			return 
		else: 
			# Selects the next variable to assign
			next_var = self.select_next_variable()
			for value in next_var.domain: 
				next_var.assigned = value
				state.add_assigned_variable(next_var)
				self.branch_and_bound(state)

			# Then unassign the value
			self.restore_variable(next_var)
		return 

if __name__ == "__main__":
    # with open('specification/with_labels.json') as data_file:
    #     shapes = json.load(data_file)
    shapes = dict() 
    child1 = Shape("child1", 50, 50)
    shapes["child1"] = child1
    canvas = Shape("canvas", 375, 667)
    canvas.add_child(child1)
    shapes["canvas"] = canvas

    # Create some variables
    var1 = Variable("canvas", "alignment", ["left", "right", "center"])
    var2 = Variable("canvas", "justification", ["top", "bottom", "center"])
    variables = []
    variables.append(var1)
    variables.append(var2)
    solver = Solver(shapes)
    solver.solve(variables)

    # for shape_key, shape in shapes.items(): 
    # 	print("-----------------")
    # 	print(shape.shape_id)
    # 	print(shape.x, shape.y, shape.width, shape.height)

    for sln in solver.solutions: 
    	print(sln)









