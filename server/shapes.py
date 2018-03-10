from z3 import * 
import solver_helpers as sh

# Shape classes for constructing the element hierarchy 
class Shape(object):
	def __init__(self, shape_id, width, height): 
		self.type = "leaf"
		self.shape_id = shape_id
		self.width = width 
		self.height = height
		self.x = sh.Variable(shape_id, "x")
		self.y = sh.Variable(shape_id, "y")

class ContainerShape(Shape): 
	def __init__(self, shape_id, width=0, height=0): 
		Shape.__init__(self, shape_id, width, height)
		self.type = "container"
		self.children = []
		self.arrangement = sh.Variable(shape_id, "arrangement", ["vertical", "horizontal"])
		self.alignment = sh.Variable(shape_id, "alignment", ["left", "center", "right"])
		self.proximity = sh.Variable(shape_id, "proximity", [10,20,30])

		# Width and Height will be adjustable for container shapes since their contents can change arrangements
		self.width = Int(shape_id + "_width")
		self.height = Int(shape_id + "_height")

	def add_child(self, child): 
		self.children.append(child)

	def remove_child(self, child):
		self.children.remove(child)

class CanvasShape(Shape):
	def __init__(self, shape_id, width, height): 
		Shape.__init__(self, shape_id, width, height)
		self.children = []
		self.type = "canvas"
		self.alignment = sh.Variable("canvas", "alignment", ["left", "center", "right"])
		self.justification = sh.Variable("canvas", "justification", ["top", "center", "bottom"])
		self.orig_x = 0
		self.orig_y = 0

	def add_child(self, child): 
		self.children.append(child)

	def add_children(self, children): 
		self.children.extend(children)