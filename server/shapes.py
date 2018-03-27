from z3 import * 
import solver_helpers as sh

# Shape classes for constructing the element hierarchy 
class Shape(object):
	def __init__(self, shape_id, element=None, locked=False, order=None): 
		self.shape_id = shape_id
		self.element = element
		self.x = sh.Variable(shape_id, "x")
		self.y = sh.Variable(shape_id, "y")
		self.locked = locked
		self.order = order

class LeafShape(Shape): 
	def __init__(self, shape_id, element, orig_bounds, locked=False, order=None): 
		Shape.__init__(self, shape_id, element, locked, order)
		self.type = "leaf"

		orig_x,orig_y,orig_width,orig_height = orig_bounds
		self.width = orig_width 
		self.height = orig_height
		self.orig_x = orig_x
		self.orig_y = orig_y

class ContainerShape(Shape): 
	def __init__(self, shape_id, element=None, locked=False, order=None): 
		Shape.__init__(self, shape_id, element, locked, order)
		self.type = "container"
		self.children = []
		self.arrangement = sh.Variable(shape_id, "arrangement", ["horizontal", "vertical"])
		self.alignment = sh.Variable(shape_id, "alignment", ["left", "center", "right"])
		self.proximity = sh.Variable(shape_id, "proximity", [10,20,30,40,50])

		# Width and Height will be adjustable for container shapes since their contents can change arrangements
		self.width = Int(shape_id + "_width")
		self.height = Int(shape_id + "_height")

	def add_child(self, child): 
		self.children.append(child)

	def remove_child(self, child):
		self.children.remove(child)

class CanvasShape(Shape):
	def __init__(self, shape_id, orig_bounds): 
		Shape.__init__(self, shape_id)
		self.children = []
		self.type = "canvas"
		self.alignment = sh.Variable("canvas", "alignment", ["left", "center", "right"])
		self.justification = sh.Variable("canvas", "justification", ["top", "center", "bottom"])

		orig_x,orig_y,orig_width,orig_height = orig_bounds
		self.width = orig_width 
		self.height = orig_height
		self.orig_x = orig_x
		self.orig_y = orig_y

	def add_child(self, child): 
		self.children.append(child)

	def add_children(self, children): 
		self.children.extend(children)