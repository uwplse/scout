from collections import namedtuple
import copy
import json
import numpy as np
import os
from pprint import pprint
import sys

from shapes import ContainerShape, CanvasShape

# import constants
from cost import CANVAS_WIDTH, CANVAS_HEIGHT
ALIGN_TOLERANCE_DELTA = 0

LeafFeature = namedtuple("LeafFeature", ["id", "x", "y", "width", "height", "component_type"])
GroupFeature = namedtuple("GroupFeature", 
	["x", "y", "width", "height", "avg_ele_width", 
	 "avg_ele_height", "area", "align_score", "balance_h", "balance_v"])

def process_element_tree(node):
	"""given a layout tree starting from node, 
		calculate tree bounds and high level features """

	# get bounds
	width = CANVAS_WIDTH if node["type"] == "canvas" else node["width"]
	height = CANVAS_HEIGHT if node["type"] == "canvas" else node["height"]
	node["bounds"] = [node["x"], node["y"], node["x"] + width, node["y"] + height]	
	
	if node["type"] == "canvas":
		children = []
		for c in node["children"]:
			if c["type"] == "group":
				_, leaves = extract_groups_and_leaves(c)
				if len(leaves) <= 1:
					children += leaves
				else:
					c["children"] = leaves
					children.append(c)
			else:
				children.append(c)
		node["children"] = children

	# add id for each node
	if node["type"] in ["canvas", "group"]:
		for c in node["children"]:
			process_element_tree(c)

def extract_groups_and_leaves(node):
	"""get all groups and leaves from the tree"""
	groups, leaves = [], []
	if node["type"] in ["canvas", "group"]:
		groups += [node]
		for c in node["children"]:
			more_groups, more_leaves = extract_groups_and_leaves(c)
			groups += more_groups
			leaves += more_leaves
	else:
		leaves.append(node)
	return groups, leaves

def print_layout_tree(node, indent=0):
	"""render a mockup for semantic layout tree"""
	space = "".join(["  " for i in range(indent)])
	label = node["type"]
	idx = node["name"]
	# print(f"{space}{idx}:{label}")
	if node["type"] in ["canvas", "group"]:
		for c in node["children"]:
			print_layout_tree(c, indent + 1)

def print_neighborhood(neighborhood):
	for x, neighbors in neighborhood:
		ln, rn, tn, bn = neighbors
		print("{}: {} {} {} {}".format(
			str(x["name"])+x["type"],
			str(ln["name"])+ln["type"] if ln else None,
			str(rn["name"])+rn["type"] if rn else None,
			str(tn["name"])+tn["type"] if tn else None,
			str(bn["name"])+bn["type"] if bn else None))

def compute_cost(layout_tree):
	layout_tree = copy.deepcopy(layout_tree)
	process_element_tree(layout_tree)
	screen_features = extract_layout_features(layout_tree)

	weights = {
		'top_level_align_score': 1, 
		'top_level_balance_score': 1, 
		'top_level_overlapping_area': 1, 
		'avg_element_width': 1, 
		'avg_element_height': 1, 
		'avg_alignment_score': 1, 
		'density': 1, 
		'imbalance': -1
	}

	cost = sum([weights[key] * screen_features[key] for key in weights])
	
	return cost

def overlap_area(a, b):  
	# returns 0 if rectangles don't intersect
    dx = min(a[2], b[2]) - max(a[0], b[0])
    dy = min(a[3], b[3]) - max(a[1], b[1])
    return dx*dy if (dx>=0) and (dy>=0) else 0

def collect_neighbors(elements):
	"""given a list of elements, collect neighbors of all elements. """

	def get_closest(e1, neighbors, dist_func):
		if neighbors:
			return neighbors[np.argmin([dist_func(e1, e2) for e2 in neighbors])]
		else:
			return None

	neighbors = []
	for i, x in enumerate(elements):

		l_neighbors = [y for j, y in enumerate(elements) if y["bounds"][2] <=  x["bounds"][0] and y_overlap(x, y) and j != i]
		r_neighbors = [y for j, y in enumerate(elements) if y["bounds"][0] >=  x["bounds"][2] and y_overlap(x, y) and j != i]

		top_neighbors = [y for j, y in enumerate(elements) if x_overlap(x, y) and y["bounds"][3] <= x["bounds"][1] and j != i]
		bot_neighbors = [y for j, y in enumerate(elements) if x_overlap(x, y) and y["bounds"][1] >= x["bounds"][3] and j != i]

		ln = get_closest(x, l_neighbors, lambda a,b: a["bounds"][0] - b["bounds"][2])
		rn = get_closest(x, r_neighbors, lambda a, b: b["bounds"][2] - a["bounds"][0])
		tn = get_closest(x, top_neighbors, lambda a, b: a["bounds"][1] - b["bounds"][3])
		bn = get_closest(x, bot_neighbors, lambda a, b: b["bounds"][3] - a["bounds"][1])

		neighbors.append((x, [ln, rn, tn, bn]))

	return neighbors

# auxiliary functions
def range_overlap(a_min, a_max, b_min, b_max):
	return (b_min <= a_min and a_min < b_max) or (b_min < a_max and a_max <= b_max)

def x_overlap(e1, e2):
	return range_overlap(e1["bounds"][0], e1["bounds"][2], e2["bounds"][0], e2["bounds"][2])

def y_overlap(e1, e2):
	return range_overlap(e1["bounds"][1], e1["bounds"][3], e2["bounds"][1], e2["bounds"][3])

def collect_neighbor_aligns(neighborhood):
	"""check element alignments among neighbors"""

	def count_possible_aligns(e1, e2):
		cnt = 0
		# vertical case
		if not y_overlap(e1, e2):
			e1_width = e1["bounds"][2] - e1["bounds"][0]
			e2_width = e2["bounds"][2] - e2["bounds"][0]
			cnt += 3 if np.absolute(e1_width - e2_width) <= ALIGN_TOLERANCE_DELTA else 1
		# horizontal case
		if not x_overlap(e1, e2):
			e1_height = e1["bounds"][3] - e1["bounds"][1]
			e2_height = e2["bounds"][3] - e2["bounds"][1]
			cnt += 3 if np.absolute(e2_height - e1_height) <= ALIGN_TOLERANCE_DELTA else 1
		return cnt

	aligns = []
	for x, neighbors in neighborhood:
		for y in neighbors:
			if y is not None:
				num_possible_aligns = count_possible_aligns(x, y)
				aligns.append((x["id"], y["id"], alignment_check([x, y]), num_possible_aligns))
	return aligns


def collect_neighbor_margins(neighborhood, x_range, y_range, return_as_dict=False):
	"""collect margins among neighborhood elements. 
		x_range, y_range: the range of x,y values that will be use to 
			calculate margins for elements that has no neighbor on the certain direction
	"""
	margins = {}
	for e, neighbors in neighborhood:
		ln, rn, tn, bn = neighbors
		margins[e["id"]] = [
			e["bounds"][0] - ln["bounds"][2] if ln is not None else e["bounds"][0] - x_range[0],
			rn["bounds"][0] - e["bounds"][2] if rn is not None else x_range[1] - e["bounds"][2],
			e["bounds"][1] - tn["bounds"][3] if tn is not None else e["bounds"][2] - y_range[0],
			bn["bounds"][3] - e["bounds"][1] if bn is not None else y_range[1] - e["bounds"][3] 
		]
	if return_as_dict == False:
		return [margins[x] for x in margins]
	return margins

def extract_layout_features(tree_root):
	"""extract layout features for learning """

	top_level_neighborhood = collect_neighbors(tree_root["children"])

	if not top_level_neighborhood:
		return {
			"top_level_align_score": 0, "top_level_balance_score": 0, "top_level_overlapping_area": 0, "avg_element_width": 0,
			"avg_element_height": 0, "avg_alignment_score": 0, "density": 0, "imbalance": 0
		}

	top_level_alignments = collect_neighbor_aligns(top_level_neighborhood)
	top_level_align_score = (sum([len(al[-2]) for al in top_level_alignments]) + 1) / float(sum([al[-1] for al in top_level_alignments]) + 1)
	top_level_margins = collect_neighbor_margins(top_level_neighborhood, x_range=(0, CANVAS_WIDTH), y_range=(0, CANVAS_HEIGHT))

	top_level_overlapping_area = 0
	for i, tg in enumerate(tree_root["children"]):
		for j in range(i + 1, len(tree_root["children"])):
			top_level_overlapping_area += overlap_area(tg["bounds"], tree_root["children"][j]["bounds"])

	# +1 for max_margin to tolerent full sized elements
	max_margin_h = max(max([m[0] for m in top_level_margins]), max([m[1] for m in top_level_margins]))
	top_level_balance_h = np.average([(m[0] + m[1] + 1) / (2 * max_margin_h + 1) for m in top_level_margins])
	
	max_margin_v = max(max([m[2] for m in top_level_margins]), max([m[3] for m in top_level_margins]))
	top_level_balance_v = np.average([(m[2] + m[3] + 1) / (2 * max_margin_v + 1) for m in top_level_margins])

	top_level_balance_score = (top_level_balance_h  + top_level_balance_v) / 2

	tree_groups, leaf_nodes = extract_groups_and_leaves(tree_root)
	# top level groups with single units
	canvas_direct_leaf_nodes = [c for c in tree_root["children"] if c["type"] != "group"] 

	# neighborhood relations among all visual elements
	global_neighborhood = collect_neighbors(leaf_nodes)

	group_features = []
	for g in tree_groups + canvas_direct_leaf_nodes:
		# canvs scores are calculated before low-level groups
		if g["type"] == "canvas": continue

		g_width = g["bounds"][2] - g["bounds"][0]
		g_height = g["bounds"][3] - g["bounds"][1]
		g_x, g_y = g["bounds"][0], g["bounds"][1]
		g_area = g_width * g_height

		elements = g["children"] if (g["type"] in ["canvas", "group"]) and len(g["children"]) > 0 else [g]

		avg_ele_width = np.average([nd["width"] for nd in elements])
		avg_ele_height = np.average([nd["height"] for nd in elements])

		group_neighborhood = collect_neighbors(elements)
		# calculate in-group alignments
		group_alignments = collect_neighbor_aligns(group_neighborhood)

		# + 1 to tolerate groups will only one elements
		group_align_score = (sum([len(al[-2]) for al in group_alignments]) + 1) / float(sum([al[-1] for al in group_alignments]) + 1)

		# extending neighborhood with elements outside this group
		extended_neighborhood = [p for p in global_neighborhood if p[0] in elements]
		margins = collect_neighbor_margins(extended_neighborhood, 
										   x_range=(0, CANVAS_WIDTH), 
										   y_range=(0, CANVAS_HEIGHT))

		max_margin_h = max(max([m[0] for m in margins]), max([m[1] for m in margins]))
		balance_h = np.average([(m[0] + m[1] + 1) / (2 * max_margin_h + 1) for m in margins])
		
		max_margin_v = max(max([m[2] for m in margins]), max([m[3] for m in margins]))
		balance_v = np.average([(m[2] + m[3] + 1) / (2 * max_margin_v + 1) for m in margins])

		feature = GroupFeature(x=g_x, y=g_y, width=g_width, height=g_height, 
							   avg_ele_width=avg_ele_width, avg_ele_height=avg_ele_height,
							   area=g_area, align_score=group_align_score, 
							   balance_h=balance_h,
							   balance_v=balance_v)
		group_features.append(feature)

	total_area = float(sum([f.area for f in group_features]))

	avg_balance_h = sum([f.balance_h * f.area for f in group_features]) / total_area
	avg_balance_v = sum([f.balance_v * f.area for f in group_features]) / total_area

	screen_feature = {
		"top_level_align_score": top_level_align_score,
		"top_level_balance_score": top_level_balance_score,
		"top_level_overlapping_area": top_level_overlapping_area / (CANVAS_WIDTH * CANVAS_HEIGHT),
		"avg_element_width": sum([(1 - f.avg_ele_width / float(CANVAS_WIDTH)) 
									* f.area for f in group_features]) / total_area,
		"avg_element_height": sum([(1 - f.avg_ele_height / float(CANVAS_HEIGHT)) 
									* f.area for f in group_features]) / total_area,
		"avg_alignment_score": sum([f.align_score * f.area for f in group_features])  / total_area,
		"density": total_area / float(CANVAS_WIDTH * CANVAS_HEIGHT),
		"imbalance": 1 - (avg_balance_v + avg_balance_h) / 2
	}

	return screen_feature

def extract_alignment_keys(elements):
	"""extract key features of an element list used for alignmetn checking"""

	x_left_vals = [c["bounds"][0] for c in elements]
	x_mid_vals = [(c["bounds"][0] + c["bounds"][2] / 2) for c in elements]
	x_right_vals = [c["bounds"][2] for c in elements]

	y_top_vals = [c["bounds"][1] for c in elements]
	y_mid_vals = [(c["bounds"][1] + c["bounds"][3] / 2) for c in elements]
	y_bot_vals = [c["bounds"][3] for c in elements]

	return x_left_vals, x_mid_vals, x_right_vals, y_top_vals, y_mid_vals, y_bot_vals

def alignment_check(elements):
	"""try to merge elements based on alignment results"""

	check_aligned = lambda l: np.std(l) <= ALIGN_TOLERANCE_DELTA

	alignment = ["left", "x-center", "right", "top", "y-center", "bottom"]
	vals = extract_alignment_keys(elements)

	align_type = []
	for i, al in enumerate(alignment):
		if check_aligned(vals[i]):
			align_type.append(al)

	return align_type


# Comparing a single pair of designs
#    For each matched pair of shapes (Find the matching shape of the name property of the element in the element tree)
#      / Only leaf node shapes 
#      Compute difference across the following dimensions
#          Position - absolute value of distance moved (computed distance between two x,y coordinates) 
#                - Normalize by dividing by screen diagonal length 
#          Size - absolute value of the difference of the two areas (HxW) between the two shapes (Normalize )
#                - Normalize by dividing by the total area of the screen
#          Neighboring elements
#              Find the closest neighboring element in each direction for each element
#              L, T, B, R 
#              If there is no element in a direction (L,T,B,R), the neighboring element in that direction is the canvas
#              For each closest neighboring element along each dimension: 
#                  Neighbor is a different element: 1, Not a different element: 0 
#                  Distance to neighbor in that direction (T,B,L,R)
#                      -- normalize by dividing by width (L,R)  or height (T,B) of canvas 
#              There should be 8 metrics T_changed + T_distance + L_changed + L_distance + B_changed + B_distance + R_changed + R_distance
#              Divide the total score/8 to get the neighboring elements diversity score
#          Representation (only for Alternate groups) - Changed - 1, Not Changed - 0
#                shape.alternate  = true 


# Diversity - iteration 2 
# S - Spatial Score 
# 		See algorithm above for computing P (position), S (size), N (neighbors)
#		For each pair of elements
#			Ppair + Spair + Npair 
#		S = Ptotal/#Elements + Stotal/#Elements + Ntotal/#Elements  
# A - Alternate Score
#  For each pair of elements
#     representation changed - 1, didn't change 0 
#  Then divide by the total number of elements (This metric wont' have much weight in our case b/c only one element can have 
#     an alternate, but it actually makes sense to normalize it this way since only one element changed)
# E - Additional Elements (Separator)
#    First, pair each separator to its closest separator in the other design (by distance)
# 	 For the score: 
#		Sum of additional elements / # elements on screen w/ additonal elements
# Total Score = S + A + E  

def compute_diversity_score(t1, t2):
	"""Given two designs t1 and t2, compute their diversity score
	Args:
		t1, t2: two object representing designs
	Returns:
		their diversity score
	"""

	# annotate the element tree with essential information
	process_element_tree(t1)
	process_element_tree(t2)
	groups_1, leaves_1 = extract_groups_and_leaves(t1)
	groups_2, leaves_2 = extract_groups_and_leaves(t2)
	neighbors1 = collect_neighbors(leaves_1)
	neighbors2 = collect_neighbors(leaves_2)
	margins1 = collect_neighbor_margins(neighbors1, x_range=(0, CANVAS_WIDTH), 
										y_range=(0, CANVAS_HEIGHT), return_as_dict=True)
	margins2 = collect_neighbor_margins(neighbors2, x_range=(0, CANVAS_WIDTH), 
										y_range=(0, CANVAS_HEIGHT), return_as_dict=True)

	# use all leave properties to compute leave difference
	l1 = {e["id"]:e for e in leaves_1}
	l2 = {e["id"]:e for e in leaves_2}
	n1 = {r[0]["id"]:r[1] for r in neighbors1}
	n2 = {r[0]["id"]:r[1] for r in neighbors2}

	def check_neighbor_changed(n1, n2):
		""" check whether two neighbor are the same or not"""
		if n1 is None and n2 is None:
			return False
		elif n1 is None or n2 is None:
			return False
		else:
			return n1["id"] != n2["id"]

	diff = {}
	for key in list(l1.keys()) + list(l2.keys()):
		if key in l2 and key in l1:
			pos_diff = ((l1[key]['x'] - l2[key]['x']), (l1[key]['y'] - l2[key]['y']))
			size_diff = (l1[key]['height'] * l1[key]["width"] - l2[key]['height'] * l2[key]["width"]) 
			size_diff = size_diff / float(CANVAS_WIDTH * CANVAS_HEIGHT)
			neighbor_changed = [check_neighbor_changed(n1[key][i], n2[key][i]) for i in range(4)]
			neighbor_dist_diff = [margins1[key][i] - margins2[key][i] for i in range(4)]
			neighbor_dist_diff = [neighbor_dist_diff[0] / float(CANVAS_WIDTH), 
								  neighbor_dist_diff[1] / float(CANVAS_WIDTH),
								  neighbor_dist_diff[2] / float(CANVAS_HEIGHT), 
								  neighbor_dist_diff[3] / float(CANVAS_HEIGHT)]
		else:
			pos_diff = None
			size_diff = None
			neighbor_changed = None
			neighbor_dist_diff = None

		values = {
			"pos_diff": pos_diff,
			"size_diff": size_diff,
			"neighbor_changed": neighbor_changed,
			"neighbor_dist_diff": neighbor_dist_diff
		}

		diff[key] = {
			"size_diff": np.absolute(size_diff),
			"pos_diff": np.linalg.norm(pos_diff, ord=2) / np.linalg.norm((CANVAS_WIDTH, CANVAS_HEIGHT)),
			"neighbor_diff": (sum(neighbor_changed) + sum([np.absolute(x) for x in neighbor_dist_diff])) / 8
		}

	return diff


from pprint import pprint
if __name__ == '__main__':
	if len(sys.argv) < 2:
		saved_path = "saved_2.json"
	else:
		saved_path = sys.argv[1]
	with open(saved_path, "r") as f:
		scout_exports = json.load(f)
		trees = [t["elements"] for t in scout_exports["saved"]]
		for i in range(len(trees)):
			for j in range(i + 1, len(trees)):
				diff = compute_diversity_score(trees[i], trees[j])
				pprint(diff)