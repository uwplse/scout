# server.py
from flask import Flask, render_template, request
import json
import base64
# import solver
# import annealing_solver as an
import uuid
import random
import copy
import custom_solver

app = Flask(__name__, static_folder="../static/dist", template_folder="../static")
DEFAULT_APP_HEIGHT = 667
DEFAULT_APP_WIDTH = 375

@app.route("/")
def index():
	return render_template("index.html")

@app.route("/home")
def home(): 
	return render_template("home.html")

@app.route("/hello")
def hello():
	return "Hello World!"


@app.route('/solve', methods=['POST'])
def solve(): 
	print("solving!")
	print(request.data)

	canvas_width = DEFAULT_APP_WIDTH
	canvas_height = DEFAULT_APP_HEIGHT

	request_data = json.loads(request.data.decode("utf-8"))
	if "elements" in request_data: 
		elements = request_data["elements"]
		groups = dict()
		solutions = get_solution_from_custom_solver(elements, groups, canvas_width, canvas_height)

	return "" 

@app.route("/get_elements")
def get_elements(): 
	# Configuration
	elements = dict()
	canvas_width = DEFAULT_APP_WIDTH
	canvas_height = DEFAULT_APP_HEIGHT
	groups = dict()
	with open('../specification/facebook_simple.json') as data_file:
		config = json.load(data_file)
		elements = config["elements"]
		tags = None
		if "tags" in config: 
			tags = config["tags"]

		for element in elements: 
			if element["type"] == "logo" or element["type"] == "image": 
				element["source"] = read_image_data(element["path"])

		canvas_width = config["canvas_size"]["width"]
		canvas_height = config["canvas_size"]["height"]
		background = config["background"]

		if "groups" in config: 
			groups = config["groups"]


	# Simulated annealing search 
	# solutions = get_solution_annealing(elements, canvas_width, canvas_height)
	# solutions = get_solution_from_solver(elements, canvas_width, canvas_height, tags)
	solutions = get_solution_from_custom_solver(elements, groups, canvas_width, canvas_height, tags)

	# Output dictionary 
	output = dict() 
	output["size"] = dict() 
	output["size"]["width"] = canvas_width
	output["size"]["height"] = canvas_height
	output["background"] = background
	output["elements"] = solutions

	# Write the results for debugging
	# with open('../results/results.json', 'w') as outfile:
	# 	json.dump(output, outfile)

	return json.dumps(output).encode('utf-8')

def get_solution_from_custom_solver(elements, groups, canvas_width, canvas_height): 
	solver = custom_solver.Solver(elements, groups, canvas_width, canvas_height)
	solutions = solver.solve()
	return solutions

def get_solution_from_solver(elements, canvas_width, canvas_height, tags): 
	layout_solver = solver.LayoutSolver(elements, canvas_width, canvas_height, tags)
	solutions = layout_solver.solve()
	return solutions

def get_initial_state(elements): 
	shapes = []
	for element in elements: 
		x = element["location"]["x"]
		y = element["location"]["y"]
		width = element["size"]["width"]
		height = element["size"]["height"]
		shapes.append([x,y,width,height])
	return shapes

def randomize_initial_positions(state, box_width, box_height): 
    for shape in state: 
        max_x = box_width - shape[2]
        max_y = box_height - shape[3]
        rand_x = random.randint(0, max_x)
        rand_y = random.randint(0, max_y)
        shape[0] = rand_x
        shape[1] = rand_y 
    return state

def convert_state(elements, state): 
	for i in range(0, len(state)): 
		x,y,width,height = state[i]
		elements[i]["location"]["x"] = x
		elements[i]["location"]["y"] = y
		elements[i]["size"]["width"] = width 
		elements[i]["size"]["height"] = height
	return elements

def get_solution_annealing(elements, canvas_width, canvas_height): 
	# latitude and longitude for the twenty largest U.S. cities
	init_state = get_initial_state(elements)
	init_state = randomize_initial_positions(init_state, canvas_width, canvas_height)

	num_shapes = len(init_state) 
	total_pairs = num_shapes * (num_shapes - 1)# The total number of possible alignment pairs
	tmax = total_pairs
	tmin = 1

	tsp = an.LayoutAnnealingProblem(init_state, canvas_width, canvas_height)
	tsp.steps = 250000
	tsp.Tmax = tmax
	tsp.Tmin = tmin

	# Send back the initial state as a solution so we can look at it
	solutions = []
	cpy = copy.deepcopy(elements)
	initial_elements = convert_state(cpy, init_state)
	sln = dict() 
	sln["elements"] = initial_elements
	sln["id"] = uuid.uuid4().hex
	sln["energy"] = tsp.energy()
	solutions.append(sln)

	# since our state is just a list, slice is the fastest way to copy
	# tsp.copy_strategy = "slice"
	state, e = tsp.anneal()
	final_elements = convert_state(elements, state)

	new_solution = dict() 
	new_solution["elements"] = final_elements
	new_solution["id"] = uuid.uuid4().hex
	new_solution["energy"] = tsp.energy()
	solutions.append(new_solution)
	return solutions

def read_image_data(image_path): 
	img = open(image_path, 'rb')
	img_data = img.read()
	img_b64 = base64.b64encode(img_data)
	img_b64_string = img_b64.decode("utf-8")
	return "data:image/png;base64, " + img_b64_string

if __name__ == "__main__":
	import argparse

	parser = argparse.ArgumentParser(description='Development Server Help')
	parser.add_argument("-d", "--debug", action="store_true", dest="debug_mode",
						help="run in debug mode (for use with PyCharm)", default=False)
	parser.add_argument("-p", "--port", dest="port",
						help="port of server (default:%(default)s)", type=int, default=5000)

	cmd_args = parser.parse_args()
	app_options = {"port": cmd_args.port}

	if cmd_args.debug_mode:
		app_options["debug"] = True
		app_options["use_debugger"] = False
		app_options["use_reloader"] = False

	app.run(**app_options)