# server.py
from z3 import * 
from flask import Flask, render_template, request
import json
import base64
# import solver
# import annealing_solver as an
import uuid
import random
import copy
import custom_solver
import threading
import sys
import os
import threading
import queue
import faulthandler
faulthandler.enable()

DEFAULT_APP_HEIGHT = 667
DEFAULT_APP_WIDTH = 375
NUM_SOLVE_THREADS = 10
NUM_CHECK_THREADS = 10

class FlaskApp(Flask): 
	def __init__(self, *args, **kwargs): 
		super(FlaskApp, self).__init__(*args, **kwargs)
		self.solve_queue = queue.Queue()
		self.check_queue = queue.Queue()

		for i in range(NUM_SOLVE_THREADS):
			z3ctx = z3.Context() 
			self.solve_queue.put(z3ctx)

		for i in range(NUM_CHECK_THREADS): 
			z3ctx = z3.Context()
			self.check_queue.put(z3ctx)

		print("size of queues initialized: ")
		print(self.solve_queue.qsize())
		print(self.check_queue.qsize())
			
app = FlaskApp(__name__, static_folder="static/dist", template_folder="static")

@app.route("/")
def index():
	return render_template("index.html")

@app.route("/home")
def home(): 
	return render_template("home.html")

@app.route("/import")
def importer(): 
	return render_template("import.html")

@app.route("/hello")
def hello():
	return "Hello World!"

@app.route('/solve', methods=['POST','GET'])
def solve(): 
	print("solving!")
	sys.stdout.flush()
	form_data = request.form

	if "elements" in form_data and "solutions" in form_data:
		elements_json = form_data["elements"]
		solutions_json = form_data["solutions"]
		elements = json.loads(elements_json)
		solutions = json.loads(solutions_json)

		relative_designs = dict() 
		if "relative_designs" in form_data: 
			relative_designs_json = form_data["relative_designs"]
			relative_designs = json.loads(relative_designs_json)

		try: 
			results = {}
			t1 = threading.Thread(target=get_solution_from_custom_solver, args=(elements, solutions, relative_designs, results,))
			t1.start()
			t1.join()
			sys.stdout.flush()

			# get_solution_from_custom_solver(elements, solutions, relative_designs, results)

			# Output dictionary 
			output = dict()
			if "solutions" in results:
				output["solutions"] = results['solutions']
			return json.dumps(output).encode('utf-8')
		except Exception as e: 
			print("Exception in creating solver")
			print(e)
			return "'"
	sys.stdout.flush()
	return ""

@app.route('/check', methods=['POST','GET'])
def check(): 
	print("checking!")
	sys.stdout.flush()

	form_data = request.form

	if "elements" in form_data:
		elements_json = form_data["elements"]
		solutions_json = form_data["solutions"]
		elements = json.loads(elements_json)
		solutions = json.loads(solutions_json)

		# Will return the status of whether the current set of constraints is valid
		# and also update the valid state of each of the previous solutions
		results = {}
		t1 = threading.Thread(target=check_solution_exists_and_validate_previous_solutions, args=(elements,solutions,results,))
		# check_solution_exists_and_validate_previous_solutions(elements, solutions, results)

		t1.start()
		sys.stdout.flush()
		t1.join()
		sys.stdout.flush()

		# Don't return back any results, just the status of whether it could be solved or not
		output = dict() 
		if 'result' in results: 
			output["result"] = results['result']["valid"]
			output["solutions"] = results['result']["solutions"]
			return json.dumps(output).encode('utf-8')
		else: 
			return ""
		# except: 
		# 	print("Exception in creating solver.")
		# 	return ""
	sys.stdout.flush()
	return ""

def check_solution_exists_and_validate_previous_solutions(elements, solutions, results):
	# Wait until a context becomes available before proceeding
	solver_ctx = app.check_queue.get(block=True)
	print(solver_ctx)
	try: 
		print("Creating solver instance.")
		# solver_ctx = z3
		# print(app.solver_ctx)
		solver = custom_solver.Solver(solver_ctx, elements, solutions, DEFAULT_APP_WIDTH, DEFAULT_APP_HEIGHT)
	except Exception as e: 
		print(e)
		print('Exception in creating solver instance.')

	try: 
		print("Checking constraints.")
		check_results = solver.check()
		results['result'] = check_results
	except Exception as e: 
		print(e)
		print('Exception in checking constraints.')

	app.check_queue.put(solver_ctx)

def get_solution_from_custom_solver(elements, solutions, relative_designs, results): 
	# print(app.solver_ctx)
	solver_ctx = app.solve_queue.get(block=True)
	print(solver_ctx)

	solver = custom_solver.Solver(solver_ctx, elements, solutions, DEFAULT_APP_WIDTH, DEFAULT_APP_HEIGHT, relative_designs=relative_designs)
	solutions = solver.solve()
	app.solve_queue.put(solver_ctx)
	results['solutions'] = solutions

def get_solution_from_solver(elements, canvas_width, canvas_height, tags): 
	layout_solver = solver.LayoutSolver(elements, canvas_width, canvas_height, tags)
	solutions = layout_solver.solve()
	return solutions

def get_initial_state(elements): 
	shapes = []
	for element in elements: 
		x = element["x"]
		y = element["y"]
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
		elements[i]["x"] = x
		elements[i]["y"] = y
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
	# import argparse

	# parser = argparse.ArgumentParser(description='Development Server Help')
	# parser.add_argument("-d", "--debug", action="store_true", dest="debug_mode",
	# 					help="run in debug mode (for use with PyCharm)", default=False)
	# parser.add_argument("-p", "--port", dest="port",
	# 					help="port of server (default:%(default)s)", type=int, default=5000)

	# cmd_args = parser.parse_args()
	# app_options = {"port": cmd_args.port}

	# #if cmd_args.debug_mode:
	# app_options["debug"] = True
	# app_options["use_debugger"] = False
	# app_options["use_reloader"] = False
	port = int(os.environ.get("PORT", 5000))
	app.run(host='0.0.0.0', port=port)

