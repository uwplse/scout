# server.py
from z3 import * 
from flask import Flask, render_template, request
import json
import custom_solver
import sys
import os
import faulthandler
import time
import logging
faulthandler.enable()


NUM_SOLVE_THREADS = 10
NUM_CHECK_THREADS = 10

class FlaskApp(Flask): 
	def __init__(self, *args, **kwargs): 
		super(FlaskApp, self).__init__(*args, **kwargs)
			
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

@app.route('/solve', methods=['POST','GET'])
def solve(): 
	print("solving!")
	sys.stdout.flush()
	form_data = request.form

	if "elements" in form_data and "solutions" in form_data:
		elements_json = form_data["elements"]
		solutions_json = form_data["solutions"]

		# relative_designs = dict() 
		# if "relative_designs" in form_data: 
		# 	relative_designs_json = form_data["relative_designs"]
		# 	relative_designs = json.loads(relative_designs_json)

		try: 
			solutions = get_solution_from_custom_solver(elements_json, solutions_json)

			# Output dictionary 
			output = dict()
			output["solutions"] = solutions
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

		# Will return the status of whether the current set of constraints is valid
		# and also update the valid state of each of the previous solutions
		results = check_solution_exists_and_validate_previous_solutions(elements_json,
																		solutions_json)

		sys.stdout.flush()

		# Don't return back any results, just the status of whether it could be solved or not
		output = dict() 
		# output["result"] = results["valid"]
		output["solutions"] = results
		return json.dumps(output).encode('utf-8')
	sys.stdout.flush()
	return ""

def check_solution_exists_and_validate_previous_solutions(elements, solutions):
	# Wait until a context becomes available before proceeding
	try: 
		print("Creating solver instance.")
		solver = custom_solver.CustomSolver(elements, solutions)
		
		print("Checking constraints.")
		check_results = solver.check()
		return check_results
	except Exception as e: 
		print(e)
		print('Exception in creating solver instance.')

def get_solution_from_custom_solver(elements, solutions, relative_designs=""):
	time_start = time.time()
	print("Creating solver instance.")
	solver = custom_solver.CustomSolver(elements, solutions, 
		relative_designs=relative_designs)

	print("Solving for designs.")
	solutions = solver.solve()
	time_end = time.time()
	logging.debug("Total time taken for call: " + str(time_end-time_start))
	return solutions

if __name__ == "__main__":
	port = int(os.environ.get("PORT", 5000))
	app.run(host='0.0.0.0', port=port)

