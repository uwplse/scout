# server.py
from flask import Flask, render_template
import json
import base64
import solver

app = Flask(__name__, static_folder="../static/dist", template_folder="../static")
DEFAULT_APP_HEIGHT = 667
DEFAULT_APP_WIDTH = 375

@app.route("/")
def index():
	return render_template("index.html")

@app.route("/hello")
def hello():
	return "Hello World!"

@app.route("/get_elements")
def get_elements(): 
	# Configuration
	elements = dict()
	canvas_width = DEFAULT_APP_WIDTH
	canvas_height = DEFAULT_APP_HEIGHT
	with open('../specification/facebook_app.json') as data_file:
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

	# Solve for all possible layouts (or one possible layout)
	print("num elements " + str(len(elements)))
	layout_solver = solver.LayoutSolver(elements, canvas_width, canvas_height, tags)
	solutions = layout_solver.solve()

	# Output dictionary 
	output = dict() 
	output["size"] = dict() 
	output["size"]["width"] = canvas_width
	output["size"]["height"] = canvas_height
	output["background"] = background
	output["elements"] = solutions

	# Write the results for debugging
	with open('../results/results.json', 'w') as outfile:
		json.dump(output, outfile)

	return json.dumps(output).encode('utf-8')

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