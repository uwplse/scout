# server.py
from flask import Flask, render_template
import json
import base64
import solver

app = Flask(__name__, static_folder="../static/dist", template_folder="../static")
APP_HEIGHT = 350
APP_WIDTH = 450

@app.route("/")
def index():

	# Configuration
	elements = dict()
	with open('../specification/content2.json') as data_file:
		config = json.load(data_file)
		elements = config["elements"]
		print(str(len(elements)))

	return render_template("index.html", elements=elements)

@app.route("/hello")
def hello():
	return "Hello World!"

@app.route("/get_elements")
def get_elements(): 
	# Configuration
	elements = dict()
	with open('../specification/content.json') as data_file:
		config = json.load(data_file)
		elements = config["elements"]
		for element in elements: 
			if element["type"] == "logo" or element["type"] == "image": 
				element["source"] = read_image_data(element["path"])

	# Solve for all possible layouts (or one possible layout)
	layout_solver = solver.LayoutSolver.init_problem(elements, APP_WIDTH, APP_WIDTH)
	elements = layout_solver.solve()

	return json.dumps(elements).encode('utf-8')

def read_image_data(image_path): 
	img = open(image_path, 'rb')
	img_data = img.read()
	img_b64 = base64.b64encode(img_data)
	img_b64_string = img_b64.decode("utf-8")
	return "data:image/png;base64, " + img_b64_string

if __name__ == "__main__":
	app.run()  