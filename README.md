# Scout

## Mac Install Instructions

### XCode Setup (**if not already installed**)
Install XCode through the app store installer. 

After installing XCode, install the XCode developer tools using the command: 
	
	xcode-select --install

### Repo Setup
Clone the repository from GitHub. 

   git clone https://github.com/uwplse/scout.git
   cd scout


### Python Setup 
Make sure you have Python 3 installed (3.5). 

Install 'virtualenv' through the command

	pip install virtualenv 

Create the virtual environment

	virtualenv --python=python3.5 scout

Activate the virtual environment

	source scout/bin/activate

### Install Python packages
    pip install -r requirements.txt


### Install Z3 
*** Optional: This part is not needed to run the server. It is only needed if are working with the code that generates the design from the constraints tree.

*** If you do not do the Z3 steps, comment out the following line in server/server.py: 
	
	import custom_solver

*** Make sure you have the Python virtual environment created above still activated. 

	git clone https://github.com/Z3Prover/z3
	cd z3
	python scripts/mk_make.py --python # Compile with Python bindings
	cd build
	make
	make install

### Compiling the web application
Install NodeJS and npm if you do not already have them. 

	https://www.npmjs.com/get-npm


Install the custom package for react-sortable-tree. 

	git clone https://github.com/mandamarie0587/react-sortable-tree.git
	cd react-sortable-tree
	npm install
	npm run build
	npm pack

Install the npm packages for building the web application. 

	cd scout 
	cd static
	npm install 
	npm run watch # This will build the web page, and recompile whenever it detects you made a change in the files so you do not need to run this command every time you make a change.  

If you want to just build the web application: 
	
	cd static 
	npm run build

### Running the web server
	cd server
	./run.sh

### Opening Scout
Home design dashboard. (*** You will only be able to open this page if you do the Z3 steps above)

	Open http://localhost:5000/

Import an svg page. 

	Open http://localhost:5000/import 