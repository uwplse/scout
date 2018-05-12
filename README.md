# Scout

### Setup 
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

Install the npm packages for building the web application. 

	cd static
	npm install 
	npm run watch # This will build the web page, and recompile whenever it detects you made a change in the files so you do not need to run this command every time you make a change.  

If you want to just build the web application: 
	
	npm run build

### Running the web server
	cd server
	./run.sh

### Opening Scout
Home design dashboard

	Open http://localhost:5000/

Import an svg

	Open http://localhost:5000/import

Testing :) 