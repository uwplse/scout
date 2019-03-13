# Scout

## MacOS Install Instructions. 

### XCode Setup (**if not already installed**)
Install XCode through the app store installer. 

After installing XCode, install the XCode developer tools using the command: 
	
	xcode-select --install

### Repo Setup
Clone the Scout repository from GitHub. 

	git clone https://github.com/uwplse/scout.git
	cd scout

### Python Setup 
Make sure you have Python 3 installed (3.5 or higher). 

Install 'virtualenv' through the command

	pip install virtualenv 

Create the virtual environment

	virtualenv --python=python3.X scout

Activate the virtual environment

	source scout/bin/activate

### Install Python packages
    pip install -r requirements.txt


### Install Z3
*** Make sure you have the Python virtual environment created above still activated. 
	Clone into the directory with scout, the structure should be: 
		GitHub/
			scout
			z3

	git clone https://github.com/Z3Prover/z3 
	cd z3
	python scripts/mk_make.py --python # Compile Z3 with Python bindings 
	cd build
	make    # (Takes ~20 minutes on a standard MacBook Pro)
	make install

### Compiling the web application
Install NodeJS and npm if you do not already have them. 

	https://www.npmjs.com/get-npm

	OR

	brew install node

Install the npm packages for building the web application. 

	cd scout 
	cd static
	npm install 
	npm run watch # Build the web page and watch for changes to the JS code

If you want to just build the web application without watching for changes to the JS: 
	cd scout
	cd static 
	npm run build

### Running the Scout server 
	cd scout
	./run.sh

### Opening Scout

	Open http://localhost:5000/


### Deploying Scout to a Docker machine on Heroku

	Instructions TBD
