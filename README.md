# layout

### Setup 
1. Make sure you have Python 3 installed (3.5). 
2. Install 'virtualenv' through the command
	pip install virtualenv 
3. Activate the virtual environment
	source layout/bin/activate

### Install Python packages
    pip install -r requirements.txt


### Install Z3 
*** Optional: This part is not needed to run the server. It is only needed if are working with the code that generates the design from the constraints tree.
*** Make sure you have the Python virtual environment created above still activated. 

1. Clone the Z3 repository 
	git clone https://github.com/Z3Prover/z3
2. cd z3
3. python scripts/mk_make.py --python # Compile with Python bindings
4. cd build
5. make
6. make install

