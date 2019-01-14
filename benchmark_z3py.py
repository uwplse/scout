from z3 import *
import time
import subprocess

expressions = 1

def test_z3_from_api(solver): 
	index = 0 
	values = [1,2,3,4,5,6,7,8,9,10]
	while index < expressions: 
		x = Int('x' + str(index))
		y = Int('y' + str(index))
		or_values = []
		for value in values: 
			or_values.append(x == value)
		solver.assert_and_track(IntVal(1) == IntVal(2), "test_unsat_core_naming")
		solver.assert_and_track(Or(or_values), "Constraint" + str(index))
		solver.assert_and_track(x == y, "Equality" + str(index))
		index += 1

def test_z3_from_expr(solver):
	index = 0
	expr = "(set-info :source | Python ftw |)\n"
	expr += "(set-option :produce-unsat-cores true)\n"
	values = ["1","2","3","4","5","6","7","8","9","10"]
	while index < expressions: 
		x_name = 'x' + str(index)
		y_name = 'y' + str(index)
		expr += "(declare-fun " + x_name + " () Int)\n"
		expr += "(declare-fun " + y_name + " () Int)\n"
		expr += "(assert (! (= 1 2) :named test_naming2))\n"
		expr += "(assert (! (= " + x_name + " " + y_name + ")))\n" 
		expr += "(declare-fun y2 () Int)\n"
		expr += "(assert (= y2 2))\n"
		expr += "(assert (or"
		for value in values: 
			expr += "(= " + x_name + " " + str(value) + ")\n"
		expr += "))\n"
		index += 1 
	solver.from_string(expr)


if __name__ == "__main__":
	num = 10
	index = 0 
	while index < num:
		ret = subprocess.Popen(["python", "z3_solver.py"])   
		print(ret)
		index += 1



