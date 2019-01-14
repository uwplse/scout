from z3 import * 
import time

def create_constraints(solver, ctx): 
	index = 0 
	values = range(0, 2000)

	expressions = 10 
	while index < expressions: 
		x = Int('x' + str(index), ctx=ctx)
		y = Int('y' + str(index), ctx=ctx)
		a = Bool('a' + str(index), ctx=ctx)
		b = Bool('b' + str(index), ctx=ctx)
		c = Bool('c' + str(index), ctx=ctx)
		d = Bool('d' + str(index), ctx=ctx)
		or_values = []
		for value in values: 
			or_values.append(x == value)
		solver.add(x > 10, y == x / 2)
		solver.assert_and_track(And([a,b], ctx), "Cosntrainta" + str(index))
		solver.assert_and_track(And([c,d], ctx), "Cosntraintb" + str(index))
		solver.assert_and_track(Or(or_values, ctx), "Constraint" + str(index))
		solver.assert_and_track(x == y, "Equality" + str(index))


		index += 1

if __name__ == "__main__":

	num = 0 
	while num < 10: 
		context = z3.Context()
		print(context.ref())

		solver = z3.Solver(ctx=context)
		create_constraints(solver, context)
		result = solver.check()
		print("Result: " + str(result))
		num += 1