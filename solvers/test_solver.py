from cassowary import SimplexSolver, Variable, STRONG, WEAK

solver = SimplexSolver()

r1_width = 100
r1_height = 100
r2_width = 100
r2_height = 100
r1_x = Variable('rectangle1x')
r1_y = Variable('rectangle1y')
r2_x = Variable('rectangle2x')
r2_y = Variable('rectangle2y')
screen_width = 300
screen_height = 300
proximity = 5

# Auxiliary variables
y0 = Variable('y0')
y1 = Variable('y1')
y2 = Variable('y2')
y3 = Variable('y3')

# Restrict the range so it satisfies at least one of the four
solver.add_constraint(y0 >= 0)
solver.add_constraint(y1 >= 0)
solver.add_constraint(y2 >= 0)
solver.add_constraint(y3 >= 0)

solver.add_constraint(y0 <= 1)
solver.add_constraint(y1 <= 1)
solver.add_constraint(y2 <= 1)
solver.add_constraint(y3 <= 1)

# Upper bounds on solutions is calculated from screen_width 
M_x = screen_width
M_y = screen_height

# Stay in bounds
solver.add_constraint(r1_x >= 0)
solver.add_constraint(r1_y >= 0)
solver.add_constraint(r2_x >= 0)
solver.add_constraint(r2_y >= 0)
solver.add_constraint(r1_x + r1_width <= screen_width)
solver.add_constraint(r2_x + r2_width <= screen_width)
solver.add_constraint(r1_y + r1_height <= screen_height)
solver.add_constraint(r2_y + r2_height <= screen_height)

# Non-overlapping 
left = r1_x + r1_width <= r2_x + (M_x * (1-y0))
right = r2_x + r2_width <= r1_x + (M_x * (1-y1))
top = r1_y + r1_height <= r2_y + (M_y * (1-y2))
bottom = r2_y + r2_height <= r1_y + (M_y * (1-y3))

# Add non-overlapping constraints into the solver
solver.add_constraint(left)
solver.add_constraint(right)
solver.add_constraint(top)
solver.add_constraint(bottom)

# Enforcing distance between two shapes == proximity 
left_dist_one = r1_x + r1_width + proximity <= r2_x + (M_x * (1-y0))
left_dist_two = r2_x <= r1_x + r1_width + proximity + (M_x * (1-y0))
left_top = r2_y <= r1_y + r1_height + proximity + (M_y * (1-y0))
left_bottom = r1_y <= r2_y + r2_height + proximity + (M_y * (1-y0))

right_dist_one = r2_x + r2_width + proximity <= r1_x + (M_x * (1-y1))
right_dist_two = r1_x <= r2_x + r2_width + proximity + (M_x * (1-y1))
right_top = r2_y <= r1_y + r1_height + proximity + (M_y * (1-y1))
right_bottom = r1_y <= r2_y + r2_height + proximity + (M_y * (1-y1))

top_dist_one = r1_y + r1_height + proximity <= r2_y + (M_y * (1-y2))
top_dist_two = r2_y <= r1_y + r1_height + proximity + (M_y * (1-y2))
top_left = r2_x <= r1_x + r1_width + proximity + (M_x * (1-y2))
top_right = r1_x <= r2_x + r2_width + proximity + (M_x * (1-y2))

bottom_dist_one = r2_y + r2_height + proximity <= r1_y + (M_y * (1-y3))
bottom_dist_two = r1_y <= r2_y + r2_height + proximity + (M_y * (1-y3))
bottom_left = r2_x <= r1_x + r1_width + proximity + (M_x * (1-y3))
bottom_right = r1_x <= r2_x + r2_width + proximity + (M_x * (1-y3))

solver.add_constraint(left_dist_one)
solver.add_constraint(left_dist_two)
solver.add_constraint(left_top)
solver.add_constraint(left_bottom)
solver.add_constraint(right_dist_one)
solver.add_constraint(right_dist_two)
solver.add_constraint(right_top)
solver.add_constraint(right_bottom)
solver.add_constraint(top_dist_one)
solver.add_constraint(top_dist_two)
solver.add_constraint(top_left)
solver.add_constraint(top_right)
solver.add_constraint(bottom_dist_one)
solver.add_constraint(bottom_dist_two)
solver.add_constraint(bottom_left)
solver.add_constraint(bottom_right)

# At least one non-overlapping constraint must be satisfied (for the disjunction)
solver.add_constraint((y0 + y1 + y2 + y3) >= 1)
r1_x_val = r1_x.value

print("hello")