
GUTTERS = [4,18,16] # TODO can introduce a variable value for these at some point
COLUMNS = [2,3,4,5,6,7,8,9,10,11,12]
MARGINS = [4,8,12,16,20,24,28,32,36,40,44,48,52,56,60]
CANVAS_WIDTH = 360 


values = dict()
columns = dict()
for margin_value in MARGINS: 
	for column_value in COLUMNS: 
		for gutter_value in GUTTERS: 
			column_width = float((CANVAS_WIDTH - (2*margin_value) - ((column_value-1)*gutter_value)))/float(column_value)
			int_column_width = int(column_width)
			if column_width - int_column_width == 0: 
				values[int_column_width] = True
				columns[column_value] = True
				print(column_value)

			# values[column_width] =  True

print(values.keys()) 
print(columns.keys())
