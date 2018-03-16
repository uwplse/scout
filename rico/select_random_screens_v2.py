import random
import os

num_screens = 5
path = "/Volumes/Amanda's Data/Rico/combined"

files = os.listdir(path)
num_files = len(files)

selected = 0
while selected < num_screens: 
	# Select a random index
	f_index = random.randint(0, num_files-1)
	f_name = files[f_index]
	if f_name.find(".json") < 0:
		f_input = os.path.join(path, f_name)
		print(f_input)
		selected += 1


