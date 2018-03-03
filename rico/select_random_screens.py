import random
import os

num_screens = 15
path = "/Volumes/My Passport/Work/Research/Mobile_App_Accessibility/Rico_Data/traces/filtered_traces"

files = os.listdir(path)
num_files = len(files)

selected = 0
while selected < num_screens: 
	# Select a random index
	f_index = random.randint(0, num_files-1)
	f_name = files[f_index]
	f_input = os.path.join(path, f_name)
	trace_path = os.path.join(f_input, "trace_0", "screenshots")

	# Select a random screenshot within the app
	screenshots = os.listdir(trace_path)
	num_screenshots = len(screenshots)
	s_index = random.randint(0, num_screenshots-1)
	s_name = screenshots[s_index]
	screenshot_path = os.path.join(trace_path, s_name)

	print(screenshot_path)
	selected += 1


