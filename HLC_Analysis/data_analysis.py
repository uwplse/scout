"""Analysis of HLC in each designer's exported designs for reporting numbers in the CHI paper"""
import sys 
import os
import csv
import json

def get_count(path, file_name, key): 
	"""Get the total number of designs they explored"""
	designs_file = os.path.join(path, file_name)
	with open(designs_file, 'r') as designs_json: 
		designs_list = json.load(designs_json)
		total_designs = len(designs_list[key])
		return total_designs
	return 0

def count_hlc(design, results_dict, parent_emphasis=False): 
	#Groups 
	"""Count up different types of HLC used"""
	if design["type"] == "group": 
		if design["alternate"]: 
			results_dict["alternate"] += 1 
		elif design["typed"]:
			results_dict["repeat_group"] +=1 
		elif not design["item"]:
			results_dict["group"] += 1 

	#Emphasis
	is_emph = False
	if "importance" in design and design["importance"] != "normal" and not parent_emphasis:
		is_emph = True
		results_dict["emphasis"] += 1

	#Order
	if "containerOrder" in design and design["containerOrder"] == "important": 
		results_dict["order"] +=1 

	if "order" in design and design["order"] != -1: 
		results_dict["order"] += 1

	if "locks" in design: 
		results_dict["locks"] += len(design["locks"])
 
	if "children" in design:
		for child in design["children"]: 
			count_hlc(child, results_dict, is_emph) 

def compute_hlc_totals(design_path, file_name, key, results): 
	""" Open designs file and count up HLC used """
	designs_file = os.path.join(design_path, file_name)
	with open(designs_file, 'r') as designs_json_file: 
		designs_json = json.load(designs_json_file)
		designs_list = designs_json[key]

		if len(designs_list): 
			results["total"] += len(designs_list)
			for design in designs_list: 
				count_hlc(design["elements"], results)
		else: 
			print(file_name)
			print("No designs found")

def analyze_hlc(path, output): 
	""" Output summed values for HLC to analysis CSV """
	output_path = os.path.join(output, "analysis.csv")
	with open(output_path, 'w') as output_file: 
		csv_writer = csv.writer(output_file, delimiter=',')
		header = ["ID", "NumDesignsExplored", "Groups", "Repeat Groups", "Alternate Groups", "Order", "Emphasis"]
		csv_writer.writerow(header)

		designer_files = os.listdir(path)
		for file in designer_files: 
			design_path = os.path.join(path, file)
			if not file.startswith('.') and os.path.isdir(design_path): 
				num_explored = 0
				num_explored += get_count(design_path, "trashed.json", "trashed")
				num_explored += get_count(design_path, "saved.json", "saved") 
				num_explored += get_count(design_path, "invalidated.json", "invalidated")
				num_explored += get_count(design_path, "under_consideration.json", "under_consideration")

				# Count the totals for HLC used 
				results = dict()
				results['group'] = 0
				results["emphasis"] = 0 
				results["repeat_group"] = 0 
				results["order"] = 0 
				results["alternate"] = 0 
				results["locks"] = 0
				results["total"] = 0

				# Count totals for each saved file in each category """
				compute_hlc_totals(design_path, "trashed.json", "trashed", results)
				compute_hlc_totals(design_path, "saved.json", "saved", results)
				compute_hlc_totals(design_path, "invalidated.json", "invalidated", results)
				compute_hlc_totals(design_path, "under_consideration.json", "under_consideration", results)

				avg_groups = results['group'] / results["total"]
				avg_emph = results['emphasis'] / results["total"]
				avg_rg = results["repeat_group"] / results["total"]
				avg_order = results["order"] / results["total"]
				avg_alt = results["alternate"] / results["total"]
				avg_locks = results["locks"] / results["total"]

				info = [file, num_explored, avg_groups, avg_rg, avg_alt, avg_order, avg_emph]
				print(info)
				csv_writer.writerow(info)



if __name__ == "__main__":
	path = sys.argv[1]
	output = sys.argv[2]
	analyze_hlc(path, output)
