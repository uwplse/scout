import json
import os 

def traverse_hierarchy(root): 
	layouts = 0
	containers = 0 
	leaves = 0
	clickable = 0
	only_leaves = 0
	if "class" in root: 
		class_name = root["class"]
		class_name_len = len(class_name)
		if class_name_len > 6:
			last_part = class_name[class_name_len-6:class_name_len]
			if last_part == "Layout": 
				layouts += 1

		if "clickable" in root and root["clickable"] == True: 
			clickable += 1

		if "children" in root: 
			containers += 1
			children = root["children"]
			num_children = len(children)
			no_leaves = 0
			leaf_classes = []
			clickables = []
			a_clickable_child = False
			for child in children: 
				if "children" in child: 
					l,c,lv,cl,ol = traverse_hierarchy(child)
					layouts += l
					containers += c
					leaves += lv
					clickable += cl
					only_leaves += ol
				else: 			
					leaves += 1
					no_leaves += 1
					if "class" in child: 
						child_class = child["class"]
						leaf_classes.append(child_class)

						if "clickable" in child and child["clickable"] == True: 
							clickable += 1
							a_clickable_child = True
							clickables.append(child_class)

			if num_children == no_leaves and a_clickable_child:
				print("---------") 
				print("Task Group: " + class_name) 
				print("Number of children: " + str(num_children))
				print("----All children-----")
				print(leaf_classes)
				print("----Clickable children----")
				print(clickables)

				only_leaves += 1

	return [layouts,containers,leaves,clickable,only_leaves]

json_path = "apps/json"
app_json_names = os.listdir(json_path)
for app_json_name in app_json_names: 
	if not app_json_name.startswith("."): 
		app_json_path = os.path.join(json_path, app_json_name)
		print(app_json_path)
		with open(app_json_path) as app_data_file: 
			app_data = json.load(app_data_file)
			if "activity" in app_data and "root" in app_data["activity"]: 
				root = app_data["activity"]["root"]
				layouts,containers,leaves,clickable,only_leaves = traverse_hierarchy(root)
				print("total layout containers: " + str(layouts))
				print("all containers: " + str(containers))
				print("leaves: " + str(leaves))
				print("clickable leaves: " + str(clickable))
				print("only leaves: " + str(only_leaves))


# with open('../specification/facebook_app.json') as data_file:
# 	config = json.load(data_file)