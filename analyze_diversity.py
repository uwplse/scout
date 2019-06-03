import sys 
import os
import csv
import cost_model
import os
import json
import sys

from pprint import pprint

OUTPUT_FILE = "diversity_scores.csv"

def load_design(design_dir):
	"""the directory containing exported designs"""

	design = {}
	# load saved designs and trashed designs
	with open(os.path.join(design_dir, "saved.json")) as f:
		design["saved"] = json.load(f)["saved"]

	if os.path.exists(os.path.join(design_dir, "trashed.json")): 
		with open(os.path.join(design_dir, "trashed.json")) as f:
			design["trashed"] = json.load(f)["trashed"]

	# load paths for saved svgs, relates to saved designs by their canvas ids
	svg_dir = os.path.join(design_dir, "saved_svgs")
	if not os.path.isdir(svg_dir):
		svg_dir = os.path.join(design_dir, "import_these_into_xd")

		if not os.path.isdir(svg_dir): 
			svg_dir = os.path.join(design_dir, "images")

	design["svg_paths"] = {}
	for fname in os.listdir(svg_dir):
		if fname.endswith(".svg"):
			design_id = fname.split(".")[0].split("-")[-1]
			design["svg_paths"][design_id] = os.path.join(svg_dir, fname)

	design["dirname"] = design_dir
	return design

def analyze_design(all_designs):
	""" Analyze design scores from all saved apps, the scores are normalized across all designs
		For each pair of saved designs in each file, display their diversity score as well as svgs
		Inputs:
			all_designs: a list of saved designs (saved.json)
	"""
	
	raw_diversity_score = {}
	
	for exp_id, design in all_designs.items():   
		
		if len(design["saved"]) == 1:
			print("[error] this directory contains only 1 saved desigsn.")
			continue

		for i in range(len(design["saved"])):
			for j in range(i + 1, len(design["saved"])):
				di, dj = design["saved"][i], design["saved"][j]
				#diversity_score, diff = cost_model.compute_diversity_score(di["elements"], dj["elements"])
				raw_diversity_score[(exp_id, i, j)] = cost_model.compute_unnormalized_diversity_score(
					di["elements"], dj["elements"])

	final_scores = cost_model.normalize_diversity_scores(raw_diversity_score)
	
	design_pairs = []
	for pair_id in final_scores:
		exp_id, i,j = pair_id
		score = (final_scores[pair_id]["alt_group_score"]
					+ final_scores[pair_id]["pos_diff_score"] 
					+ final_scores[pair_id]["rel_dist_diff_score"] 
					+ 2 * final_scores[pair_id]["size_diff_score"])
		design_pair = {
			"exp_id": exp_id,
			"score": score,
			"score_detail": final_scores[pair_id],
			"di": all_designs[exp_id]["saved"][i],
			"dj": all_designs[exp_id]["saved"][j],
		}
		
		design_pairs.append(design_pair)

	return design_pairs

def analyze_diversity(folder):
	""" Analyze sets of designs within a folder """ 
	all_designs = {}
	for dirname in os.listdir(folder):
		design_dir = os.path.join(folder, dirname)
		if not os.path.isdir(design_dir):
			continue
		design = load_design(design_dir)
		all_designs[dirname] = design
		
	design_pairs = analyze_design(all_designs)
	return design_pairs

def output_results(design_pairs, output_folder): 
	""" Output the results into a CSV """ 
	csv_output_path = os.path.join(output_folder, OUTPUT_FILE)
	with open(csv_output_path, mode='w') as diversity_file:
		diversity_writer = csv.writer(diversity_file, delimiter=',', 
			quotechar='"')
		diversity_writer.writerow(["Participant ID", "Experience Level", "Order", "Task", "Condition", "Pair 1", "Pair 2", "score", "alt_group_score", "pos_diff_score",
			"rel_dist_diff_score", "size_diff_score"])

		for pair in design_pairs: 
			exp_id = pair["exp_id"]
			exp_id_split = exp_id.split("_")
			participant_id = exp_id_split[0]
			order = exp_id_split[1]
			experience_level = exp_id_split[2]
			condition = exp_id_split[3]
			task = exp_id_split[4]
			pair1 = pair["di"]["elements"]["name"]
			pair2 = pair["dj"]["elements"]["name"]
			score = pair["score"]
			alt = pair["score_detail"]["alt_group_score"]
			pos = pair["score_detail"]["pos_diff_score"]
			size = pair["score_detail"]["size_diff_score"]
			rel = pair["score_detail"]["rel_dist_diff_score"]
			diversity_writer.writerow([participant_id, experience_level, order, task, condition, pair1, pair2, score, alt, pos, size, rel])

if __name__ == '__main__':
	data_folder = sys.argv[1] 
	results = analyze_diversity(data_folder)
	output_results(results, data_folder)