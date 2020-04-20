import sys
import os
import csv
import cost_model
import os
import json
import sys

from pprint import pprint

OUTPUT_FILE = "diversity_scores.csv"

def load_by_designer_tool(export_dir):
    """the directory containing exported designs, 
        there is a group for each designer and each tool"""

    all_designs = {}
    for dirname in os.listdir(export_dir):
        design_dir = os.path.join(export_dir, dirname)
        if not os.path.isdir(design_dir):
            continue

        # load paths for saved images, relates to saved designs by their canvas ids
        img_dir = os.path.join(design_dir, "images")
        img_file_names = {}
        for fname in os.listdir(img_dir):
            if fname.endswith(".png"):
                if "Alternative 1" in fname:
                    design_id = "Alternative 1"
                elif "Alternative 2" in fname:
                    design_id = "Alternative 2"
                elif "Alternative 3" in fname:
                    design_id = "Alternative 3"
                elif "Original" in fname:
                    design_id = "Original"
                img_file_names[design_id] = os.path.join(img_dir, fname)

        group_id = dirname
        designs = []
        with open(os.path.join(design_dir, "saved.json")) as f:
            for d in json.load(f)["saved"]:
                d["img_path"] = img_file_names[d["elements"]["name"]]
                designs.append(d)

        if group_id not in all_designs:
            all_designs[group_id] = []
        all_designs[group_id] += designs

    return all_designs


def load_by_tool(export_dir):
    """the directory containing exported designs, 
        there is a group for each tool"""

    all_designs = {}
    for dirname in os.listdir(export_dir):
        design_dir = os.path.join(export_dir, dirname)
        if not os.path.isdir(design_dir):
            continue

        # load paths for saved images, relates to saved designs by their canvas ids
        img_dir = os.path.join(design_dir, "images")
        img_file_names = {}
        for fname in os.listdir(img_dir):
            if fname.endswith(".png"):
                if "Alternative 1" in fname:
                    design_id = "Alternative 1"
                elif "Alternative 2" in fname:
                    design_id = "Alternative 2"
                elif "Alternative 3" in fname:
                    design_id = "Alternative 3"
                elif "Original" in fname:
                    design_id = "Original"
                img_file_names[design_id] = os.path.join(img_dir, fname)

        group_id = "baseline" if "baseline" in dirname else "scout"
        designs = []
        with open(os.path.join(design_dir, "saved.json")) as f:
            for d in json.load(f)["saved"]:
                d["img_path"] = img_file_names[d["elements"]["name"]]
                d["exp_id"] = dirname
                designs.append(d)

        if group_id not in all_designs:
            all_designs[group_id] = []
        all_designs[group_id] += designs

    return all_designs

def analyze_design(all_designs):
    """ Analyze design scores from all saved apps, the scores are normalized across all designs
        For each pair of saved designs in each file, display their diversity score as well as svgs
        Inputs:
            all_designs: a list of saved designs (saved.json)
    """

    raw_diversity_score = {}
    for group_id, designs in all_designs.items():

        for i in range(len(designs)):
            for j in range(i + 1, len(designs)):
                di, dj = designs[i], designs[j]
                #diversity_score, diff = cost_model.compute_diversity_score(di["elements"], dj["elements"])

                unnormalized_score =  cost_model.compute_unnormalized_diversity_score(di["elements"], dj["elements"])


                raw_diversity_score[(group_id, i, j)] ={
                    "unnormalized_score": unnormalized_score,
                    "exp_id1": di["exp_id"],
                    "exp_id2": dj["exp_id"]
                }

    final_scores = cost_model.normalize_diversity_scores(raw_diversity_score)

    design_pairs = []
    for pair_id in final_scores:
        group_id, i,j = pair_id
        score = (final_scores[pair_id]["alt_group_score"]
                    + final_scores[pair_id]["pos_diff_score"]
                    + final_scores[pair_id]["rel_dist_diff_score"]
                    + 2 * final_scores[pair_id]["size_diff_score"])
        design_pair = {
            "group_id": group_id,
            "score": score,
            "score_detail": final_scores[pair_id],
            "di": all_designs[group_id][i],
            "dj": all_designs[group_id][j],
            "exp_id1": final_scores[pair_id]["exp_id1"], 
            "exp_id2": final_scores[pair_id]["exp_id2"]
        }

        design_pairs.append(design_pair)
    return design_pairs

def analyze_diversity(folder):
    """ Analyze sets of designs within a folder """
    all_designs = load_by_tool(folder)
    design_pairs = analyze_design(all_designs)
    return design_pairs

def output_all_pairs_results(design_pairs, output_folder):
    """ Output the results into a CSV """
    csv_output_path = os.path.join(output_folder, OUTPUT_FILE)
    with open(csv_output_path, mode='w') as diversity_file:
        diversity_writer = csv.writer(diversity_file, delimiter=',',
            quotechar='"')
        diversity_writer.writerow(["Participant ID - 1", "Experience Level - 1", "Order - 1", "Task - 1", "Condition - 1", 
            "Participant ID - 2", "Experience Level - 2", "Order - 2",  "Task - 2", "Condition - 2",
            "Pair 1", "Pair 2", "score", "alt_group_score", "pos_diff_score",
            "rel_dist_diff_score", "size_diff_score"])

        for pair in design_pairs:
            # First design in the pair
            exp_id1 = pair["exp_id1"]
            exp_id1_split = exp_id1.split("_")
            participant_id1 = exp_id1_split[0]
            order1 = exp_id1_split[1]
            experience_level1 = exp_id1_split[2]
            condition1 = exp_id1_split[3]
            task1 = exp_id1_split[4]

            # Second design in the pair
            exp_id2 = pair["exp_id2"]
            exp_id2_split = exp_id2.split("_")
            participant_id2 = exp_id2_split[0]
            order2 = exp_id2_split[1]
            experience_level2 = exp_id2_split[2]
            condition2 = exp_id2_split[3]
            task2 = exp_id2_split[4]
                  
            pair1 = pair["di"]["elements"]["name"]
            pair2 = pair["dj"]["elements"]["name"]
            score = pair["score"]
            alt = pair["score_detail"]["alt_group_score"]
            pos = pair["score_detail"]["pos_diff_score"]
            size = pair["score_detail"]["size_diff_score"]
            rel = pair["score_detail"]["rel_dist_diff_score"]
            diversity_writer.writerow([participant_id1, experience_level1, order1, task1, condition1, 
                participant_id2, experience_level2, order2, task2, condition2, pair1, pair2, score, alt, pos, size, rel])

if __name__ == '__main__':
    data_folder = sys.argv[1]
    results = analyze_diversity(data_folder)
    output_all_pairs_results(results, data_folder)