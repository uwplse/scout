import Constants from "./Constants"; 

class ConstraintActions {}
ConstraintActions.locked_location_key = 'location'; 
ConstraintActions.locked_size_key = 'size'
ConstraintActions.locked_arrangement_key = 'arrangement'; 
ConstraintActions.locked_alignment_key = 'alignment';
ConstraintActions.locked_justification_key = 'justification';
ConstraintActions.locked_distribution_key = 'distribution';
ConstraintActions.locked_grid_key = 'grid';


// Keep these here for now. Update when we have any more possible arrangement patterns
ConstraintActions.arrangements = ["horizontal", "vertical", "rows", "columns"];
ConstraintActions.alignments = ["left", "center", "right"];
ConstraintActions.justifications = ["top", "center", "bottom"];
ConstraintActions.proximities = [10,20,30,40,50];
ConstraintActions.grids = [5];
ConstraintActions.distributions = [20,40,60,80,100,120,140,160,180,200,220,240,260,280,300,320,340,360,380,400];

ConstraintActions.locked_proximity_key = 'proximity'; 
ConstraintActions.locked_margin_key = 'margin';
ConstraintActions.locked_text_key = 'text';
ConstraintActions.locksKey = 'locks'; 

ConstraintActions.defaultKeepConstraint = function keepConstraint(constraintsCanvasShape, designCanvasShape, constraintKey) {
  	if(constraintsCanvasShape[ConstraintActions.locksKey] == undefined) {
		constraintsCanvasShape[ConstraintActions.locksKey] = []; 
	} 

	constraintsCanvasShape[ConstraintActions.locksKey].push(constraintKey); 

	// Also should the constraints canvas arrange itself in the way of the designs canvas?
	// Update the constraint property on the object
	constraintsCanvasShape[constraintKey] = designCanvasShape[constraintKey]; 	
}

ConstraintActions.defaultUndoKeepConstraint = function undoKeepConstraint(constraintsCanvasShape, designCanvasShape, constraintKey) {
	var index = constraintsCanvasShape[ConstraintActions.locksKey].indexOf(constraintKey); 
	constraintsCanvasShape[ConstraintActions.locksKey].splice(index,1); 
	if(!constraintsCanvasShape[ConstraintActions.locksKey].length) {
		delete constraintsCanvasShape[ConstraintActions.locksKey]; 
	}

	delete constraintsCanvasShape[constraintKey]; 
}

ConstraintActions.defaultFeedbackMessage = function feedbackMessage(constraintKey, value) {
	return "Keep the " + constraintKey + " " + value;	
}

ConstraintActions.defaultUndoFeedbackMessage = function undoFeedbackMessage(constraintKey, value) {
	return "Unlock " + constraintKey + " from " + value;
}

ConstraintActions.elementConstraints = {
	"x" : {
		"do": {
			"key": ConstraintActions.locked_location_key,
			"updateConstraintsCanvasShape": function keepPosition(constraintsCanvasShape, designCanvasShape) {
			    // Update the property on shape according to the selected option
			    // Use the server key for locking a shape into a specific location
			    if(constraintsCanvasShape[ConstraintActions.locksKey] == undefined) {
			    	constraintsCanvasShape[ConstraintActions.locksKey] = []; 
			    } 

			    constraintsCanvasShape[ConstraintActions.locksKey].push("x"); 
			    let y_val = constraintsCanvasShape[ConstraintActions.locked_location_key] ? constraintsCanvasShape[ConstraintActions.locked_location_key]["y"] : 0; 
			    constraintsCanvasShape[ConstraintActions.locked_location_key] = {
			    	x: designCanvasShape[ConstraintActions.locked_location_key]["x"], 
			    	y: y_val
			    }
			}, 
			"getFeedbackMessage": function generateFeedbackMessage(shape) {
				return "Keep x position at " + shape[ConstraintActions.locked_location_key]["x"] + "px.";
			}
		}, 
		"undo": {
			"key": ConstraintActions.locked_location_key,
			"updateConstraintsCanvasShape": function undoKeepPosition(constraintsCanvasShape, designCanvasShape) {
				var index = constraintsCanvasShape[ConstraintActions.locksKey].indexOf("x"); 
				constraintsCanvasShape[ConstraintActions.locksKey].splice(index,1); 
				if(!constraintsCanvasShape[ConstraintActions.locksKey].length) {
					delete constraintsCanvasShape[ConstraintActions.locksKey]; 
				}
			}, 
			"getFeedbackMessage": function generateFeedbackMessage(shape) {
				return "Unlock x position from " + shape[ConstraintActions.locked_location_key]["x"] + "px.";
			}
		}
	}, 
	"y" : {
		"do": {
			"key": ConstraintActions.locked_location_key,
			"updateConstraintsCanvasShape": function keepPosition(constraintsCanvasShape, designCanvasShape) {
			    // Update the property on shape according to the selected option
			    // Use the server key for locking a shape into a specific location
			    if(constraintsCanvasShape[ConstraintActions.locksKey] == undefined) {
			    	constraintsCanvasShape[ConstraintActions.locksKey] = []; 
			    } 

			    constraintsCanvasShape[ConstraintActions.locksKey].push("y"); 
			    let x_val = constraintsCanvasShape[ConstraintActions.locked_location_key] ? constraintsCanvasShape[ConstraintActions.locked_location_key]["x"] : 0; 
			    constraintsCanvasShape[ConstraintActions.locked_location_key] = {
			    	x: x_val, 
			    	y: designCanvasShape[ConstraintActions.locked_location_key]["y"]
			    }
			}, 
			"getFeedbackMessage": function generateFeedbackMessage(shape) {
				return "Keep y position at " + shape[ConstraintActions.locked_location_key]["y"] + "px.";
			}
		}, 
		"undo": {
			"key": ConstraintActions.locked_location_key,
			"updateConstraintsCanvasShape": function undoKeepPosition(constraintsCanvasShape, designCanvasShape) {
				var index = constraintsCanvasShape[ConstraintActions.locksKey].indexOf("y"); 
				constraintsCanvasShape[ConstraintActions.locksKey].splice(index,1); 
				if(!constraintsCanvasShape[ConstraintActions.locksKey].length) {
					delete constraintsCanvasShape[ConstraintActions.locksKey]; 
				}
			}, 
			"getFeedbackMessage": function generateFeedbackMessage(shape) {
				return "Unlock y position from " + shape[ConstraintActions.locked_location_key]["y"] + "px.";
			}
		}
	}, 
	"width": {
		"do": {
			"key": ConstraintActions.locked_size_key,
			"updateConstraintsCanvasShape": function keepSize(constraintsCanvasShape, designCanvasShape) {
			    // Update the property on shape according to the selected option
			    // Use the server key for locking a shape into a specific location
			    if(constraintsCanvasShape[ConstraintActions.locksKey] == undefined) {
			    	constraintsCanvasShape[ConstraintActions.locksKey] = []; 
			    } 

			    constraintsCanvasShape[ConstraintActions.locksKey].push("width"); 
			    height_val = constraintsCanvasShape[ConstraintActions.locked_size_key]["height"]; 
			    constraintsCanvasShape[ConstraintActions.locked_size_key] = {
			    	width: designCanvasShape[ConstraintActions.locked_size_key]["width"], 
			    	height: height_val
			    }
			}, 
			"getFeedbackMessage": function generateFeedbackMessage(shape) {
				return "Keep width at " + shape[ConstraintActions.locked_size_key]["width"] + "px.";
			}
		}, 
		"undo": {
			"key": ConstraintActions.locked_size_key,
			"updateConstraintsCanvasShape": function undoKeepPosition(constraintsCanvasShape, designCanvasShape) {
				var index = constraintsCanvasShape[ConstraintActions.locksKey].indexOf(ConstraintActions.locked_size_key); 
				constraintsCanvasShape[ConstraintActions.locksKey].splice(index,1); 
				if(!constraintsCanvasShape[ConstraintActions.locksKey].length) {
					delete constraintsCanvasShape[ConstraintActions.locksKey]; 
				}
			}, 
			"getFeedbackMessage": function generateFeedbackMessage(shape) {
				return "Unlock width from " + shape[ConstraintActions.locked_size_key]["width"] + "px.";
			}
		}	
	}, 
	"height": {
		"do": {
			"key": ConstraintActions.locked_size_key,
			"updateConstraintsCanvasShape": function keepSize(constraintsCanvasShape, designCanvasShape) {
			    // Update the property on shape according to the selected option
			    // Use the server key for locking a shape into a specific location
			    if(constraintsCanvasShape[ConstraintActions.locksKey] == undefined) {
			    	constraintsCanvasShape[ConstraintActions.locksKey] = []; 
			    } 

			    constraintsCanvasShape[ConstraintActions.locksKey].push("height"); 
			    width_val = constraintsCanvasShape[ConstraintActions.locked_size_key]["width"]; 
			    constraintsCanvasShape[ConstraintActions.locked_size_key] = {
			    	width: width_val, 
			    	height: designCanvasShape[ConstraintActions.locked_size_key]["height"]
			    }
			}, 
			"getFeedbackMessage": function generateFeedbackMessage(shape) {
				return "Keep height at " + shape[ConstraintActions.locked_size_key]["height"] + "px.";
			}
		}, 
		"undo": {
			"key": ConstraintActions.locked_size_key,
			"updateConstraintsCanvasShape": function undoKeepPosition(constraintsCanvasShape, designCanvasShape) {
				var index = constraintsCanvasShape[ConstraintActions.locksKey].indexOf(ConstraintActions.locked_size_key); 
				constraintsCanvasShape[ConstraintActions.locksKey].splice(index,1); 
				if(!constraintsCanvasShape[ConstraintActions.locksKey].length) {
					delete constraintsCanvasShape[ConstraintActions.locksKey]; 
				}; 
			}, 
			"getFeedbackMessage": function generateFeedbackMessage(shape) {
				return "Unlock height from " + shape[ConstraintActions.locked_size_key]["height"] + "px.";
			}
		}	
	}
}

ConstraintActions.groupConstraints = {
	"arrangement": 
		{
			"do": {
				"key": ConstraintActions.locked_arrangement_key,
				"updateConstraintsCanvasShape": function keepArrangment(constraintsCanvasShape, designCanvasShape) {
					ConstraintActions.defaultKeepConstraint(constraintsCanvasShape, designCanvasShape, ConstraintActions.locked_arrangement_key);
				}, 
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					let arrangementValue = ConstraintActions.arrangements[shape[ConstraintActions.locked_arrangement_key]];
					return ConstraintActions.defaultFeedbackMessage(ConstraintActions.locked_arrangement_key, arrangementValue) + ".";
				}
			}, 
			"undo": {
				"key": ConstraintActions.locked_arrangement_key,
				"updateConstraintsCanvasShape": function undoKeepArrangement(constraintsCanvasShape, designCanvasShape) {
					ConstraintActions.defaultUndoKeepConstraint(constraintsCanvasShape, designCanvasShape, ConstraintActions.locked_arrangement_key);
				},
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					let arrangementValue = ConstraintActions.arrangements[shape[ConstraintActions.locked_arrangement_key]]; 
					return ConstraintActions.defaultUndoFeedbackMessage(ConstraintActions.locked_arrangement_key, arrangementValue) + ".";
				}
			}
		}, 
	"alignment": 
		{
			"do": {
				"key": ConstraintActions.locked_alignment_key,
				"updateConstraintsCanvasShape": function keepAlignment(constraintsCanvasShape, designCanvasShape) {
					ConstraintActions.defaultKeepConstraint(constraintsCanvasShape, designCanvasShape, ConstraintActions.locked_alignment_key);
				}, 
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					let alignmentValue = ConstraintActions.alignments[shape[ConstraintActions.locked_alignment_key]];
					return ConstraintActions.defaultFeedbackMessage(ConstraintActions.locked_alignment_key, alignmentValue) + ".";
				}
			}, 
			"undo": {
				"key": ConstraintActions.locked_alignment_key,
				"updateConstraintsCanvasShape": function undoKeepAlignment(constraintsCanvasShape, designCanvasShape) {
					ConstraintActions.defaultUndoKeepConstraint(constraintsCanvasShape, designCanvasShape, ConstraintActions.locked_alignment_key);
				},
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					let alignmentValue = ConstraintActions.alignments[shape[ConstraintActions.locked_alignment_key]]; 
					return ConstraintActions.defaultUndoFeedbackMessage(ConstraintActions.locked_alignment_key, alignmentValue) + ".";
				}
			}
		}, 
	"proximity": 
		{
			"do": {
				"key": ConstraintActions.locked_proximity_key,
				"updateConstraintsCanvasShape": function keepProximity(constraintsCanvasShape, designCanvasShape) {
					ConstraintActions.defaultKeepConstraint(constraintsCanvasShape, designCanvasShape, ConstraintActions.locked_proximity_key);
				}, 
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					let proximityValue = shape[ConstraintActions.locked_proximity_key];
					return ConstraintActions.defaultFeedbackMessage(ConstraintActions.locked_proximity_key, proximityValue) + "px.";
				}
			}, 
			"undo": {
				"key": ConstraintActions.locked_proximity_key,
				"updateConstraintsCanvasShape": function undoKeepProximity(constraintsCanvasShape, designCanvasShape) {
					ConstraintActions.defaultUndoKeepConstraint(constraintsCanvasShape, designCanvasShape, ConstraintActions.locked_proximity_key);
				},
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					let proximityValue = shape[ConstraintActions.locked_proximity_key]; 
					return ConstraintActions.defaultUndoFeedbackMessage(ConstraintActions.locked_proximity_key, proximityValue) + "px.";
				}
			}
		}, 
	"distribution": 
		{
			"do": {
				"key": ConstraintActions.locked_distribution_key,
				"updateConstraintsCanvasShape": function keepDistribution(constraintsCanvasShape, designCanvasShape) {
					ConstraintActions.defaultKeepConstraint(constraintsCanvasShape, designCanvasShape, ConstraintActions.locked_justification_key);
				}, 
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					let distributionValue = shape[ConstraintActions.locked_distribution_key];
					return ConstraintActions.defaultFeedbackMessage(ConstraintActions.locked_distribution_key, distributionValue) + "px.";
				}
			}, 
			"undo": {
				"key": ConstraintActions.locked_justification_key,
				"updateConstraintsCanvasShape": function undoKeepDistribution(constraintsCanvasShape, designCanvasShape) {
					ConstraintActions.defaultUndoKeepConstraint(constraintsCanvasShape, designCanvasShape, ConstraintActions.locked_justification_key);
				},
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					let distributionValue = shape[ConstraintActions.locked_distribution_key]; 
					return ConstraintActions.defaultUndoFeedbackMessage(ConstraintActions.locked_distribution_key, distributionValue) + "px.";
				}
			}
		}
}

ConstraintActions.canvasConstraints = {
	"margin": 
		{
			"do": {
				"key": ConstraintActions.locked_margin_key, 
				"updateConstraintsCanvasShape": function keepMargin(constraintsCanvasShape, designCanvasShape) {
				  	if(constraintsCanvasShape[ConstraintActions.locksKey] == undefined) {
						constraintsCanvasShape[ConstraintActions.locksKey] = []; 
					} 

			    	constraintsCanvasShape[ConstraintActions.locksKey].push(ConstraintActions.locked_margin_key); 

					// Also should the constraints canvas arrange itself in the way of the designs canvas?
					// Update the constraint property on the object
					constraintsCanvasShape[ConstraintActions.locked_margin_key] = designCanvasShape[ConstraintActions.locked_margin_key]; 
				}, 
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					return "Keep the global " + ConstraintActions.locked_margin_key + " at " + shape[ConstraintActions.locked_margin_key] + "px.";
				}
			}, 
			"undo": {
				"key": ConstraintActions.locked_proximity_key,
				"updateConstraintsCanvasShape": function undoKeepProximity(constraintsCanvasShape, designCanvasShape) {
					var index = constraintsCanvasShape[ConstraintActions.locksKey].indexOf(ConstraintActions.locked_margin_key); 
					constraintsCanvasShape[ConstraintActions.locksKey].splice(index,1); 
					if(!constraintsCanvasShape[ConstraintActions.locksKey].length) {
						delete constraintsCanvasShape[ConstraintActions.locksKey]; 
					}

					delete constraintsCanvasShape[ConstraintActions.locked_margin_key]; 
				}, 
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					return "Unlock " + ConstraintActions.locked_margin_key + " from " + shape[ConstraintActions.locked_margin_key] + "px.";
				}
			}
		},
	"alignment": 
		{
			"do": {
				"key": ConstraintActions.locked_alignment_key,
				"updateConstraintsCanvasShape": function keepAlignment(constraintsCanvasShape, designCanvasShape) {
					ConstraintActions.defaultKeepConstraint(constraintsCanvasShape, designCanvasShape, ConstraintActions.locked_alignment_key);
				}, 
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					let alignmentValue = ConstraintActions.alignments[shape[ConstraintActions.locked_alignment_key]];
					return ConstraintActions.defaultFeedbackMessage(ConstraintActions.locked_alignment_key, alignmentValue) + ".";
				}
			}, 
			"undo": {
				"key": ConstraintActions.locked_alignment_key,
				"updateConstraintsCanvasShape": function undoKeepAlignment(constraintsCanvasShape, designCanvasShape) {
					ConstraintActions.defaultUndoKeepConstraint(constraintsCanvasShape, designCanvasShape, ConstraintActions.locked_alignment_key);
				},
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					let alignmentValue = ConstraintActions.alignments[shape[ConstraintActions.locked_alignment_key]]; 
					return ConstraintActions.defaultUndoFeedbackMessage(ConstraintActions.locked_alignment_key, alignmentValue) + ".";
				}
			}
		}, 
	"justification": 
		{
			"do": {
				"key": ConstraintActions.locked_justification_key,
				"updateConstraintsCanvasShape": function keepJustification(constraintsCanvasShape, designCanvasShape) {
					ConstraintActions.defaultKeepConstraint(constraintsCanvasShape, designCanvasShape, ConstraintActions.locked_justification_key);
				}, 
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					let justificationValue = ConstraintActions.justifications[shape[ConstraintActions.locked_justification_key]];
					return ConstraintActions.defaultFeedbackMessage(ConstraintActions.locked_justification_key, justificationValue) + ".";
				}
			}, 
			"undo": {
				"key": ConstraintActions.locked_justification_key,
				"updateConstraintsCanvasShape": function undoKeepJustification(constraintsCanvasShape, designCanvasShape) {
					ConstraintActions.defaultUndoKeepConstraint(constraintsCanvasShape, designCanvasShape, ConstraintActions.locked_justification_key);
				},
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					let justificationValue = ConstraintActions.justifications[shape[ConstraintActions.locked_justification_key]]; 
					return ConstraintActions.defaultUndoFeedbackMessage(ConstraintActions.locked_justification_key, justificationValue) + ".";
				}
			}
		}, 
	"grid": 
		{
			"do": {
				"key": ConstraintActions.locked_grid_key = 'grid',
				"updateConstraintsCanvasShape": function keepJustification(constraintsCanvasShape, designCanvasShape) {
					ConstraintActions.defaultKeepConstraint(constraintsCanvasShape, designCanvasShape, ConstraintActions.locked_grid_key);
				}, 
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					return "Keep the global " + ConstraintActions.locked_grid_key + " at " + shape[ConstraintActions.locked_grid_key] + "px.";
				}
			}, 
			"undo": {
				"key": ConstraintActions.locked_grid_key,
				"updateConstraintsCanvasShape": function undoKeepGrid(constraintsCanvasShape, designCanvasShape) {
					ConstraintActions.defaultUndoKeepConstraint(constraintsCanvasShape, designCanvasShape, ConstraintActions.locked_grid_key);
				},
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					let gridValue = shape[ConstraintActions.locked_grid_key]; 
					return ConstraintActions.defaultUndoFeedbackMessage(ConstraintActions.locked_grid_key, gridValue) + "px.";
				}
			}
		}
}

// ConstraintActions.relationalConstraints = {
// 	"relative_alignment": {
// 		"types": ["left", "right", "x-center", "y-center", "top", "bottom"], 
// 		"do": {
// 			"label": function getLabel(type, id) {

// 			},
// 			"updateConstraintsCanvasShape": keepRelativeAlignment(type, des)

// 		}, 
// 		"undo":
// 	}
// }

export default ConstraintActions; 
