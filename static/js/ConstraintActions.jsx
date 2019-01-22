
// Feedback items
// Groups - Order, Size
// Global - Whitespace, Density 
class ConstraintActions {}

ConstraintActions.locked_size_key = 'size'
ConstraintActions.locked_arrangement_key = 'arrangement'; 
ConstraintActions.locked_alignment_key = 'alignment';
ConstraintActions.locked_justification_key = 'justification';
ConstraintActions.locked_distribution_key = 'distribution';
ConstraintActions.locked_grid_key = 'grid';


// Keep these here for now. Update when we have any more possible arrangement patterns
ConstraintActions.horizontalArrangements = ["horizontal", "rows"];
ConstraintActions.verticalArrangements = ["vertical", "columns"];
ConstraintActions.arrangments = ["horizontal", "vertical", "rows", "columns"]; 
ConstraintActions.verticalAlignments = ["left", "center", "right"];
ConstraintActions.horizontalAlignments = ["top", "center", "bottom"];

ConstraintActions.arrangements = ["horizontal", "vertical", "rows", "columns"];
ConstraintActions.justifications = ["top", "center", "bottom"];

ConstraintActions.locked_proximity_key = 'proximity'; 
ConstraintActions.locked_margin_key = 'margin';
ConstraintActions.locked_text_key = 'text';
ConstraintActions.locksKey = 'locks'; 

ConstraintActions.getAction = function getAction(lock, shape) {
	if(shape.type == "canvas") {
		let action = ConstraintActions.canvasConstraints[lock]; 
		if(action) {
			return action;
		}
	}else if(shape.type == "group") {
		let action = ConstraintActions.groupConstraints[lock]; 
		if(action){
			return action;
		}
	}
	else {
		let action = ConstraintActions.elementConstraints[lock]; 
		if(action){
			return action;
		}
	}
}

ConstraintActions.defaultKeepConstraint = function keepConstraint(constraintsCanvasShape, designCanvasShape, constraintKey) {
  	if(constraintsCanvasShape[ConstraintActions.locksKey] == undefined) {
		constraintsCanvasShape[ConstraintActions.locksKey] = []; 
	} 

	if(constraintsCanvasShape[ConstraintActions.locksKey].indexOf(constraintKey) == -1) {
		constraintsCanvasShape[ConstraintActions.locksKey].push(constraintKey); 
	}

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
	return "Don't keep the " + constraintKey + " " + value;
}

ConstraintActions.elementConstraints = {
	"x" : {
		"do": {
			"key": "x",
			"updateConstraintsCanvasShape": function keepPosition(constraintsCanvasShape, designCanvasShape) {
			    // Update the property on shape according to the selected option
			    // Use the server key for locking a shape into a specific location
			    if(constraintsCanvasShape[ConstraintActions.locksKey] == undefined) {
			    	constraintsCanvasShape[ConstraintActions.locksKey] = []; 
			    } 

			    constraintsCanvasShape[ConstraintActions.locksKey].push("x"); 
			    let y_val = constraintsCanvasShape["y"] ? constraintsCanvasShape["y"] : 0; 
			    constraintsCanvasShape["x"] = designCanvasShape["x"]; 
			    constraintsCanvasShape["y"] = y_val; 
			}, 
			"getFeedbackMessage": function generateFeedbackMessage(shape) {
				return "Keep x location at " + shape["x"] + "px.";
			}
		}, 
		"undo": {
			"key": "x",
			"updateConstraintsCanvasShape": function undoKeepPosition(constraintsCanvasShape, designCanvasShape) {
				let index = constraintsCanvasShape[ConstraintActions.locksKey].indexOf("x"); 
				constraintsCanvasShape[ConstraintActions.locksKey].splice(index,1); 
				if(!constraintsCanvasShape[ConstraintActions.locksKey].length) {
					delete constraintsCanvasShape[ConstraintActions.locksKey]; 
				}
			}, 
			"getFeedbackMessage": function generateFeedbackMessage(shape) {
				return "Don't keep x location at " + shape["x"] + "px.";
			}
		}
	}, 
	"y" : {
		"do": {
			"key": "y",
			"updateConstraintsCanvasShape": function keepPosition(constraintsCanvasShape, designCanvasShape) {
			    // Update the property on shape according to the selected option
			    // Use the server key for locking a shape into a specific location
			    if(constraintsCanvasShape[ConstraintActions.locksKey] == undefined) {
			    	constraintsCanvasShape[ConstraintActions.locksKey] = []; 
			    } 

			    constraintsCanvasShape[ConstraintActions.locksKey].push("y"); 
			    let x_val = constraintsCanvasShape["x"] ? constraintsCanvasShape["x"] : 0; 
			    constraintsCanvasShape["x"] = x_val; 
			    constraintsCanvasShape["y"] = designCanvasShape["y"];
			}, 
			"getFeedbackMessage": function generateFeedbackMessage(shape) {
				return "Keep y location at " + shape["y"] + "px.";
			}
		}, 
		"undo": {
			"key": "y",
			"updateConstraintsCanvasShape": function undoKeepPosition(constraintsCanvasShape, designCanvasShape) {
				let index = constraintsCanvasShape[ConstraintActions.locksKey].indexOf("y"); 
				constraintsCanvasShape[ConstraintActions.locksKey].splice(index,1); 
				if(!constraintsCanvasShape[ConstraintActions.locksKey].length) {
					delete constraintsCanvasShape[ConstraintActions.locksKey]; 
				}
			}, 
			"getFeedbackMessage": function generateFeedbackMessage(shape) {
				return "Don't keep y location at " + shape["y"] + "px.";
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
				let index = constraintsCanvasShape[ConstraintActions.locksKey].indexOf(ConstraintActions.locked_size_key); 
				constraintsCanvasShape[ConstraintActions.locksKey].splice(index,1); 
				if(!constraintsCanvasShape[ConstraintActions.locksKey].length) {
					delete constraintsCanvasShape[ConstraintActions.locksKey]; 
				}
			}, 
			"getFeedbackMessage": function generateFeedbackMessage(shape) {
				return "Don't keep width at " + shape[ConstraintActions.locked_size_key]["width"] + "px.";
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
				let indsex = constraintsCanvasShape[ConstraintActions.locksKey].indexOf(ConstraintActions.locked_size_key); 
				constraintsCanvasShape[ConstraintActions.locksKey].splice(index,1); 
				if(!constraintsCanvasShape[ConstraintActions.locksKey].length) {
					delete constraintsCanvasShape[ConstraintActions.locksKey]; 
				}; 
			}, 
			"getFeedbackMessage": function generateFeedbackMessage(shape) {
				return "Don't keep height at " + shape[ConstraintActions.locked_size_key]["height"] + "px.";
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
					let alignmentValue = ConstraintActions.verticalAlignments[shape[ConstraintActions.locked_alignment_key]];
					let arrangementValue = ConstraintActions.arrangments[shape[ConstraintActions.locked_arrangement_key]]; 
					if(ConstraintActions.horizontalArrangements.indexOf(arrangementValue) > -1) {
						alignmentValue = ConstraintActions.horizontalAlignments[shape[ConstraintActions.locked_alignment_key]]; 
					}

					return ConstraintActions.defaultFeedbackMessage(ConstraintActions.locked_alignment_key, alignmentValue) + ".";
				}
			}, 
			"undo": {
				"key": ConstraintActions.locked_alignment_key,
				"updateConstraintsCanvasShape": function undoKeepAlignment(constraintsCanvasShape, designCanvasShape) {
					ConstraintActions.defaultUndoKeepConstraint(constraintsCanvasShape, designCanvasShape, ConstraintActions.locked_alignment_key);
				},
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					let alignmentValue = ConstraintActions.verticalAlignments[shape[ConstraintActions.locked_alignment_key]];
					let arrangementValue = ConstraintActions.arrangments[shape[ConstraintActions.locked_arrangement_key]]; 
					if(ConstraintActions.horizontalArrangements.indexOf(arrangementValue) > -1) {
						alignmentValue = ConstraintActions.horizontalAlignments[shape[ConstraintActions.locked_alignment_key]]; 
					}

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
					ConstraintActions.defaultKeepConstraint(constraintsCanvasShape, designCanvasShape, ConstraintActions.locked_distribution_key);
				}, 
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					let distributionValue = shape[ConstraintActions.locked_distribution_key];
					return ConstraintActions.defaultFeedbackMessage(ConstraintActions.locked_distribution_key, distributionValue) + "px.";
				}
			}, 
			"undo": {
				"key": ConstraintActions.locked_justification_key,
				"updateConstraintsCanvasShape": function undoKeepDistribution(constraintsCanvasShape, designCanvasShape) {
					ConstraintActions.defaultUndoKeepConstraint(constraintsCanvasShape, designCanvasShape, ConstraintActions.locked_distribution_key);
				},
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					let distributionValue = shape[ConstraintActions.locked_distribution_key]; 
					return ConstraintActions.defaultUndoFeedbackMessage(ConstraintActions.locked_distribution_key, distributionValue) + "px.";
				}
			}
		},
	"order": 
		{
			"do": {
				"key": "order",
				"updateConstraintsCanvasShape": function keepOrder(constraintsCanvasShape, designCanvasShape) {
					/**
					 TBD  
					*/
				}, 
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					
					return "Keep this order. (TBD)";
				}
			}, 
			"undo": {
				"key": ConstraintActions.locked_arrangement_key,
				"updateConstraintsCanvasShape": function undoKeepArrangement(constraintsCanvasShape, designCanvasShape) {
					/** 
					 TBD 
					*/
				},
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					return "Don't keep this order. (TBD)";
				}
			}
		},
	"width": {
		"do": {
			"key": "width",
			"updateConstraintsCanvasShape": function keepSize(constraintsCanvasShape, designCanvasShape) {
			    // Update the property on shape according to the selected option
			    // Use the server key for locking a shape into a specific location
			    /* TBD */
			}, 
			"getFeedbackMessage": function generateFeedbackMessage(shape) {
				return "Keep width at " + shape["width"] + "px. (TBD)";
			}
		}, 
		"undo": {
			"key": "width",
			"updateConstraintsCanvasShape": function undoKeepSize(constraintsCanvasShape, designCanvasShape) {
				/* TBD */
			}, 
			"getFeedbackMessage": function generateFeedbackMessage(shape) {
				return "Don't keep width at " + shape["width"] + "px. (TBD)";
			}
		}	
	}, 
	"height": {
		"do": {
			"key": "height",
			"updateConstraintsCanvasShape": function keepSize(constraintsCanvasShape, designCanvasShape) {
			    // Update the property on shape according to the selected option
			    // Use the server key for locking a shape into a specific location
			    /* TBD */ 
			}, 
			"getFeedbackMessage": function generateFeedbackMessage(shape) {
				return "Keep height at " + shape["height"] + "px. (TBD)";
			}
		}, 
		"undo": {
			"key": "height",
			"updateConstraintsCanvasShape": function undoKeepPosition(constraintsCanvasShape, designCanvasShape) {
				/* TBD */ 
			}, 
			"getFeedbackMessage": function generateFeedbackMessage(shape) {
				return "Don't keep height at " + shape["height"] + "px. (TBD)";
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
					return "Keep the " + ConstraintActions.locked_margin_key + " at " + shape[ConstraintActions.locked_margin_key] + "px.";
				}
			}, 
			"undo": {
				"key": ConstraintActions.locked_proximity_key,
				"updateConstraintsCanvasShape": function undoKeepProximity(constraintsCanvasShape, designCanvasShape) {
					let index = constraintsCanvasShape[ConstraintActions.locksKey].indexOf(ConstraintActions.locked_margin_key); 
					constraintsCanvasShape[ConstraintActions.locksKey].splice(index,1); 
					if(!constraintsCanvasShape[ConstraintActions.locksKey].length) {
						delete constraintsCanvasShape[ConstraintActions.locksKey]; 
					}

					delete constraintsCanvasShape[ConstraintActions.locked_margin_key]; 
				}, 
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					return "Don't keep " + ConstraintActions.locked_margin_key + " at " + shape[ConstraintActions.locked_margin_key] + "px.";
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
					let alignmentValue = ConstraintActions.verticalAlignments[shape[ConstraintActions.locked_alignment_key]];
					let arrangementValue = ConstraintActions.arrangments[shape[ConstraintActions.locked_arrangement_key]]; 
					if(ConstraintActions.horizontalArrangements.indexOf(arrangementValue) > -1) {
						alignmentValue = ConstraintActions.horizontalAlignments[shape[ConstraintActions.locked_alignment_key]]; 
					}

					return ConstraintActions.defaultFeedbackMessage(ConstraintActions.locked_alignment_key, alignmentValue) + ".";
				}
			}, 
			"undo": {
				"key": ConstraintActions.locked_alignment_key,
				"updateConstraintsCanvasShape": function undoKeepAlignment(constraintsCanvasShape, designCanvasShape) {
					ConstraintActions.defaultUndoKeepConstraint(constraintsCanvasShape, designCanvasShape, ConstraintActions.locked_alignment_key);
				},
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					let alignmentValue = ConstraintActions.verticalAlignments[shape[ConstraintActions.locked_alignment_key]];
					let arrangementValue = ConstraintActions.arrangments[shape[ConstraintActions.locked_arrangement_key]]; 
					if(ConstraintActions.horizontalArrangements.indexOf(arrangementValue) > -1) {
						alignmentValue = ConstraintActions.horizontalAlignments[shape[ConstraintActions.locked_alignment_key]]; 
					}

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
				"updateConstraintsCanvasShape": function keepGrid(constraintsCanvasShape, designCanvasShape) {
					ConstraintActions.defaultKeepConstraint(constraintsCanvasShape, designCanvasShape, ConstraintActions.locked_grid_key);
				}, 
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					return "Keep the " + ConstraintActions.locked_grid_key + " at " + shape[ConstraintActions.locked_grid_key] + "px.";
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
		}, 
	// "background_color": 
	// 	{
	// 		"do": {
	// 			"key": "background_color",
	// 			"updateConstraintsCanvasShape": function keepBackgroundColor(constraintsCanvasShape, designCanvasShape) {
	// 				ConstraintActions.defaultKeepConstraint(constraintsCanvasShape, designCanvasShape, "background_color");
	// 			}, 
	// 			"getFeedbackMessage": function generateFeedbackMessage(shape) {
	// 				return "Keep the background color.";
	// 			}
	// 		}, 
	// 		"undo": {
	// 			"key": "background_color",
	// 			"updateConstraintsCanvasShape": function undoKeepBackgroundColor(constraintsCanvasShape, designCanvasShape) {
	// 				ConstraintActions.defaultUndoKeepConstraint(constraintsCanvasShape, designCanvasShape, "background_color");
	// 			},
	// 			"getFeedbackMessage": function generateFeedbackMessage(shape) {
	// 				return "Don't keep the background color.";
	// 			}
	// 		}
	// 	},
	"density": 
		{
			"do": {
				"key": "density",
				"updateConstraintsCanvasShape": function keepDensity(constraintsCanvasShape, designCanvasShape) {
					/* TBD */ 
				}, 
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					return "Keep the density. (TBD)";
				}
			}, 
			"undo": {
				"key": "desnity",
				"updateConstraintsCanvasShape": function undoKeepDenity(constraintsCanvasShape, designCanvasShape) {
					/* TBD */ 
				},
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					return "Don't keep the density. (TBD)";
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
