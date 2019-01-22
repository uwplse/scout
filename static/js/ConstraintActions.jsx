
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
			"key": "width",
			"updateConstraintsCanvasShape": function keepWidth(constraintsCanvasShape, designCanvasShape) {
			    // Update the property on shape according to the selected option
			    // Use the server key for locking a shape into a specific location
			    if(constraintsCanvasShape[ConstraintActions.locksKey] == undefined) {
			    	constraintsCanvasShape[ConstraintActions.locksKey] = []; 
			    } 

			    constraintsCanvasShape[ConstraintActions.locksKey].push("width"); 
			    constraintsCanvasShape["width"] = designCanvasShape["width"]
			}, 
			"getFeedbackMessage": function generateFeedbackMessage(shape) {
				return "Keep width at " + shape["width"] + "px.";
			}
		}, 
		"undo": {
			"key": "width",
			"updateConstraintsCanvasShape": function undoKeepWidth(constraintsCanvasShape, designCanvasShape) {
				let index = constraintsCanvasShape[ConstraintActions.locksKey].indexOf("width"); 
				constraintsCanvasShape[ConstraintActions.locksKey].splice(index,1); 
				if(!constraintsCanvasShape[ConstraintActions.locksKey].length) {
					delete constraintsCanvasShape[ConstraintActions.locksKey]; 
				}
			}, 
			"getFeedbackMessage": function generateFeedbackMessage(shape) {
				return "Don't keep width at " + shape["width"] + "px.";
			}
		}	
	}, 
	"height": {
		"do": {
			"key": "height",
			"updateConstraintsCanvasShape": function keepHeight(constraintsCanvasShape, designCanvasShape) {
			    // Update the property on shape according to the selected option
			    // Use the server key for locking a shape into a specific location
			    if(constraintsCanvasShape[ConstraintActions.locksKey] == undefined) {
			    	constraintsCanvasShape[ConstraintActions.locksKey] = []; 
			    } 

			    constraintsCanvasShape[ConstraintActions.locksKey].push("height"); 
			    constraintsCanvasShape["height"] = designCanvasShape["height"]; 
			}, 
			"getFeedbackMessage": function generateFeedbackMessage(shape) {
				return "Keep height at " + shape["height"] + "px.";
			}
		}, 
		"undo": {
			"key": "height",
			"updateConstraintsCanvasShape": function undoKeepHeight(constraintsCanvasShape, designCanvasShape) {
				let indsex = constraintsCanvasShape[ConstraintActions.locksKey].indexOf("height"); 
				constraintsCanvasShape[ConstraintActions.locksKey].splice(index,1); 
				if(!constraintsCanvasShape[ConstraintActions.locksKey].length) {
					delete constraintsCanvasShape[ConstraintActions.locksKey]; 
				}; 
			}, 
			"getFeedbackMessage": function generateFeedbackMessage(shape) {
				return "Don't keep height at " + shape["height"] + "px.";
			}
		}	
	}
}

// These actions will only appear for direct children of the canvas container
ConstraintActions.canvasChildConstraints = {
	"column": {
		"do": {
			"key": "column",
			"updateConstraintsCanvasShape": function keepColumn(constraintsCanvasShape, designCanvasShape) {
			    // Update the property on shape according to the selected option
			    // Use the server key for locking a shape into a specific location
			    if(constraintsCanvasShape[ConstraintActions.locksKey] == undefined) {
			    	constraintsCanvasShape[ConstraintActions.locksKey] = []; 
			    } 

			    constraintsCanvasShape[ConstraintActions.locksKey].push("column"); 
			    constraintsCanvasShape["column"] = designCanvasShape["column"]; 
			}, 
			"getFeedbackMessage": function generateFeedbackMessage(shape) {
				return "Keep column at " + shape["column"] + ".";
			}
		}, 
		"undo": {
			"key": "column",
			"updateConstraintsCanvasShape": function undoKeepColumn(constraintsCanvasShape, designCanvasShape) {
				let index = constraintsCanvasShape[ConstraintActions.locksKey].indexOf("column"); 
				constraintsCanvasShape[ConstraintActions.locksKey].splice(index,1); 
				if(!constraintsCanvasShape[ConstraintActions.locksKey].length) {
					delete constraintsCanvasShape[ConstraintActions.locksKey]; 
				}; 
			}, 
			"getFeedbackMessage": function generateFeedbackMessage(shape) {
				return "Don't keep column at " + shape["column"] + ".";
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
	"padding": 
		{
			"do": {
				"key": "padding",
				"updateConstraintsCanvasShape": function keepPadding(constraintsCanvasShape, designCanvasShape) {
					ConstraintActions.defaultKeepConstraint(constraintsCanvasShape, designCanvasShape, "padding");
				}, 
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					let paddingValue = shape["padding"];
					return ConstraintActions.defaultFeedbackMessage("padding", paddingValue) + "px.";
				}
			}, 
			"undo": {
				"key": "padding",
				"updateConstraintsCanvasShape": function undoKeepPadding(constraintsCanvasShape, designCanvasShape) {
					ConstraintActions.defaultUndoKeepConstraint(constraintsCanvasShape, designCanvasShape, "padding");
				},
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					let paddingValue = shape["padding"]; 
					return ConstraintActions.defaultUndoFeedbackMessage("padding", paddingValue) + "px.";
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
				"key": ConstraintActions.locked_margin_key,
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
	"baseline_grid": 
		{
			"do": {
				"key": "baseline_grid",
				"updateConstraintsCanvasShape": function keepBaselineGrid(constraintsCanvasShape, designCanvasShape) {
					ConstraintActions.defaultKeepConstraint(constraintsCanvasShape, designCanvasShape, "baseline_grid");
				}, 
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					let baselineGridValue = shape["baseline_grid"];
					return ConstraintActions.defaultFeedbackMessage("baseline_grid", baselineGridValue) + "px.";
				}
			}, 
			"undo": {
				"key": "baseline_grid",
				"updateConstraintsCanvasShape": function undoKeepBaselineGrid(constraintsCanvasShape, designCanvasShape) {
					ConstraintActions.defaultUndoKeepConstraint(constraintsCanvasShape, designCanvasShape, "baseline_grid");
				},
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					let baselineGridValue = shape["baseline_grid"]; 
					return ConstraintActions.defaultUndoFeedbackMessage("baseline_grid", baselineGridValue) + "px.";
				}
			}
		},	
	"gutter_width": 
		{
			"do": {
				"key": "gutter_width",
				"updateConstraintsCanvasShape": function keepGutterWidth(constraintsCanvasShape, designCanvasShape) {
					ConstraintActions.defaultKeepConstraint(constraintsCanvasShape, designCanvasShape, "gutter_width");
				}, 
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					let gwValue = shape["gutter_width"];
					return ConstraintActions.defaultFeedbackMessage("gutter_width", gwValue) + "px.";
				}
			}, 
			"undo": {
				"key": "gutter_width",
				"updateConstraintsCanvasShape": function undoKeepGutterWidth(constraintsCanvasShape, designCanvasShape) {
					ConstraintActions.defaultUndoKeepConstraint(constraintsCanvasShape, designCanvasShape, "gutter_width");
				},
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					let gwValue = shape["gutter_width"]; 
					return ConstraintActions.defaultUndoFeedbackMessage("gutter_width", gwValue) + "px.";
				}
			}
		},	
	"column_width": 
		{
			"do": {
				"key": "column_width",
				"updateConstraintsCanvasShape": function keepColumnWidth(constraintsCanvasShape, designCanvasShape) {
					ConstraintActions.defaultKeepConstraint(constraintsCanvasShape, designCanvasShape, "column_width");
				}, 
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					let cwValue = shape["column_width"];
					return ConstraintActions.defaultFeedbackMessage("column_width", cwValue) + "px.";
				}
			}, 
			"undo": {
				"key": "column_width",
				"updateConstraintsCanvasShape": function undoKeepColumnWidth(constraintsCanvasShape, designCanvasShape) {
					ConstraintActions.defaultUndoKeepConstraint(constraintsCanvasShape, designCanvasShape, "column_width");
				},
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					let cwValue = shape["column_width"]; 
					return ConstraintActions.defaultUndoFeedbackMessage("column_width", cwValue) + "px.";
				}
			}
		},	
	"columns": 
		{
			"do": {
				"key": "columns",
				"updateConstraintsCanvasShape": function keepColumns(constraintsCanvasShape, designCanvasShape) {
					ConstraintActions.defaultKeepConstraint(constraintsCanvasShape, designCanvasShape, "columns");
				}, 
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					let columnsValue = shape["columns"];
					return ConstraintActions.defaultFeedbackMessage("columns", columnsValue) + ".";
				}
			}, 
			"undo": {
				"key": "columns",
				"updateConstraintsCanvasShape": function undoKeepColumns(constraintsCanvasShape, designCanvasShape) {
					ConstraintActions.defaultUndoKeepConstraint(constraintsCanvasShape, designCanvasShape, "column");
				},
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					let columnsValue = shape["columns"]; 
					return ConstraintActions.defaultUndoFeedbackMessage("column", columnsValue) + "px.";
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
