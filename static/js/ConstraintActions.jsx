
// Feedback items
// Groups - Order, Size
// Global - Whitespace, Density 
class ConstraintActions {}


// Keep these here for now. Update when we have any more possible arrangement patterns
ConstraintActions.horizontalArrangements = ["horizontal", "rows"];
ConstraintActions.verticalArrangements = ["vertical", "columns"];
ConstraintActions.arrangments = ["horizontal", "vertical", "rows", "columns"]; 
ConstraintActions.verticalAlignments = ["left", "center", "right"];
ConstraintActions.horizontalAlignments = ["top", "center", "bottom"];

ConstraintActions.arrangements = ["horizontal", "vertical", "rows", "columns"];
ConstraintActions.justifications = ["top", "center", "bottom"];
ConstraintActions.locksKey = 'locks'; 

ConstraintActions.getAction = function getAction(lock, shape) {
	if(shape.type == "canvas") {
		let action = ConstraintActions.canvasConstraints[lock]; 
		if(action) {
			return action;
		}
	} else if(shape.type == "group") {
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

ConstraintActions.undoSizeKeepConstraint = function undoKeepConstraint(constraintsCanvasShape, designCanvasShape, constraintKey) {
	var index = constraintsCanvasShape[ConstraintActions.locksKey].indexOf(constraintKey); 
	constraintsCanvasShape[ConstraintActions.locksKey].splice(index,1); 
	if(!constraintsCanvasShape[ConstraintActions.locksKey].length) {
		delete constraintsCanvasShape[ConstraintActions.locksKey]; 
	}

	// Don't delete the value of size as the initial size is how we adjust up or down to grow or shrink the shape 
}


ConstraintActions.undoPositionKeepConstraint = function undoKeepConstraint(constraintsCanvasShape, designCanvasShape, constraintKey) {
	var index = constraintsCanvasShape[ConstraintActions.locksKey].indexOf(constraintKey); 
	constraintsCanvasShape[ConstraintActions.locksKey].splice(index,1); 
	if(!constraintsCanvasShape[ConstraintActions.locksKey].length) {
		delete constraintsCanvasShape[ConstraintActions.locksKey]; 
	}

	// Don't delete the value of size as the initial size is how we adjust up or down to grow or shrink the shape 
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
			"updateConstraintsCanvasShape": function keepX(constraintsCanvasShape, designCanvasShape) {
				ConstraintActions.defaultKeepConstraint(constraintsCanvasShape, designCanvasShape, "x");
			}, 
			"getFeedbackMessage": function generateFeedbackMessage(shape) {
				return "Keep x location at " + shape["x"] + "px.";
			}
		}, 
		"undo": {
			"key": "x",
			"updateConstraintsCanvasShape": function undoKeepX(constraintsCanvasShape, designCanvasShape) {
				ConstraintActions.undoPositionKeepConstraint(constraintsCanvasShape, designCanvasShape, "x");
			}, 
			"getFeedbackMessage": function generateFeedbackMessage(shape) {
				return "Don't keep x location at " + shape["x"] + "px.";
			}
		}
	}, 
	"y" : {
		"do": {
			"key": "y",
			"updateConstraintsCanvasShape": function keepY(constraintsCanvasShape, designCanvasShape) {
				ConstraintActions.defaultKeepConstraint(constraintsCanvasShape, designCanvasShape, "y");
			}, 
			"getFeedbackMessage": function generateFeedbackMessage(shape) {
				return "Keep y location at " + shape["y"] + "px.";
			}
		}, 
		"undo": {
			"key": "y",
			"updateConstraintsCanvasShape": function undoKeepY(constraintsCanvasShape, designCanvasShape) {
				ConstraintActions.undoPositionKeepConstraint(constraintsCanvasShape, designCanvasShape, "y");
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
				ConstraintActions.defaultKeepConstraint(constraintsCanvasShape, designCanvasShape, "width");
			}, 
			"getFeedbackMessage": function generateFeedbackMessage(shape) {
				return "Keep width at " + shape["width"] + "px.";
			}
		}, 
		"undo": {
			"key": "width",
			"updateConstraintsCanvasShape": function undoKeepWidth(constraintsCanvasShape, designCanvasShape) {
				ConstraintActions.undoSizeKeepConstraint(constraintsCanvasShape, designCanvasShape, "width");
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
				ConstraintActions.defaultKeepConstraint(constraintsCanvasShape, designCanvasShape, "height");
			}, 
			"getFeedbackMessage": function generateFeedbackMessage(shape) {
				return "Keep height at " + shape["height"] + "px.";
			}
		}, 
		"undo": {
			"key": "height",
			"updateConstraintsCanvasShape": function undoKeepHeight(constraintsCanvasShape, designCanvasShape) {
				ConstraintActions.undoSizeKeepConstraint(constraintsCanvasShape, designCanvasShape, "height");
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
			    ConstraintActions.defaultKeepConstraint(constraintsCanvasShape, designCanvasShape, "column");
			}, 
			"getFeedbackMessage": function generateFeedbackMessage(shape) {
				return "Keep column at " + shape["column"] + ".";
			}
		}, 
		"undo": {
			"key": "column",
			"updateConstraintsCanvasShape": function undoKeepColumn(constraintsCanvasShape, designCanvasShape) {
				ConstraintActions.defaultUndoKeepConstraint(constraintsCanvasShape, designCanvasShape, "column");
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
				"key": "arrangement",
				"updateConstraintsCanvasShape": function keepArrangment(constraintsCanvasShape, designCanvasShape) {
					ConstraintActions.defaultKeepConstraint(constraintsCanvasShape, designCanvasShape, "arrangement");
				}, 
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					let arrangementValue = ConstraintActions.arrangements[shape["arrangement"]];
					return ConstraintActions.defaultFeedbackMessage("arrangement", arrangementValue) + ".";
				}
			}, 
			"undo": {
				"key": "arrangement",
				"updateConstraintsCanvasShape": function undoKeepArrangement(constraintsCanvasShape, designCanvasShape) {
					ConstraintActions.defaultUndoKeepConstraint(constraintsCanvasShape, designCanvasShape, "arrangement");
				},
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					let arrangementValue = ConstraintActions.arrangements[shape["arrangement"]]; 
					return ConstraintActions.defaultUndoFeedbackMessage("arrangement", arrangementValue) + ".";
				}
			}
		}, 
	"alignment": 
		{
			"do": {
				"key": "alignment",
				"updateConstraintsCanvasShape": function keepAlignment(constraintsCanvasShape, designCanvasShape) {
					ConstraintActions.defaultKeepConstraint(constraintsCanvasShape, designCanvasShape, "alignment");
				}, 
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					// Generate the message based on the axis of alignment
					let alignmentValue = ConstraintActions.verticalAlignments[shape["alignment"]];
					let arrangementValue = ConstraintActions.arrangments[shape["arrangement"]]; 
					if(ConstraintActions.horizontalArrangements.indexOf(arrangementValue) > -1) {
						alignmentValue = ConstraintActions.horizontalAlignments[shape["alignment"]]; 
					}

					return ConstraintActions.defaultFeedbackMessage("alignment", alignmentValue) + ".";
				}
			}, 
			"undo": {
				"key": "alignment",
				"updateConstraintsCanvasShape": function undoKeepAlignment(constraintsCanvasShape, designCanvasShape) {
					ConstraintActions.defaultUndoKeepConstraint(constraintsCanvasShape, designCanvasShape, "alignment");
				},
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					let alignmentValue = ConstraintActions.verticalAlignments[shape["alignment"]];
					let arrangementValue = ConstraintActions.arrangments[shape["arrangement"]]; 
					if(ConstraintActions.horizontalArrangements.indexOf(arrangementValue) > -1) {
						alignmentValue = ConstraintActions.horizontalAlignments[shape["alignment"]]; 
					}

					return ConstraintActions.defaultUndoFeedbackMessage("alignment", alignmentValue) + ".";
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
				"key": "margin", 
				"updateConstraintsCanvasShape": function keepMargin(constraintsCanvasShape, designCanvasShape) {
					ConstraintActions.defaultKeepConstraint(constraintsCanvasShape, designCanvasShape, "margin");
				}, 
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					return "Keep the " + "margin" + " at " + shape["margin"] + "px.";
				}
			}, 
			"undo": {
				"key": "margin",
				"updateConstraintsCanvasShape": function undoKeepProximity(constraintsCanvasShape, designCanvasShape) {
					ConstraintActions.defaultUndoKeepConstraint(constraintsCanvasShape, designCanvasShape, "margin");
				}, 
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					return "Don't keep " + "margin" + " at " + shape["margin"] + "px.";
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
