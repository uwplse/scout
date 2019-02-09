
// Feedback items
// Groups - Order, Size
// Global - Whitespace, Density 
class ConstraintActions {}

// Variables where the domains are encoded as integer values into the domain list
// rather than string values, or real values (e.g., margins)
ConstraintActions.index_domains = ["arrangement", "alignment"]


// Keep these here for now. Update when we have any more possible arrangement patterns
ConstraintActions.horizontalArrangements = ["horizontal", "rows"];
ConstraintActions.verticalArrangements = ["vertical", "columns"];
ConstraintActions.arrangments = ["horizontal", "vertical", "rows", "columns"]; 
ConstraintActions.verticalAlignments = ["left", "center", "right"];
ConstraintActions.horizontalAlignments = ["top", "center", "bottom"];
ConstraintActions.paddings = [4,8,12,16,20,24,28,32,36,40]; 
ConstraintActions.arrangements = ["horizontal", "vertical", "rows", "columns"];

ConstraintActions.margins = [4,8,12,16,20,24,28,32,36,40,44,48,52,56,60]; 
ConstraintActions.columns = [2,3,4,6,12]; 
ConstraintActions.column_widths = [0]; // TODO
ConstraintActions.gutter_widths = [10]
ConstraintActions.baseline_grids = [4,8,16]

ConstraintActions.getAction = function getAction(actionType, shape) {
	if(shape.type == "canvas") {
		let action = ConstraintActions.canvasConstraints[actionType]; 
		if(action) {
			return action;
		}
	} else if(shape.type == "group") {
		let action = ConstraintActions.groupConstraints[actionType]; 
		if(action){
			return action;
		}
	}
	else {
		let action = ConstraintActions.elementConstraints[actionType]; 
		if(action){
			return action;
		}
	}
}

ConstraintActions.defaultKeepConstraint = function keepConstraint(property, shape, value) {
  	if(shape["locks"] == undefined) {
		shape["locks"] = []; 
	} 

	if(shape["locks"].indexOf(property) == -1) {
		shape["locks"].push(property); 
	}

	shape[property] = value; 	
}

ConstraintActions.defaultUndoKeepConstraint = function undoKeepConstraint(property, shape, value=undefined) {
	var index = shape["locks"].indexOf(property); 
	shape["locks"].splice(index,1); 
	if(!shape["locks"].length) {
		delete shape["locks"]; 
	}

	delete shape[property]; 
}

ConstraintActions.defaultPreventConstraint = function preventConstraint(property, shape, value) {
  	if(shape["prevents"] == undefined) {
		shape["prevents"] = []; 
	} 

	if(shape["prevents"].indexOf(property) == -1) {
		shape["prevents"].push(property); 
	}

	shape[property] = value; 	
}

ConstraintActions.defaultUndoPreventConstraint = function undoPreventConstraint(property, shape, value=undefined) {
	var index = shape["prevents"].indexOf(property); 
	shape["prevents"].splice(index,1); 
	if(!shape["prevents"].length) {
		delete shape["prevents"]; 
	}

	delete shape[property]; 
}


ConstraintActions.undoSpatialKeepConstraint = function undoKeepConstraint(constraintsCanvasShape, designCanvasShape, constraintKey) {
	var index = constraintsCanvasShape["locks"].indexOf(constraintKey); 
	constraintsCanvasShape["locks"].splice(index,1); 
	if(!constraintsCanvasShape["locks"].length) {
		delete constraintsCanvasShape["locks"]; 
	}
}

ConstraintActions.undoSpatialPreventConstraint = function undoKeepConstraint(constraintsCanvasShape, designCanvasShape, constraintKey) {
	var index = constraintsCanvasShape["prevents"].indexOf(constraintKey); 
	constraintsCanvasShape["prevents"].splice(index,1); 
	if(!constraintsCanvasShape["prevents"].length) {
		delete constraintsCanvasShape["prevents"]; 
	}
}

ConstraintActions.messages = {
	"width": function getMessage(shape) {
		let value = shape["width"];
		return "width of " + value + "px."
	}, 
	"height": function getMessage(shape) {
		let value = shape["height"];
		return "height of " + value + "px."
	}, 
	"x": function getMessage(shape) {
		let value = shape["x"];
		return "x at location " + value + "px."
	}, 
	"y": function getMessage(shape) {
		let value = shape["y"];
		return "y at location " + value + "px."
	},
	"column": function getMessage(shape) {
		let value = shape["column"];
		return " in column " + value + ".";
	}, 
	"arrangement": function getMessage(shape) {
		let value = shape["arrangement"];
		let labelValue = ConstraintActions.arrangements[value]; 
		return " arrangement " + labelValue + "."; 
	}, 
	"padding": function getMessage(shape) {
		let value = shape["padding"];
		return " padding of " + value + "px."; 
	},
	"margin": function getMessage(shape) {
		let value = shape["margin"];
		return " margin of " + value + "px."; 
	}, 
	"baseline_grid": function getMessage(shape) {
		let value = shape["baseline_grid"];
		return " baseline grid of " + value + "px."; 
	}, 
	"columns": function getMessage(shape) {
		let value = shape["columns"];
		return " columns of " + value + ".";
	}, 
	"gutter_width": function getMessage(shape) {
		let value = shape["gutter_width"];
		return " gutter width of " + value + "px."; 
	}, 
	"column_width": function getMessage(shape) {
		let value = shape["column_width"];
		return " column width of " + value + "px."; 
	}, 
	"alignment": function getMessage(shape) {
		// Generate the message based on the axis of alignment
		let alignmentValue = ConstraintActions.verticalAlignments[shape["alignment"]];
		let arrangementValue = ConstraintActions.arrangements[shape["arrangement"]]; 
		if(ConstraintActions.horizontalArrangements.indexOf(arrangementValue) > -1) {
			alignmentValue = ConstraintActions.horizontalAlignments[shape["alignment"]]; 
		}
		return " alignment " + alignmentValue + "."; 
	}
}

ConstraintActions.defaultDoKeep = {
	"updateConstraintsCanvasShape": function keepConstraint(property, shape, value) {
		ConstraintActions.defaultKeepConstraint(property, shape, value);
	}, 
	"getFeedbackMessage": function generateFeedbackMessage(property, shape) {
		let message = ConstraintActions.messages[property](shape); 
		return "Keep " + message; 
	}
}

ConstraintActions.defaultUndoKeep =  {
	"updateConstraintsCanvasShape": function undoKeepConstraint(property, shape) {
		ConstraintActions.defaultUndoKeepConstraint(property, shape);
	}, 
	"getFeedbackMessage": function generateFeedbackMessage(property, shape) {
		let message = ConstraintActions.messages[property](shape); 
		return "Don't keep " + message; 
	}
} 

ConstraintActions.defaultDoPrevent = {
	"updateConstraintsCanvasShape": function preventConstraint(property, shape, value) {
		ConstraintActions.defaultPreventConstraint(property, shape, value);
	}, 
	"getFeedbackMessage": function generateFeedbackMessage(property, shape) {
		let message = ConstraintActions.messages[property](shape); 
		return "Prevent " + message; 
	}
} 

ConstraintActions.defaultUndoPrevent = {
	"updateConstraintsCanvasShape": function undoPreventConstraint(property, shape, value) {
		ConstraintActions.defaultUndoPreventConstraint(property, shape, value);
	}, 
	"getFeedbackMessage": function generateFeedbackMessage(property, shape) {
		let message = ConstraintActions.messages[property](shape); 
		return "Don't prevent " + message; 
	}
}

ConstraintActions.defaultKeep = {
	"do": ConstraintActions.defaultDoKeep, 
	"undo": ConstraintActions.defaultUndoKeep
}

ConstraintActions.defaultPrevent = {
	"do": ConstraintActions.defaultDoPrevent, 
	"undo": ConstraintActions.defaultUndoPrevent
}

ConstraintActions.elementConstraints = {
	"values": ["x", "y", "width", "height"], 
	"keep":  
	{
		"do": ConstraintActions.defaultDoKeep, 
		"undo": {
			"updateConstraintsCanvasShape": function undoKeepConstraint(property, constraintsCanvasShape, designCanvasShape) {
				ConstraintActions.undoSpatialKeepConstraint(constraintsCanvasShape, designCanvasShape, property);
			}, 
			"getFeedbackMessage": function generateFeedbackMessage(property, shape) {
				let message = ConstraintActions.messages[property](shape); 
				return "Don't keep " + message; 
			}
		}, 
	},
	"prevent": {
		"do": ConstraintActions.defaultDoPrevent, 
		"undo": {
			"updateConstraintsCanvasShape": function undoPreventConstraint(property, constraintsCanvasShape, designCanvasShape) {
				ConstraintActions.undoSpatialPreventConstraint(constraintsCanvasShape, designCanvasShape, property);
			}, 
			"getFeedbackMessage": function generateFeedbackMessage(property, shape) {
				let message = ConstraintActions.messages[property](shape); 
				return "Don't prevent " + message; 
			}
		}
	}	
}

// These actions will only appear for direct children of the canvas container
ConstraintActions.canvasChildConstraints = {
	"values": ["column"],
	"keep": ConstraintActions.defaultKeep, 
	"prevent": ConstraintActions.defaultPrevent
}

ConstraintActions.groupConstraints = {
	"values": ["arrangement", "alignment", "padding"], 
	"keep": ConstraintActions.defaultKeep, 
	"prevent": ConstraintActions.defaultPrevent, 
	"domains": {
		"arrangement": ConstraintActions.arrangments, 
		"alignment": ConstraintActions.verticalAlignments, 
		"padding": ConstraintActions.paddings
	}
}

ConstraintActions.canvasConstraints = {
	"values": ["margin", "baseline_grid", "columns", "gutter_width", "column_width"], 
	"keep": ConstraintActions.defaultKeep, 
	"prevent": ConstraintActions.defaultPrevent, 
	"domains": {
		"margin": ConstraintActions.margins, 
		"baseline_grid": ConstraintActions.baseline_grids, 
		"columns": ConstraintActions.columns, 
		"gutter_width": ConstraintActions.gutter_widths, 
		"column_width": ConstraintActions.column_widths
	}
}

export default ConstraintActions; 
