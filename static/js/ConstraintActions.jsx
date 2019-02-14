
// Feedback items
// Groups - Order, Size
// Global - Whitespace, Density 
class ConstraintActions {}

ConstraintActions.computeColumnWidths = function computeColumnWidths() {
	let widths = [];
	for(let i=0; i<ConstraintActions.margins.length; i++) {
		for(let j=0; j<ConstraintActions.num_columns.length; j++) {
			for(let k=0; k<ConstraintActions.gutter_widths.length; k++) {
				let margin_value = ConstraintActions.margins[i]; 
				let column_value = ConstraintActions.num_columns[j]; 
				let gutter_width_value = ConstraintActions.gutter_widths[k]; 
				let column_width = (ConstraintActions.canvas_width - (2*margin_value) - ((column_value-1)*gutter_width_value))/column_value; 
				if(column_width - Math.round(column_width) == 0) {
					widths.push(column_width); 
				}
			}
		}
	}

	return _.uniq(widths).sort((a, b) => a - b); 
}

// Variables where the domains are encoded as integer values into the domain list
// rather than string values, or real values (e.g., margins)
ConstraintActions.index_domains = ["arrangement", "alignment"]

ConstraintActions.canvas_width = 360; 
ConstraintActions.canvas_height = 640; 

ConstraintActions.grid_constant = 4; 
ConstraintActions.min_height = 48; 
ConstraintActions.min_width = 48; 
ConstraintActions.max_height = 636; 
ConstraintActions.max_width = 356;

// Keep these here for now. Update when we have any more possible arrangement patterns
ConstraintActions.horizontalArrangements = ["horizontal", "rows"];
ConstraintActions.verticalArrangements = ["vertical", "columns"];
ConstraintActions.arrangments = ["horizontal", "vertical", "rows", "columns"]; 
ConstraintActions.verticalAlignments = ["left", "center", "right"];
ConstraintActions.horizontalAlignments = ["top", "center", "bottom"];
ConstraintActions.paddings = [4,8,12,16,20,24,28,32,36,40]; 
ConstraintActions.arrangements = ["horizontal", "vertical", "rows", "columns"];

// Canvas variable domains 
ConstraintActions.margins = [4,8,12,16,20,24,28,32,36,40,44,48,52,56,60]; 
ConstraintActions.num_columns = [2,3,4,6,12]; 
ConstraintActions.gutter_widths = [4,8,16]
ConstraintActions.baseline_grids = [4,8,16]
ConstraintActions.column_widths = ConstraintActions.computeColumnWidths(); 

// Element specific domains
ConstraintActions.left_columns = [1,2,3,4,5,6,7,8,9,10,11,12]; 
ConstraintActions.right_columns = [1,2,3,4,5,6,7,8,9,10,11,12]; 

ConstraintActions.y_positions = [...Array(ConstraintActions.canvas_height).keys()].filter((value) => {
	return ((value % 4) == 0); 
})

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

	if(shape["locked_values"] == undefined) {
		shape["locked_values"] = {}; 
	}

	if(shape["locks"].indexOf(property) == -1) {
		shape["locks"].push(property); 
	}

	if(!shape["locked_values"][property]) {
		shape["locked_values"][property] = []; 
	}

	shape["locked_values"][property].push(value); 	
}

ConstraintActions.defaultUndoKeepConstraint = function undoKeepConstraint(property, shape, value) {
	var index = shape["locks"].indexOf(property); 
	if(index > -1) {
		if(shape["locked_values"][property]) {
			let valueIndex = shape["locked_values"][property].indexOf(value); 
			if(valueIndex > -1) {
				shape["locked_values"][property].splice(valueIndex,1);
			}

			if(!shape["locked_values"][property].length) {
				delete shape["locked_values"][property]; 

				// Also remove the lock for that property 
				shape["locks"].splice(index, 1); 

				if(!shape["locks"].length) {
					delete shape["locks"]; 
				}
			}

			if(_.isEmpty(shape["locked_values"])) {
				delete shape["locked_values"]; 
			}
		}
	}
}

ConstraintActions.defaultPreventConstraint = function preventConstraint(property, shape, value) {
  	if(shape["prevents"] == undefined) {
		shape["prevents"] = []; 
	} 

	if(shape["prevented_values"] == undefined) {
		shape["prevented_values"] = {}; 
	}

	if(shape["prevents"].indexOf(property) == -1) {
		shape["prevents"].push(property); 
	}

	if(!shape["prevented_values"][property]) {
		shape["prevented_values"][property] = []; 
	}

	shape["prevented_values"][property].push(value); 	
}	

ConstraintActions.defaultUndoPreventConstraint = function undoPreventConstraint(property, shape, value) {
	var index = shape["prevents"].indexOf(property); 
	if(index > -1) {
		if(shape["prevented_values"][property]) {
			let valueIndex = shape["prevented_values"][property].indexOf(value); 
			if(valueIndex > -1) {
				shape["prevented_values"][property].splice(valueIndex,1);
			}

			if(!shape["prevented_values"][property].length) {
				delete shape["prevented_values"][property]; 

				// Also remove the lock for that property 
				shape["prevents"].splice(index, 1); 

				if(!shape["prevents"].length) {
					delete shape["prevents"]; 
				}
			}

			if(_.isEmpty(shape["prevented_values"])) {
				delete shape["prevented_values"]; 
			}
		}
	}
}

ConstraintActions.messages = {
	"width": function getMessage(shape, value) {
		return "width of " + value + "px."
	}, 
	"height": function getMessage(shape, value) {
		return "height of " + value + "px."
	}, 
	"x": function getMessage(shape, value) {
		return "x at location " + value + "px."
	}, 
	"y": function getMessage(shape, value) {
		return "y at location " + value + "px."
	},
	"left_column": function getMessage(shape, value) {
		return " left aligned to column " + value + ".";
	}, 
	"right_column": function getMessage(shape, value) {
		return " right aligned to column " + value + ".";
	}, 
	"arrangement": function getMessage(shape, value) {
		let labelValue = ConstraintActions.arrangements[value]; 
		return " arrangement " + labelValue + "."; 
	}, 
	"padding": function getMessage(shape, value) {
		return " padding of " + value + "px."; 
	},
	"margin": function getMessage(shape, value) {
		return " margin of " + value + "px."; 
	}, 
	"baseline_grid": function getMessage(shape, value) {
		return " baseline grid of " + value + "px."; 
	}, 
	"columns": function getMessage(shape, value) {
		return " columns of " + value + ".";
	}, 

	"gutter_width": function getMessage(shape, value) {
		return " gutter width of " + value + "px."; 
	}, 
	"column_width": function getMessage(shape, value) {
		return " column width of " + value + "px."; 
	}, 
	"alignment": function getMessage(shape, value) {
		// Generate the message based on the axis of alignment
		let alignmentValue = ConstraintActions.verticalAlignments[value];

		// TODO -- Address 
		// let arrangementValue = ConstraintActions.arrangements[shape["arrangement"]]; 
		// if(ConstraintActions.horizontalArrangements.indexOf(arrangementValue) > -1) {
		// 	alignmentValue = ConstraintActions.horizontalAlignments[shape["alignment"]]; 
		// }
		return " alignment " + alignmentValue + "."; 
	}
}

ConstraintActions.defaultDoKeep = {
	"updateConstraintsCanvasShape": function keepConstraint(property, shape, value) {
		ConstraintActions.defaultKeepConstraint(property, shape, value);
	}, 
	"getFeedbackMessage": function generateFeedbackMessage(property, shape, value) {
		let message = ConstraintActions.messages[property](shape, value); 
		return "Keep " + message; 
	}
}

ConstraintActions.defaultUndoKeep =  {
	"updateConstraintsCanvasShape": function undoKeepConstraint(property, shape, value) {
		ConstraintActions.defaultUndoKeepConstraint(property, shape, value);
	}, 
	"getFeedbackMessage": function generateFeedbackMessage(property, shape, value) {
		let message = ConstraintActions.messages[property](shape); 
		return "Don't keep " + message; 
	}
} 

ConstraintActions.defaultDoPrevent = {
	"updateConstraintsCanvasShape": function preventConstraint(property, shape, value) {
		ConstraintActions.defaultPreventConstraint(property, shape, value);
	}, 
	"getFeedbackMessage": function generateFeedbackMessage(property, shape, value) {
		let message = ConstraintActions.messages[property](shape, value); 
		return "Prevent " + message; 
	}
} 

ConstraintActions.defaultUndoPrevent = {
	"updateConstraintsCanvasShape": function undoPreventConstraint(property, shape, value) {
		ConstraintActions.defaultUndoPreventConstraint(property, shape, value);
	}, 
	"getFeedbackMessage": function generateFeedbackMessage(property, shape, value) {
		let message = ConstraintActions.messages[property](shape, value); 
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
		"undo": ConstraintActions.defaultUndoKeep
	},
	"prevent": {
		"do": ConstraintActions.defaultDoPrevent, 
		"undo": ConstraintActions.defaultUndoPrevent
	}, 
	"domains": {
		"size": function(shape) {
			let heights = [];
			let widths = []; 

			let orig_height = shape.orig_height; 
			let orig_width = shape.orig_width; 
			let aspect_ratio = orig_width/orig_height; 

			let height_diff = orig_height % ConstraintActions.grid_constant; 
			let height = orig_height - height_diff; 
			let width = Math.round(height * aspect_ratio); 

			heights.push(height);
			widths.push(width); 

			let minimum_element_height = ConstraintActions.min_height > (orig_height / 2) ? ConstraintActions.min_height : (orig_height / 2); 
			let minimum_element_width = ConstraintActions.min_width > (orig_width / 2) ? ConstraintActions.min_width : (orig_width / 2); 
			let computed_height = height;
			let computed_width = width; 

			if(shape.importance != "high") {
				while (computed_height > minimum_element_height && computed_width > minimum_element_width) {
					computed_height -= ConstraintActions.grid_constant; 
					computed_width = Math.round(computed_height * aspect_ratio); 

					if(computed_height > minimum_element_height && computed_width > minimum_element_width) {
						heights.push(computed_height);
						widths.push(computed_width); 
					}
				}
			}

			let maximum_element_height = ConstraintActions.max_height < (orig_height * 2) ? ConstraintActions.max_height : (orig_height * 2); 
			let maximum_element_width = ConstraintActions.max_height < (orig_width * 2) ? ConstraintActions.max_height : (orig_width * 2); 
			computed_height = height;
			computed_width = width; 
			if(shape.importance != "low") {
				while (computed_height < maximum_element_height && computed_width < maximum_element_width) {
					computed_height += ConstraintActions.grid_constant; 
					computed_width = Math.round(computed_height * aspect_ratio); 

					if(computed_height < maximum_element_height && computed_width < maximum_element_width) {
						heights.push(computed_height);
						widths.push(computed_width); 
					}
				}
			}

			return { "height" : heights, "width" : widths }
		}, 
		"x": [], 
		"y": []
	}
}

// These actions will only appear for direct children of the canvas container
ConstraintActions.canvasChildConstraints = {
	"values": ["left_column", "right_column", "y"],
	"keep": ConstraintActions.defaultKeep, 
	"prevent": ConstraintActions.defaultPrevent, 
	"domains": {
		"left_column": ConstraintActions.left_columns, 
		"right_column": ConstraintActions.right_columns, 
		"y": ConstraintActions.y_positions
	}
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
		"columns": ConstraintActions.num_columns, 
		"gutter_width": ConstraintActions.gutter_widths, 
		"column_width": ConstraintActions.column_widths
	}
}

export default ConstraintActions; 
