import Constants from "./Constants"; 

class ConstraintActions {}
ConstraintActions.locked_location_key = 'location'; 
ConstraintActions.locked_arrangement_key = 'arrangement'; 

// Keep these here for now. Update when we have any more possible arrangement patterns
ConstraintActions.arrangements = ["horizontal", "vertical"];

ConstraintActions.locked_proximity_key = 'proximity'; 
ConstraintActions.locked_margin_key = 'margin';
ConstraintActions.locked_text_key = 'text';
ConstraintActions.locksKey = 'locks'; 

ConstraintActions.elementConstraints = {
	"location" : {
		"do": {
			"key": ConstraintActions.locked_location_key,
			"updateConstraintsCanvasShape": function keepPosition(constraintsCanvasShape, designCanvasShape) {
			    // Update the property on shape according to the selected option
			    // Use the server key for locking a shape into a specific location
			    if(constraintsCanvasShape[ConstraintActions.locksKey] == undefined) {
			    	constraintsCanvasShape[ConstraintActions.locksKey] = []; 
			    } 

			    constraintsCanvasShape[ConstraintActions.locksKey].push(ConstraintActions.locked_location_key); 
			    constraintsCanvasShape[ConstraintActions.locked_location_key] = {
			    	x: designCanvasShape["location"]["x"], 
			    	y: designCanvasShape["location"]["y"]
			    }
			}, 
			"getFeedbackMessage": function generateFeedbackMessage(shape) {
				return "Keep position at X: " + shape[ConstraintActions.locked_location_key]["x"] + ", Y: " + shape[ConstraintActions.locked_location_key]["y"] + ".";
			}
		}, 
		"undo": {
			"key": ConstraintActions.locked_location_key,
			"updateConstraintsCanvasShape": function undoKeepPosition(constraintsCanvasShape, designCanvasShape) {
				var index = constraintsCanvasShape[ConstraintActions.locksKey].indexOf(ConstraintActions.locked_location_key); 
				constraintsCanvasShape[ConstraintActions.locksKey].splice(index,1); 
				if(!constraintsCanvasShape[ConstraintActions.locksKey].length) {
					delete constraintsCanvasShape[ConstraintActions.locksKey]; 
				}

				delete constraintsCanvasShape[ConstraintActions.locked_location_key]; 
			}, 
			"getFeedbackMessage": function generateFeedbackMessage(shape) {
				return "Unlock position from X: " + shape[ConstraintActions.locked_location_key]["x"] + ", Y: " + shape[ConstraintActions.locked_location_key]["y"] + ".";
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
				  	if(constraintsCanvasShape[ConstraintActions.locksKey] == undefined) {
						constraintsCanvasShape[ConstraintActions.locksKey] = []; 
					} 

			    	constraintsCanvasShape[ConstraintActions.locksKey].push(ConstraintActions.locked_arrangement_key); 

					// Also should the constraints canvas arrange itself in the way of the designs canvas?
					// Update the constraint property on the object
					constraintsCanvasShape[ConstraintActions.locked_arrangement_key] = designCanvasShape[ConstraintActions.locked_arrangement_key]; 
				}, 
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					let arrangmentValue = ConstraintActions.arrangements[shape[ConstraintActions.locked_arrangement_key]];
					return "Keep the " + ConstraintActions.locked_arrangement_key + " " + arrangmentValue + ".";
				}
			}, 
			"undo": {
				"key": ConstraintActions.locked_arrangement_key,
				"updateConstraintsCanvasShape": function undoKeepArrangement(constraintsCanvasShape, designCanvasShape) {
					var index = constraintsCanvasShape[ConstraintActions.locksKey].indexOf(ConstraintActions.locked_arrangement_key); 
					constraintsCanvasShape[ConstraintActions.locksKey].splice(index,1); 
					if(!constraintsCanvasShape[ConstraintActions.locksKey].length) {
						delete constraintsCanvasShape[ConstraintActions.locksKey]; 
					}

					delete constraintsCanvasShape[ConstraintActions.locked_arrangement_key]; 
				},
				"getFeedbackMessage": function generateFeedbackMessage(shape) {
					return "Unlock " + ConstraintActions.locked_arrangement_key + " from " + ConstraintActions.arrangements[shape[ConstraintActions.locked_arrangement_key]] + ".";
				}
			}
		}
}

ConstraintActions.pageConstraints = {
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
