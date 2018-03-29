import Constants from "./Constants"; 

class ConstraintActions {}
ConstraintActions.locked_position_key = 'position'; 
ConstraintActions.locked_arrangement_key = 'arrangement'; 
ConstraintActions.locked_proximity_key = 'proximity'; 
ConstraintActions.locksKey = 'locks'; 

ConstraintActions.elementConstraints = {
	"position" : {
		"do": {
			"label": "Keep position.",
			"updateConstraintsCanvasShape": function keepPosition(constraintsCanvasShape, designCanvasShape) {
			    // Update the property on shape according to the selected option
			    // Use the server key for locking a shape into a specific location
			    if(constraintsCanvasShape[ConstraintActions.locksKey] == undefined) {
			    	constraintsCanvasShape[ConstraintActions.locksKey] = []; 
			    } 

			    constraintsCanvasShape[ConstraintActions.locksKey].push(ConstraintActions.locked_position_key); 
			    constraintsCanvasShape[ConstraintActions.locked_position_key] = "x: " + designCanvasShape["location"]["x"] + ", y: " + designCanvasShape["location"]["y"]; 

			    // Then update the location of the constraints canvas shape to that of the design canvas shape
			    // constraintsCanvasShape.shape.set({
			    // 	left: designCanvasShape.shape.left * Constants.designCanvasScalingFactor(), 
			    // 	top: designCanvasShape.shape.top * Constants.designCanvasScalingFactor() 
			    // }); 
			}
		}, 
		"undo": {
			"label": "Unlock position.", 
			"updateConstraintsCanvasShape": function undoKeepPosition(constraintsCanvasShape, designCanvasShape) {
				var index = constraintsCanvasShape[ConstraintActions.locksKey].indexOf(ConstraintActions.locked_position_key); 
				constraintsCanvasShape[ConstraintActions.locksKey].splice(index,1); 
				if(!constraintsCanvasShape[ConstraintActions.locksKey].length) {
					delete constraintsCanvasShape[ConstraintActions.locksKey]; 
				}
			}
		} 
	}
}

ConstraintActions.groupConstraints = {
	"arrangement": 
		{
			"do": {
				"label": "Keep arrangement. ", 
				"updateConstraintsCanvasShape": function keepArrangment(constraintsCanvasShape, designCanvasShape) {
				  	if(constraintsCanvasShape[ConstraintActions.locksKey] == undefined) {
						constraintsCanvasShape[ConstraintActions.locksKey] = []; 
					} 

			    	constraintsCanvasShape[ConstraintActions.locksKey].push(ConstraintActions.locked_arrangement_key); 

					// Also should the constraints canvas arrange itself in the way of the designs canvas?
					// Update the constraint property on the object
					constraintsCanvasShape[ConstraintActions.locked_arrangement_key] = designCanvasShape[ConstraintActions.locked_arrangement_key]; 
				}
			}, 
			"undo": {
				"label": "Unlock arrangement. ",
				"updateConstraintsCanvasShape": function undoKeepArrangement(constraintsCanvasShape, designCanvasShape) {
					var index = constraintsCanvasShape[ConstraintActions.locksKey].indexOf(ConstraintActions.locked_arrangement_key); 
					constraintsCanvasShape[ConstraintActions.locksKey].splice(index,1); 
					if(!constraintsCanvasShape[ConstraintActions.locksKey].length) {
						delete constraintsCanvasShape[ConstraintActions.locksKey]; 
					}
				}
			}
		}
}

ConstraintActions.pageConstraints = {
	"proximity": 
		{
			"do": {
				"label": "Keep proximity. ", 
				"updateConstraintsCanvasShape": function keepProximity(constraintsCanvasShape, designCanvasShape) {
				  	if(constraintsCanvasShape[ConstraintActions.locksKey] == undefined) {
						constraintsCanvasShape[ConstraintActions.locksKey] = []; 
					} 

			    	constraintsCanvasShape[ConstraintActions.locksKey].push(ConstraintActions.locked_proximity_key); 

					// Also should the constraints canvas arrange itself in the way of the designs canvas?
					// Update the constraint property on the object
					constraintsCanvasShape[ConstraintActions.locked_proximity_key] = designCanvasShape[ConstraintActions.locked_proximity_key]; 
				}
			}, 
			"undo": {
				"label": "Unlock proximity. ",
				"updateConstraintsCanvasShape": function undoKeepProximity(constraintsCanvasShape, designCanvasShape) {
					var index = constraintsCanvasShape[ConstraintActions.locksKey].indexOf(ConstraintActions.locked_proximity_key); 
					constraintsCanvasShape[ConstraintActions.locksKey].splice(index,1); 
					if(!constraintsCanvasShape[ConstraintActions.locksKey].length) {
						delete constraintsCanvasShape[ConstraintActions.locksKey]; 
					}
				}
			}
		}
}

export default ConstraintActions; 
