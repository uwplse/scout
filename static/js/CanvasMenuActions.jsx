import Constants from "./Constants"; 

class CanvasMenuActions {}
CanvasMenuActions.locked_position_key = 'position'; 
CanvasMenuActions.locked_arrangement_key = 'arrangement'; 
CanvasMenuActions.locksKey = 'locks'; 

CanvasMenuActions.elementConstraints = {
	"position" : {
		"do": {
			"label": "Keep position.",
			"updateConstraintsCanvasShape": function lockPosition(constraintsCanvasShape, designCanvasShape) {
			    // Update the property on shape according to the selected option
			    // Use the server key for locking a shape into a specific location
			    if(constraintsCanvasShape[CanvasMenuActions.locksKey] == undefined) {
			    	constraintsCanvasShape[CanvasMenuActions.locksKey] = []; 
			    } 

			    constraintsCanvasShape[CanvasMenuActions.locksKey].push(CanvasMenuActions.locked_position_key); 
			    constraintsCanvasShape[CanvasMenuActions.locked_position_key] = "x: " + designCanvasShape["location"]["x"] + ", y: " + designCanvasShape["location"]["y"]; 

			    // Then update the location of the constraints canvas shape to that of the design canvas shape
			    // constraintsCanvasShape.shape.set({
			    // 	left: designCanvasShape.shape.left * Constants.designCanvasScalingFactor(), 
			    // 	top: designCanvasShape.shape.top * Constants.designCanvasScalingFactor() 
			    // }); 
			}
		}, 
		"undo": {
			"label": "Unlock position.", 
			"updateConstraintsCanvasShape": function undoLockPosition(constraintsCanvasShape, designCanvasShape) {
				var index = constraintsCanvasShape[CanvasMenuActions.locksKey].indexOf(CanvasMenuActions.locked_position_key); 
				constraintsCanvasShape[CanvasMenuActions.locksKey].splice(index,1); 
				if(!constraintsCanvasShape[CanvasMenuActions.locksKey].length) {
					delete constraintsCanvasShape[CanvasMenuActions.locksKey]; 
				}
			}
		} 
	}
}

CanvasMenuActions.groupConstraints = {
	"arrangement": 
		{
			"do": {
				"label": "Keep arrangement. ", 
				"updateConstraintsCanvasShape": function keepArrangment(constraintsCanvasShape, designCanvasShape) {
				  	if(constraintsCanvasShape[CanvasMenuActions.locksKey] == undefined) {
						constraintsCanvasShape[CanvasMenuActions.locksKey] = []; 
					} 

			    	constraintsCanvasShape[CanvasMenuActions.locksKey].push(CanvasMenuActions.locked_arrangement_key); 

					// Also should the constraints canvas arrange itself in the way of the designs canvas?
					// Update the constraint property on the object
					constraintsCanvasShape[CanvasMenuActions.locked_arrangement_key] = designCanvasShape[CanvasMenuActions.locked_arrangement_key]; 
				}
			}, 
			"undo": {
				"label": "Unlock arrangement. ",
				"updateConstraintsCanvasShape": function undoLockArrangment(constraintsCanvasShape, designCanvasShape) {
					var index = constraintsCanvasShape[CanvasMenuActions.locksKey].indexOf(CanvasMenuActions.locked_arrangement_key); 
					constraintsCanvasShape[CanvasMenuActions.locksKey].splice(index,1); 
					if(!constraintsCanvasShape[CanvasMenuActions.locksKey].length) {
						delete constraintsCanvasShape[CanvasMenuActions.locksKey]; 
					}
				}
			}
		}
}

export default CanvasMenuActions; 
