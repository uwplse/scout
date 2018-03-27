// import Constants from "./Constants"; 
class Constants {}
Constants.designCanvasScalingFactor = 2; 


class CanvasMenuActions {}
CanvasMenuActions.locked_position_key = 'locked_position'; 
CanvasMenuActions.locked_arrangement_key = 'locked_arrangement'; 
CanvasMenuActions.elementConstraints = {
	"locked_position" : {
		"do": {
			"label": "Lock position.",
			"updateConstraintsCanvasShape": function lockPosition(constraintsCanvasShape, designCanvasShape) {
			    // Update the property on shape according to the selected option
			    // Use the server key for locking a shape into a specific location
			    constraintsCanvasShape[CanvasMenuActions.locked_position_key] = true; 

			    // Then update the location of the constraints canvas shape to that of the design canvas shape
			    constraintsCanvasShape.shape.set({
			    	left: designCanvasShape.shape.left * Constants.designCanvasScalingFactor, 
			    	top: designCanvasShape.shape.top * Constants.designCanvasScalingFactor 
			    }); 
			}
		}, 
		"undo": {
			"label": "Unlock position.", 
			"updateConstraintsCanvasShape": function undoLockPosition(constraintsCanvasShape, designCanvasShape) {
				constraintsCanvasShape[CanvasMenuActions.locked_position_key] = false; 
				// What does it mean to undo this action?
			}
		} 
	}
}

CanvasMenuActions.groupConstraints = {
	"locked_arrangement": // Should this be contextual? (Say Horizontal/Vertical instead of just arrangment)
		{
			"do": {
				"label": "Lock arrangment. ", 
				"updateConstraintsCanvasShape": function keepArrangment(constraintsCanvasShape, designCanvasShape) {
					constraintsCanvasShape[CanvasMenuActions.locked_arrangement_key] = true; 

					// Also should the constraints canvas arrange itself in the way of the designs canvas?
				}
			}, 
			"undo": {
				"label": "Unlock arrangement. ",
				"updateConstraintsCanvasShape": function undoLockArrangment(constraintsCanvasShape, designCanvasShape) {
					// TODO: What does undo do?
					constraintsCanvasShape[CanvasMenuActions.locked_arrangement_key] = false;
				}
			}
		}
}

export default CanvasMenuActions; 
