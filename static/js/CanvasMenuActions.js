import Constants from "./Constants.js"; 

class CanvasMenuActions {}
CanvasMenuActions.locked_position_key = 'locked_position'; 
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

export default CanvasMenuActions; 
