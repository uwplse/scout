import Constants from "./Constants.js"; 

class CanvasMenuActions {}
CanvasMenuActions.elementConstraints = {
	"locked_position": {
		"do": {
			"label": "Lock position.",
			"callback": function lockPosition(constraintsCanvasShape, designCanvasShape) {
			    // Update the property on shape according to the selected option
			    // Use the server key for locking a shape into a specific location
			    constraintsCanvasShape['locked_position'] = true; 
			    designCanvasShape['locked_position'] = true; 

			    // Then update the location of the constraints canvas shape to that of the design canvas shape
			    constraintsCanvasShape.shape.set({
			    	left: designCanvasShape.shape.left * Constants.designCanvasScalingFactor, 
			    	top: designCanvasShape.shape.top * Constants.designCanvasScalingFactor 
			    }); 
			}
		}, 
		"undo": {
			"label": "Unlock position.", 
			"callback": function undoLockPosition(constraintsCanvasShape, designCanvasShape) {
				constraintsCanvasShape['locked_position'] = false; 
				designCanvasShape['locked_position'] = false; 
				// What does it mean to undo this action?
			}
		} 
	}
}

export default CanvasMenuActions; 
