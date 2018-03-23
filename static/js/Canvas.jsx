// App.jsx
import React from "react";
import FabricHelpers from "./FabricHelpers.js"; 
import CanvasMenu from "./CanvasMenu"; 

export default class Canvas extends React.Component {
  constructor(props) {
  	super(props);
  	this.showConstraintsContextMenu.bind(this); 

  	// Shapes to be drawn onto the canvas
  	this.elements = props.elements; 
  	this.id = props.id; 

  	this.state = {
  		menuShown: false, 
  		menuPosition: { x: 0, y: 0 }
  	}; 
  } 

  drawShapes() {
  	// Draw each shape in the collection
  }

  getScaledBounds(x,y,width,height) {
  	return [x/2,y/2,width/2,height/2]; 
  }

  showConstraintsContextMenu(shape,evt) {
  	if(evt.button == 1) {
  		// evt.stopPropagation(); // Prevent it from bubbling to the canvas

  		// Show the context menu. 
  		let componentBoundingBox = this.refs["design-canvas-" + this.id].getBoundingClientRect(); 
	    this.setState({
	      menuShown: true, 
	      menuPosition: {
	      	x: componentBoundingBox.x + shape.left + (shape.width/2), 
	      	y: componentBoundingBox.y + shape.top + (shape.height/2)
	      }
	    });
    }
  }

  // hideConstraintsContextMenu

  componentDidMount() {
    this.canvas = new fabric.Canvas('design-canvas-' + this.id); 
    this.canvas.on("mousedown", this.)

	// When the component mounts, draw the shapes onto the canvas
	for(var i=0; i<this.elements.length; i++) {
		let element = this.elements[i]; 

		// Scale down the values
		let x = element.location.x/2; 
		let y = element.location.y/2; 
		let width = element.size.width/2; 
		let height = element.size.height/2; 
		if(element.type == "button") {
			let button = FabricHelpers.getButton(x,y,width,height,{'cursor': 'hand', 'selectable': false}); 
			button.on("mousedown", this.showConstraintsContextMenu.bind(this,button));
			this.canvas.add(button); 
		}
		else if (element.type == "text") {
			let fontSize = height/2; // TODO: Hack. Fix this later
			let text = FabricHelpers.getText(x,y,fontSize,{'cursor': 'hand', 'selectable': false}); 
			text.on("mousedown", this.showConstraintsContextMenu.bind(this,text));
			this.canvas.add(text); 
		}
		else if (element.type == "field") {
			let field = FabricHelpers.getField(x,y,width,height,{'cursor': 'hand', 'selectable': false}); 
			field.on("mousedown", this.showConstraintsContextMenu.bind(this,field));
			this.canvas.add(field); 
		}
	}
  }

  render () {
 	let menuShown = this.state.menuShown; 
 	let menuPosition = this.state.menuPosition; 
    return  (<div className="canvas-container" id={"canvas-box-" + this.id}> 
    			<div style={{left: menuPosition.x, top: menuPosition.y}} className={"canvas-menu-container " + (menuShown ? "" : "hidden")}>{menuShown ? <CanvasMenu /> : null}</div>
	    		<canvas ref={"design-canvas-" + this.id} className="design-canvas" id={"design-canvas-" + this.id} width="187.5px" height="333px">
	            </canvas>
	         </div>); 
  }
}
