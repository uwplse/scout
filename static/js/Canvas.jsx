// App.jsx
import React from "react";
import FabricHelpers from "./FabricHelpers.js"

export default class Canvas extends React.Component {
  constructor(props) {
  	super(props);
  	// Shapes to be drawn onto the canvas
  	this.elements = props.elements; 
  	this.id = props.id; 
  } 

  drawShapes() {
  	// Draw each shape in the collection
  }

  getScaledBounds(x,y,width,height) {
  	return [x/2,y/2,width/2,height/2]; 
  }

  componentDidMount() {
    this.canvas = new fabric.Canvas('design-canvas-' + this.id); 

	// When the component mounts, draw the shapes onto the canvas
	for(var i=0; i<this.elements.length; i++) {
		let element = this.elements[i]; 

		// Scale down the values
		let x = element.location.x/2; 
		let y = element.location.y/2; 
		let width = element.size.width/2; 
		let height = element.size.height/2; 
		if(element.type == "button") {
			let button = FabricHelpers.getButton(x,y,width,height); 
			this.canvas.add(button); 
		}
		else if (element.type == "text") {
			let text = FabricHelpers.getText(x,y); 
			this.canvas.add(text); 
		}
		else if (element.type == "field") {
			let field = FabricHelpers.getField(x,y,width,height); 
			this.canvas.add(field); 
		}
	}
  }

  render () {
    return  <canvas className="design-canvas" id={"design-canvas-" + this.id} width="187.5px" height="333px">
            </canvas>; 
  }
}
