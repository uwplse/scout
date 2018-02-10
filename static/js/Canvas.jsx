// App.jsx
import React from "react";
import '../css/Canvas.css'; 

export default class Canvas extends React.Component {
  constructor(props) {
  	super(props); 
  	this.drawElements = this.drawElements.bind(this); 
  	this.drawButton = this.drawButton.bind(this); 
    this.elements = props.elements; 
    this.id = props.id; 
    this.width = props.width; 
    this.height = props.height; 
    this.background = props.background; 
  }

  componentDidMount() {
    var canvas = document.getElementById(this.id)
    if (canvas.getContext) {
      this.ctx = canvas.getContext("2d"); 
      this.drawElements(this.elements); 
    }
  }

  drawButton(x, y, width, height, label) {
  	this.ctx.fillStyle = 'grey'; 
  	this.ctx.fillRect(x, y, width, height); 
    this.ctx.fillStyle = 'white'; 
    this.ctx.fillText(label, x+(width/4), y+(height/2))
  }

  drawField(x, y, width, height) {
  	this.ctx.fillStyle = 'white'; 
  	this.ctx.strokeStyle = 'grey'; 
  	this.ctx.strokeRect(x, y, width, height); 
  }

  drawLink(x, y, width, height, text) {
  	this.ctx.fillStyle = 'white'; 
  	this.ctx.textBaseline = 'top'; 
  	this.ctx.fillText(text, x, y); 
  }

  drawImage(x, y, width, height, source) {
  	var img = new Image(); 
  	var self = this; 
  	img.onload = function() {
  		self.ctx.drawImage(img, x, y, width, height);   		
  	}

  	img.src = source; 
  }

  drawElements(elements) {
  	for(var i=0; i<elements.length; i++) {
  		var element = elements[i]; 
  		var x = element.location.x; 
  		var y = element.location.y;
  		var width = element.size.width; 
  		var height = element.size.height; 
  		if(element.type == "button") {
        let label = element.label; 
  			this.drawButton(x, y, width, height, label);
  		} 
  		else if (element.type == "image") {
  			this.drawImage(x, y, width, height, element.source); 
  		}
  		else if (element.type == "link") {
  			this.drawLink(x, y, width, height, element.label); 
  		}
  		else if (element.type == "field") {
  			this.drawField(x, y, width, height); 
  		}
  	}
  }

  render () {
    return <canvas className="canvas" id={this.id} width={this.width + "px"} height={this.height + "px"} style={{backgroundColor: this.background}}>
           </canvas>;
  }
}

// Shape types link, button, logo, image