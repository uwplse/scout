// App.jsx
import React from "react";
import '../css/Canvas.css'; 

export default class Canvas extends React.Component {
  constructor(props) {
  	super(props); 
  	this.drawElements = this.drawElements.bind(this); 
  	this.drawButton = this.drawButton.bind(this); 
  }

  drawButton(x, y, width, height) {
  	this.ctx.fillStyle = 'grey'; 
  	this.ctx.fillRect(x, y, width, height); 
  }

  drawField(x, y, width, height) {
  	this.ctx.fillStyle = 'white'; 
  	this.ctx.strokeStyle = 'grey'; 
  	this.ctx.strokeRect(x, y, width, height); 
  }

  drawLink(x, y, width, height, text) {
  	this.ctx.fillStyle = 'blue'; 
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
  			this.drawButton(x, y, width, height);
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

  componentDidMount() {
  	var canvas = document.getElementById("shape-canvas")
  	if (canvas.getContext) {
  		this.ctx = canvas.getContext("2d"); 

  		// Request the elements from the configuration file
  		var self = this; 
		$.get('/get_elements', 
			function (data) {
				let elementsParsed = JSON.parse(data); 
				self.drawElements(elementsParsed); 
			}
		);
  	}
  }

  render () {
    return <canvas className="canvas" id="shape-canvas" width="450px" height="350px"></canvas>;
  }
}

// Shape types link, button, logo, image