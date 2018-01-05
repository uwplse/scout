// App.jsx
import React from "react";
export default class Canvas extends React.Component {
  constructor(props) {
  	super(props); 
  	this.drawElements = this.drawElements.bind(this); 
  	this.drawButton = this.drawButton.bind(this); 
  }

  drawButton(x, y) {
  	this.ctx.fillStyle = 'grey'; 
  	this.ctx.fillRect(x, y, 100, 30); 
  }

  drawField(x, y) {
  	this.ctx.fillStyle = 'white'; 
  	this.ctx.strokeStyle = 'grey'; 
  	this.ctx.strokeRect(x, y, 200, 30); 
  }

  drawLink(x, y, text) {
  	this.ctx.fillStyle = 'blue'; 
  	this.ctx.fillText(text, x, y); 
  }

  drawImage(x, y, source) {
  	var img = new Image(); 
  	var self = this; 
  	img.onload = function() {
  		self.ctx.drawImage(img, x, y);   		
  	}

  	img.src = source; 
  }

  drawElements(elements) {
  	for(var i=0; i<elements.length; i++) {
  		var element = elements[i]; 
  		var x = element.location.x; 
  		var y = element.location.y;

  		if(element.type == "button") {
  			this.drawButton(x, y);
  		} 
  		else if (element.type == "image") {
  			this.drawImage(x, y, element.source); 
  		}
  		else if (element.type == "link") {
  			this.drawLink(x, y, element.label); 
  		}
  		else if (element.type == "field") {
  			this.drawField(x, y); 
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
    return <canvas id="shape-canvas" width="450px" height="350px"></canvas>;
  }
}

// Shape types link, button, logo, image