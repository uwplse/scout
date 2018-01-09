// App.jsx
import React from "react";
import Canvas from "./Canvas";

export default class CanvasContainer extends React.Component {
  constructor(props) {
  	super(props); 
    this.drawCanvas = this.drawCanvas.bind(this); 
    this.state = { canvases: [] }; 
  }

  drawCanvas(canvas) {
    let children = canvas["elements"];
    let id = canvas["id"];
    let canvasList = this.state.canvases; 
    canvasList.push(<Canvas elements={children} id={id} key={id} />)
  }

  componentDidMount() {
		// Request the elements from the configuration file
		var self = this; 
		$.get('/get_elements', 
			function (data) {
				let elementsParsed = JSON.parse(data); 
        for(var i=0; i<elementsParsed.length; i++){
          let canvas = elementsParsed[i]; 
          self.drawCanvas(canvas); 
        }

        let canvasList = self.state.canvases; 
        self.setState({
          canvases: canvasList
        });
			}
		);
  }

  render () {
    const canvasList = this.state.canvases;
    return <div className="canvas-container" id="canvas-container">{canvasList}</div>;
  }
}