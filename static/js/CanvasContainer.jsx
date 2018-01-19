// App.jsx
import React from "react";
import Canvas from "./Canvas";

export default class CanvasContainer extends React.Component {
  constructor(props) {
  	super(props); 
    this.drawCanvas = this.drawCanvas.bind(this); 
    this.state = { canvases: [] }; 
  }

  drawCanvas(canvas, width, height, background) {
    let children = canvas["elements"];
    let id = canvas["id"];
    let canvasList = this.state.canvases; 
    canvasList.push(<Canvas elements={children} id={id} key={id} width={width} height={height} background={background}/>)
  }

  componentDidMount() {
		// Request the elements from the configuration file
		var self = this; 
		$.get('/get_elements', 
			function (data) {
				let resultsParsed = JSON.parse(data); 
        let elements = resultsParsed.elements; 
        let size = resultsParsed.size; 
        let background = resultsParsed.background; 
        for(var i=0; i<elements.length; i++){
          let canvas = elements[i]; 
          self.drawCanvas(canvas, size.width, size.height, background); 
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