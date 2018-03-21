// App.jsx
import React from "react";
import '../css/Canvas.css'; 
import 'whatwg-fetch'; 
import Canvas from "./Canvas"; 
import FabricHelpers from './FabricHelpers.js';

export default class PageContainer extends React.Component {
  constructor(props) {
  	super(props); 
    this.drawCanvas = this.drawCanvas.bind(this); 
    this.fieldClicked = this.fieldClicked.bind(this); 
    this.textClicked = this.textClicked.bind(this); 
    this.buttonClicked = this.buttonClicked.bind(this); 
    this.getDesigns = this.getDesigns.bind(this); 
    this.parseSolutions = this.parseSolutions.bind(this);

    this.canvas = undefined; 
    this.constraintsTop = 10; 

    // This collection contains the set of shapes on the constraints canvas
    this.constraintsShapes = []; 

    // This is the set of design canvases in the design window
    this.state = { designCanvases: [] }; 
  }

  componentDidMount() {
    // Construct the intial canvas
    this.drawCanvas(); 
  }


  fieldClicked() {
    this.constraintsTop += 50; 
    let top = this.constraintsTop; 
    let left = 20; 

    // Add a new field to the constraints canvas
    let field = FabricHelpers.getField(left, top,120,40);
    this.constraintsCanvas.add(field); 

    // Set up the JSON object
    let json = {
      "name": _.uniqueId(),
      "label": "field", 
      "type": "field", 
      "shape": field
    }

    this.constraintsShapes.push(json); 
  }

  textClicked() {
    this.constraintsTop += 50; 
    let top = this.constraintsTop; 
    let left = 20; 

    // Add a new text to the constraints canvas
    let text = FabricHelpers.getInteractiveText(left, top);
    this.constraintsCanvas.add(text); 

    // Set up the JSON object
    let json = {
      "name": _.uniqueId(),
      "label": "text", 
      "type": "text", 
      "shape": text
    }

    this.constraintsShapes.push(json); 
  }

  buttonClicked() {
    this.constraintsTop += 50; 
    let top = this.constraintsTop; 
    let left = 20; 

    // Add a new field to the constraints canvas
    let button = FabricHelpers.getButton(left, top,120,40);
    this.constraintsCanvas.add(button); 

    // Set up the JSON object
    let json = {
      "name": _.uniqueId(),
      "label": "button", 
      "type": "button", 
      "shape": button
    }

    this.constraintsShapes.push(json);  
  }

  drawCanvas() {
    this.widgetsCanvas = new fabric.Canvas('widgets-canvas');
    let field = FabricHelpers.getField(20,50,120,40,'hand',false); 
    let text = FabricHelpers.getText(20,150,'hand',false); 
    let button = FabricHelpers.getButton(20,250,120,40,'hand',false); 
    field.on('mousedown', this.fieldClicked); 
    text.on('mousedown', this.textClicked); 
    button.on('mousedown', this.buttonClicked); 
    this.widgetsCanvas.add(field); 
    this.widgetsCanvas.add(text); 
    this.widgetsCanvas.add(button); 


    this.constraintsCanvas = new fabric.Canvas('constraints-canvas'); 
  }

  getShapesJSON() {
    // Get all of the shapes on the canvas into a collection 
    let shapeJSON = []; 
    for(var i=0; i<this.constraintsShapes.length; i++) {
      let shape = this.constraintsShapes[i]; 
      let jsonShape = {}; 
      let fabricShape = shape.shape; 

      jsonShape["name"] = shape.name; 
      jsonShape["label"] = shape.label;
      jsonShape["type"] = shape.type;

      jsonShape["location"] = {
        "x": fabricShape.left, 
        "y": fabricShape.top
      }

      jsonShape["size"] = {
        "width": fabricShape.width, 
        "height": fabricShape.height

      }

      shapeJSON.push(jsonShape); 
    }  

    return JSON.stringify(shapeJSON)
  }

  parseSolutions(requestData) {
    let resultsParsed = JSON.parse(requestData); 
    let solutions = resultsParsed.elements;
    let designCanvasList = this.state.designCanvases; 
    for(let i=0; i<solutions.length; i++) {
      let solution = solutions[i]; 
      let elements = solution.elements; 
      designCanvasList.push(<Canvas key={solution.id} id={solution.id} elements={elements} />); 
    }

    this.setState({
      designCanvases: designCanvasList
    });
  }

  getDesigns() {
    let jsonShapes = this.getShapesJSON(); 
   
   // Send an ajax request to the server 
   // Solve for the new designs
    $.post("/solve", {"elements": jsonShapes}, this.parseSolutions, 'text');
  }

  render () {
    const designs = this.state.designCanvases;
    return (
      <div className="page-container">
        <nav className="navbar navbar-default">
         <div className="container-fluid">
          <div className="navbar-header">
            <button type="button" className="btn btn-default navbar-btn" onClick={this.getDesigns}>Get Designs</button>
          </div>
         </div>
        </nav>
        <div className="bottom">
          <div className="panel panel-primary widgets-container">
            <div className="panel-heading"> 
              <h3 className="panel-title">Widgets</h3>
            </div>  
            <div className="panel-body">         
              <canvas id="widgets-canvas" width="200px" height="667px">
              </canvas>
            </div>
          </div>
          <div className="panel panel-primary constraints-container">
            <div className="panel-heading"> 
              <h3 className="panel-title">Constraints</h3>
            </div>
            <div className="panel-body">
              <canvas id="constraints-canvas" width="375px" height="667px">
              </canvas>
            </div>
          </div>
          <div className="panel panel-primary designs-container">
            <div className="panel-heading"> 
              <h3 className="panel-title">Designs</h3>
            </div>
            <div className="panel-body design-body">
            {designs}
            </div>
          </div>
        </div>
      </div>
    ); 
  }
}