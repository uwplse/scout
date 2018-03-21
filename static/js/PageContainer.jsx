// App.jsx
import React from "react";
import '../css/Canvas.css'; 
import 'whatwg-fetch'; 

export default class PageContainer extends React.Component {
  constructor(props) {
  	super(props); 
    this.drawCanvas = this.drawCanvas.bind(this); 
    this.fieldClicked = this.fieldClicked.bind(this); 
    this.textClicked = this.textClicked.bind(this); 
    this.buttonClicked = this.buttonClicked.bind(this); 
    this.getDesigns = this.getDesigns.bind(this); 

    this.canvas = undefined; 
    this.constraintsTop = 10; 

    // This collection contains the set of shapes on the constraints canvas
    this.constraintsShapes = []; 
  }

  componentDidMount() {
    // Construct the intial canvas
    this.drawCanvas(); 
  }

  getButton(left, top, cursor, selectable=true) {
    var rect = new fabric.Rect({
        width : 120,
        height : 40,
        fill : '#44ACB1'
    });

    var text = new fabric.IText('Button', {
      fontSize: 20, 
      fontFamily: 'Georgia', 
      strokeWidth:0, 
      fill: 'white', 
      left: 25, 
      top: 10
    });

    var group = new fabric.Group([ rect, text ], { 
        left: left, 
        top: top, 
        selectable: false, 
        hoverCursor: cursor, 
        selectable: selectable
      });

    return group; 
  }

  getText(left, top, cursor, selectable=true) {
    var text = new fabric.Text('Text', {
      fontSize: 60,
      left: left,
      top: top,
      fontFamily: 'Georgia',
      fill: '#000', 
      lockRotation: true, 
      hoverCursor: cursor, 
      selectable: selectable
    });

    return text; 
  }

  getInteractiveText(left, top, cursor, selectable=true) {
    var text = new fabric.IText('Text', {
      fontSize: 60,
      left: left,
      top: top,
      fontFamily: 'Georgia',
      fill: '#000', 
      lockRotation: true, 
      hoverCursor: cursor, 
      selectable: selectable
    });

    return text; 
  }

  getField(left, top, cursor, selectable=true) {
    var rect = new fabric.Rect({
        width : 120,
        height : 40,
        fill: 'white', 
        stroke: 'black', 
        strokeWidth: 1
    });

    var text = new fabric.Text('Field', {
      fontSize: 20, 
      fontFamily: 'Georgia', 
      strokeWidth:0, 
      fill: 'black', 
      top: 10, 
      left: 25
    });

    var group = new fabric.Group([ rect, text ], { 
        left: left, 
        top: top,
        hoverCursor: cursor, 
        selectable: selectable
      });

    return group;
  }

  fieldClicked() {
    this.constraintsTop += 50; 
    let top = this.constraintsTop; 
    let left = 20; 

    // Add a new field to the constraints canvas
    let field = this.getField(left, top);
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
    let text = this.getInteractiveText(left, top);
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
    let button = this.getButton(left, top);
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
    let field = this.getField(20,50,'hand',false); 
    let text = this.getText(20,150,'hand',false); 
    let button = this.getButton(20,250,'hand',false); 
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

    let jsonAllShapes = {
      "elements": shapeJSON
    }

    return JSON.stringify(jsonAllShapes); 
  }

  getDesigns() {
    let jsonShapes = this.getShapesJSON(); 
   
    // Send an ajax request to the server
    fetch('/solve', {
      method: 'POST',
      headers: {
        'Content-Type': 'application/json'
      },
      body: jsonShapes
    });
  }

  render () {
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
          <div className="widgets-container">
            <h1>Widgets</h1>
            <canvas id="widgets-canvas" width="200px" height="1000px">
            </canvas>
          </div>
          <div className="constraints-container"> 
            <h1>Constraints</h1>
            <canvas id="constraints-canvas" width="600px" height="1000px">
            </canvas>
          </div>
        </div>
      </div>
    ); 
  }
}