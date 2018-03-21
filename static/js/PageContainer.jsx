// App.jsx
import React from "react";
import '../css/Canvas.css'; 

export default class PageContainer extends React.Component {
  constructor(props) {
  	super(props); 
    this.drawCanvas = this.drawCanvas.bind(this); 
    this.fieldClicked = this.fieldClicked.bind(this); 
    this.textClicked = this.textClicked.bind(this); 
    this.buttonClicked = this.buttonClicked.bind(this); 

    this.canvas = undefined; 
    this.constraintsTop = 10; 
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

    var text = new fabric.Text('Button', {
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

  }

  textClicked() {
    this.constraintsTop += 50; 
    let top = this.constraintsTop; 
    let left = 20; 

    // Add a new text to the constraints canvas
    let field = this.getInteractiveText(left, top);
    this.constraintsCanvas.add(field); 
  }

  buttonClicked() {
    this.constraintsTop += 50; 
    let top = this.constraintsTop; 
    let left = 20; 

    // Add a new field to the constraints canvas
    let field = this.getButton(left, top);
    this.constraintsCanvas.add(field); 
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

  render () {
    return (
      <div className="page-container">
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
    ); 
  }
}