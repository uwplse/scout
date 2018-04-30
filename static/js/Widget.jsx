// App.jsx
import React from "react";
import FabricHelpers from './FabricHelpers';

export default class Widget extends React.Component {
  constructor(props) {
  	super(props); 
    this.type = props.type; 
    this.id = props.id; 
    this.element = props.shape; // constraints shape object

    this.defaultControlHeight = props.height; 
    this.defaultControlWidth = props.width;

    // mapping of shape types to handler functions
    this.shapeAddHandlers = {
      'text': this.addTextToCanvas.bind(this), 
      'button': this.addButtonToCanvas.bind(this), 
      'field': this.addFieldToCanvas.bind(this), 
      'labelGroup': this.addLabelGroupToCanvas.bind(this), 
      'group': this.addGroupToCanvas.bind(this)
    }; 
  }

  componentDidMount() {
    this.canvas = new fabric.Canvas('widget-canvas-' + this.id); 

    let shapeAddHandler = this.shapeAddHandlers[this.type];
    shapeAddHandler();

    this.canvas.renderAll(); 
  }

  componentWillUnmount() {
    this.canvas.dispose();
  }

  addLabelGroupToCanvas() {
    let groupRect = FabricHelpers.getGroup(0,0, this.defaultControlWidth, this.defaultControlHeight, {
      stroke: 'red', 
      groupType: 'Label', 
      strokeDashArray: [5,5]
    });

    this.canvas.add(groupRect)
  }

  addGroupToCanvas() {
    let groupRect = FabricHelpers.getGroup(0, 0, this.defaultControlWidth, this.defaultControlHeight, {
      stroke: '#39a1f4', 
      groupType: 'Group', 
      strokeDashArray: [5,5]
    });

    this.canvas.add(groupRect); 
  }

  addFieldToCanvas() {
    // Add a new field to the constraints canvas
    let field = FabricHelpers.getInteractiveField(0,0, this.defaultControlWidth, this.defaultControlHeight, {'selectable': true});
    this.canvas.add(field.field); 
    this.canvas.add(field.line);
    this.element.size = {}; 
    this.element.size.width = this.defaultControlWidth; 
    this.element.size.height = this.defaultControlHeight;

    let shape = this.element;
    field.field.on("modified", function() {
      shape["label"] = field.field.text; 
    }); 
  }

  addTextToCanvas() {
    // Add a new text to the constraints canvas
    let text = FabricHelpers.getInteractiveText(0, 0, 20, {'selectable': true});
    this.canvas.add(text);
    this.element.size = {}; 
    this.element.size.width = 50; 
    this.element.size.height = 40; 

    // Update the label when the text is modified
    let shape = this.element; 
    text.on("modified", function() {
      shape["label"] = text.text;
    }); 
  }

  addButtonToCanvas() {
    let button = FabricHelpers.getInteractiveButton(0, 0, this.defaultControlWidth, this.defaultControlHeight, {'selectable': true});
    this.canvas.add(button.button);
    this.canvas.add(button.label);   

    this.element.size = {}; 
    this.element.size.width = this.defaultControlWidth; 
    this.element.size.height = this.defaultControlHeight;

    let shape = this.element; 
    button.label.on("modified", function() {
      shape["label"] = button.label.text
    }); 
  }

  render () {
    return (
      <div className="widget-container">
        <canvas id={"widget-canvas-"  + this.id} className="widget-canvas" width={this.defaultControlWidth + "px"} height={this.defaultControlHeight + "px"}></canvas>
      </div>); 
  }














}
