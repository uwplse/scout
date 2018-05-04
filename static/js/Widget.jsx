// App.jsx
import React from "react";
import FabricHelpers from './FabricHelpers';

export default class Widget extends React.Component {
  
  static initialWidthValues(type) {
    let values = {
      'button': 120, 
      'text': 120, 
      'field':  120, 
      'group': 120, 
      'labelGroup': 120
    }; 
    return values[type]; 
  }; 

  static initialHeightValues(type) {
    let values =  {
      'button': 40, 
      'text': 40, 
      'field': 40, 
      'group': 40,
      'labelGroup': 40
    };
    return values[type];
  }; 

  constructor(props) {
  	super(props); 
    this.type = props.type; 
    this.id = props.id; 
    this.element = props.shape; // constraints shape object

    // Callback to notify the parent container to re-check the solution validity
    this.checkSolutionValidity =  props.checkSolutionValidity; 

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
    let groupRect = FabricHelpers.getGroup(0,0, 120, 40, {
      stroke: 'red', 
      groupType: 'Label', 
      strokeDashArray: [5,5]
    });

    this.canvas.add(groupRect)
  }

  addGroupToCanvas() {
    let groupRect = FabricHelpers.getGroup(0, 0, 120, 40, {
      stroke: '#39a1f4', 
      groupType: 'Group', 
      strokeDashArray: [5,5]
    });

    this.canvas.add(groupRect); 
  }

  addFieldToCanvas() {
    // Add a new field to the constraints canvas
    let label = this.element.label; 
    let field = FabricHelpers.getInteractiveField(0,0, this.element.size.width, this.element.size.height, {'selectable': true, 'text': label});
    this.canvas.add(field.field); 
    this.canvas.add(field.line);


    let shape = this.element;
    let self = this; 
    field.field.on("modified", function() {
      shape["label"] = field.field.text; 

      // Notify the parent to update the solution state after any property of the widget changes
      self.checkSolutionValidity();
    }); 
  }

  addTextToCanvas() {
    // Add a new text to the constraints canvas
    let label = this.element.label;
    let text = FabricHelpers.getInteractiveText(0, 0, 20, {'selectable': true, 'text': label});
    this.canvas.add(text);

    // Update the label when the text is modified
    let shape = this.element; 
    let self = this; 
    text.on("modified", function() {
      shape.label = text.text; 

      // Also update the height and width of the text to tell the solver the calculated size. 
      shape.size.height = Math.round(text.height); 
      shape.size.width = Math.round(text.width);

      // Notify the parent to update the solution state after any property of the widget changes
      self.checkSolutionValidity();
    }); 
  }

  addButtonToCanvas() {
    let button = FabricHelpers.getInteractiveButton(0, 0, this.element.size.width, this.element.size.height, {'selectable': true});
    this.canvas.add(button.button);
    this.canvas.add(button.label);   

    let shape = this.element; 
    let self = this; 
    button.label.on("modified", function() {
      shape["label"] = button.label.text

      // Notify the parent to update the solution state after any property of the widget changes
      self.checkSolutionValidity();
    }); 
  }

  render () {
    return (
      <div className="widget-container">
        <canvas id={"widget-canvas-"  + this.id} className="widget-canvas" width={this.element.size.width + "px"} height={this.element.size.height + "px"}></canvas>
      </div>); 
  }














}
