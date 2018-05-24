import React from "react";
import Resizable from 're-resizable';
import ConstraintActions from './ConstraintActions';
import SVGInline from "react-svg-inline"

export default class DesignCanvasSVGWidget extends React.Component {

  constructor(props) {
  	super(props); 
    this.type = props.shape.type; 
    this.controlType = props.shape.controlType; 
    this.id = props.id; 
    this.element = props.shape; // constraints shape object
    this.svgSource = props.source; 

    this.uniqueID = _.uniqueId();

    this.state = {
      height: props.height,
      width: props.width, 
      left: props.left, 
      top: props.top
    }
  }

  componentWillMount() {
    this.timer = null; 
  }

  componentDidMount() {
    // Set the initial value for the text label
    this.setTextLabel();   
  }

  setTextLabel(initSize) {
    let id = "design-canvas-widget-" + this.id + "-" + this.uniqueID; 
    let svgElement = document.getElementById(id); 
    let editableText = svgElement.querySelectorAll(".widget-editable-text");
    if(editableText[0]) {
      editableText[0].innerHTML = this.element.label;  
      editableText[0].style.fontSize = "50%";

      // Adjust the initial translation of the text to center it in the middle (only for buttons)
      let bboxText = editableText[0].getBoundingClientRect();
      let heightLocation = (this.state.height/2);
      if(this.controlType == "button") {
        editableText[0].style.transform = "translate(" + this.state.width/2 + "px," + heightLocation + "px)";  
      }    
      else if(this.controlType == "label") {
        editableText[0].style.transform = "translate(0px," + heightLocation + "px)";  
      }  
    }

    if(this.state.width == 0 || this.state.height == 0) {
      // give the component an initial size based on the calculated size of the text box
      let sizeContainer = svgElement.querySelectorAll(".widget-size-container"); 
      this.adjustElementSize(sizeContainer[0]);
    }
  }

  setElementSize(width, height) {
    // When height and width are updated by font size changes, update the element object. 
    this.element.size.height = height; 
    this.element.size.width = width; 
  }

  render () {
    const source = this.svgSource; 
    const height = this.state.height; 
    const width = this.state.width; 
    const left = this.state.left; 
    const top = this.state.top;
    return (
      <div id={"design-canvas-widget-" + this.id + "-" + this.uniqueID} className="widget-control-parent" 
        style={{position: "absolute", left: left + "px", top: top + "px"}}>
        <SVGInline className={"widget-control-" + this.controlType} svg={source} height={this.state.height + "px"} width={this.state.width + "px"} />
      </div>); 
  }
}
