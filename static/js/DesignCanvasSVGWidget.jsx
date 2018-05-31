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

    // Method bindings
    this.setHovered = this.setHovered.bind(this); 
    this.hideHovered = this.hideHovered.bind(this);

    this.uniqueID = _.uniqueId();

    this.state = {
      height: props.height,
      width: props.width, 
      left: props.left, 
      top: props.top, 
      hovered: false, 
      fontSize: this.element.fontSize
    }
  }

  componentWillMount() {
    this.timer = null; 
  }

  componentDidMount() {
    // Set the initial value for the text label
    this.setTextLabel();  
  }

  setTextLabel() {
    let id = "design-canvas-widget-" + this.id + "-" + this.uniqueID; 
    let svgElement = document.getElementById(id); 
    let editableText = svgElement.querySelectorAll(".widget-editable-text");

    if(this.type == "label") {
      let svgElementInline = svgElement.querySelectorAll(".SVGInline-svg"); 
      svgElementInline[0].setAttribute("font-size", this.element.fontSize); 

      if(this.controlType == "label") {
        // Unset these so that we can calculate a new size after the font size is changed
        svgElementInline[0].style.width = ""; 
        svgElementInline[0].style.height = "";
      }
    }

    if(editableText[0]) {
      editableText[0].innerHTML = this.element.label;  
      editableText[0].style.fontSize = "50%"; 

      // Adjust the initial translation of the text to center it in the middle (only for buttons)
      let bboxText = editableText[0].getBoundingClientRect();
      if(this.type == "label") {
        this.setState({
          height: Math.round(bboxText.height,0), 
          width: Math.round(bboxText.width)
        }); 
      }
    }
  }

  setElementSize(width, height) {
    // When height and width are updated by font size changes, update the element object. 
    this.element.size.height = height; 
    this.element.size.width = width; 
  }

  setHovered(evt) {
    this.setState({
      hovered: true
    }); 
  }

  hideHovered(evt) {
    let id = "design-canvas-widget-" + this.id + "-" + this.uniqueID; 
    let element = document.getElementById(id); 
    let elementBox = element.getBoundingClientRect();

    this.setState({
      hovered: false
    }); 
  }

  render () {
    const source = this.svgSource; 
    const height = this.state.height; 
    const width = this.state.width; 
    const left = this.state.left; 
    const top = this.state.top;
    const fontSize = (this.type == "label" ? { fontSize: this.state.fontSize } : {}); 
    return (
      <div id={"design-canvas-widget-" + this.id + "-" + this.uniqueID} 
        className={"widget-control-parent "  + (this.state.hovered ? "design-canvas-hovered" : "")}
        onMouseEnter={this.setHovered}
        onMouseLeave={this.hideHovered}
        style={{position: "absolute", left: left + "px", top: top + "px"}}>
        <SVGInline style={fontSize} className={"widget-control-" + this.controlType} svg={source} height={this.state.height + "px"} width={this.state.width + "px"} />
      </div>); 
  }
}
