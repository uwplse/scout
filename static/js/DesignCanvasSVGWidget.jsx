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
    this.contextMenu = props.contextMenu; 

    // Method bindings
    this.setHovered = this.setHovered.bind(this); 
    this.hideHovered = this.hideHovered.bind(this);
    this.contextMenuClicked = this.contextMenuClicked.bind(this);

    this.uniqueID = _.uniqueId();

    this.state = {
      height: props.height,
      width: props.width, 
      left: props.left, 
      top: props.top, 
      hovered: false, 
      fontSize: this.element.fontSize,
      scaling: props.scalingFactor
    }
  }

  static getDerivedStateFromProps(nextProps, prevState) {
    return {
      height: nextProps.height,
      width: nextProps.width, 
      left: nextProps.left, 
      top: nextProps.top, 
      hovered: prevState.hovered, 
      fontSize: prevState.fontSize, 
      scaling: nextProps.scaling
    }
  }

  componentWillMount() {
    this.timer = null; 
  }

  componentDidMount() {
    // Set the initial value for the text label
    this.setTextLabel();  
    this.rescaleTextLabel();
  }

  setTextLabel() {
    let id = "design-canvas-widget-" + this.id + "-" + this.uniqueID; 
    let svgElement = document.getElementById(id); 
    let editableText = svgElement.querySelectorAll(".widget-editable-text");

    // if(this.controlType == "label") {
    //   // Unset these so that we can calculate a new size after the font size is changed
    //   let svgElementInline = svgElement.querySelectorAll(".SVGInline-svg"); 
    //   svgElementInline[0].style.width = ""; 
    //   svgElementInline[0].style.height = "";
    //   console.log("unset text sizes");
    // }

    if(editableText.length) {
      editableText[0].innerHTML = this.element.label;  
    
      if(this.controlType == "label") {
        let textArea = editableText[0].getBoundingClientRect(); 
        console.log(textArea.height);
        console.log(textArea.width);
        this.setState({
          height: Math.round(textArea.height,0), 
          width: Math.round(textArea.width,0)
        }); 
      }
    }
  }

  rescaleTextLabel() {
    let id = "design-canvas-widget-" + this.id + "-" + this.uniqueID; 
    let svgElement = document.getElementById(id); 
    if(svgElement) {
      let editableText = svgElement.querySelectorAll(".widget-editable-text");
      if(editableText.length) {
        let scaledFont = 100 * this.state.scaling; 
        editableText[0].style.fontSize = scaledFont + "%"; 

        if(this.type == "button") {
          editableText[0].style.transform = "translate(" + Math.round(this.state.width/2,0) + "px," + Math.round(this.state.height/2,0) + "px)"; 
        }
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

  contextMenuClicked(evt) {
    this.contextMenu(this.element, evt);
  }

  render () {
    const source = this.svgSource; 
    const height = this.state.height; 
    const width = this.state.width; 
    const left = this.state.left; 
    const top = this.state.top;
    const fontSize = (this.type == "label" ? { fontSize: this.state.fontSize } : {}); 
    this.rescaleTextLabel();
    console.log(this.state.height); 
    console.log(this.state.width); 
    return (
      <div id={"design-canvas-widget-" + this.id + "-" + this.uniqueID} onContextMenu={this.contextMenuClicked}
        className={"widget-control-parent "  + (this.state.hovered ? "design-canvas-hovered" : "")}
        onMouseEnter={this.setHovered}
        onMouseLeave={this.hideHovered}
        style={{position: "absolute", left: left + "px", top: top + "px"}}>
        <SVGInline style={fontSize} className={"widget-control-" + this.controlType} svg={source} height={this.state.height + "px"} width={this.state.width + "px"} />
      </div>); 
  }
}
