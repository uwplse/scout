import React from "react";
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
    this.displayWidgetFeedback = props.displayWidgetFeedback; 
    this.timer = null;

    this.uniqueID = _.uniqueId();
  }

  onClick = (evt) => {
    // Stop the event from propagating to the canvas shape. 
    evt.stopPropagation();
    
    this.displayWidgetFeedback(this.element); 
  }

  replaceViewBox = (svgSource) => {
    let factor = 1/this.props.scale; 
    let newViewBox = "viewBox=\"0 0 " + (this.props.width * factor) + " " + (this.props.height * factor) + "\""; 
    let newSvg = svgSource.replace(/viewBox="[a-zA-Z0-9_\s]+"/, newViewBox); 
    return newSvg; 
  }

  render () {
    const source = this.replaceViewBox(this.svgSource); 
    const height = this.props.height; 
    const width = this.props.width; 
    const left = this.props.left; 
    const top = this.props.top;    
    let isContainer = (this.type == "group" || this.type == "labelGroup" || this.type == "canvas"); 
    const isPrimary = this.props.primarySelection && this.props.primarySelection == this.props.shape;
    const isSecondary = this.props.primarySelection && !isPrimary && this.props.primarySelection.name == this.props.shape.name; 

    return (
      <div 
        id={"design-canvas-widget-" + this.id + "-" + this.uniqueID} 
        onClick={this.onClick}
        className={"design-canvas-widget " 
          + (isPrimary ? "primary-selection" : " ")
          + (isSecondary ? "secondary-selection" : "")}
        style={{position: "absolute", left: left + "px", top: top + "px"}}>
        <SVGInline 
          className={"widget-control-" + this.type} 
          svg={source} 
          height={this.props.height + "px"} 
          width={this.props.width + "px"} />
      </div>); 
  }
}
