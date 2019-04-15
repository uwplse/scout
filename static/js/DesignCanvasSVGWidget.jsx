import React from "react";
import ConstraintActions from './ConstraintActions';
import SVGInline from "react-svg-inline"

const TOUCH_TARGETS = ["button", "field", "separator"]; 

export default class DesignCanvasSVGWidget extends React.Component {

  constructor(props) {
  	super(props); 
    this.timer = null;

    this.uniqueID = _.uniqueId();
  }

  onClick = (evt) => {
    // Stop the event from propagating to the canvas shape. 
    evt.stopPropagation();
    
    this.props.setPrimarySelection(this.props.shape); 
  }

  replaceViewBox = (svgSource) => {
    let newSvg = svgSource; 
    if(TOUCH_TARGETS.indexOf(this.props.shape.type) > -1) {
      let factor = 1/this.props.scale; 
      let newViewBox = "viewBox=\"0 0 " + (this.props.width * factor) + " " + (this.props.height * factor) + "\""; 
      newSvg = svgSource.replace(/viewBox="[a-zA-Z0-9_\s]+"/, newViewBox); 
    }
    return newSvg; 
  }

  render () {
    const source = this.replaceViewBox(this.props.source); 
    const height = this.props.height; 
    const width = this.props.width; 
    const left = this.props.left; 
    const top = this.props.top;    
    let isContainer = (this.props.shape.type == "group" || this.props.shape.type == "labelGroup" || this.props.shape.type == "canvas"); 
    const isPrimary = this.props.primarySelection && this.props.primarySelection == this.props.shape;
    const isSecondary = this.props.primarySelection && !isPrimary && this.props.primarySelection.name == this.props.shape.name; 

    return (
      <div 
        id={"design-canvas-widget-" + this.props.id + "-" + this.uniqueID} 
        onClick={this.onClick}
        className={"design-canvas-widget " 
          + (isPrimary ? "primary-selection" : " ")
          + (isSecondary ? "secondary-selection" : "")}
        style={{position: "absolute", left: left + "px", top: top + "px"}}>
        <SVGInline 
          className={"widget-control-" + this.props.type} 
          svg={source} 
          height={this.props.height + "px"} 
          width={this.props.width + "px"} />
      </div>); 
  }
}
