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

    this.state = {
      height: props.height,
      width: props.width, 
      left: props.left, 
      top: props.top, 
      scaling: props.scaling, 
      primarySelection: props.primarySelection
    }
  }

  static getDerivedStateFromProps(nextProps, prevState) {
    return {
      height: prevState.height,
      width: prevState.width, 
      left: prevState.left, 
      top: prevState.top, 
      scaling: nextProps.scaling, 
      primarySelection: nextProps.primarySelection
    }
  }

  onClick = (evt) => {
    // Stop the event from propagating to the canvas shape. 
    evt.stopPropagation();
    
    this.displayWidgetFeedback(this.element); 
  }

  render () {
    const source = this.svgSource; 
    const height = this.state.height; 
    const width = this.state.width; 
    const left = this.state.left; 
    const top = this.state.top;
    
    let isContainer = (this.type == "group" || this.type == "labelGroup" || this.type == "canvas"); 
    const isPrimary = this.state.primarySelection && this.state.primarySelection == this.props.shape; 
    const isSecondary = this.state.primarySelection && !isPrimary && this.state.primarySelection.name == this.props.shape.name; 

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
          height={this.state.height + "px"} 
          width={this.state.width + "px"} />
      </div>); 
  }
}
