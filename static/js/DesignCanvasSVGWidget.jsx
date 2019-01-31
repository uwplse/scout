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
    this.showWidgetFeedback = props.showWidgetFeedback; 
    this.timer = null;

    this.uniqueID = _.uniqueId();

    this.state = {
      height: props.height,
      width: props.width, 
      left: props.left, 
      top: props.top, 
      hovered: false, 
      fontSize: this.element.fontSize,
      scaling: props.scaling
    }
  }

  static getDerivedStateFromProps(nextProps, prevState) {
    return {
      height: prevState.height,
      width: prevState.width, 
      left: prevState.left, 
      top: prevState.top, 
      hovered: prevState.hovered, 
      fontSize: prevState.fontSize, 
      scaling: nextProps.scaling
    }
  }

  setElementSize = (width, height) => {
    // When height and width are updated by font size changes, update the element object. 
    this.element.height = height; 
    this.element.width = width; 
  }

  setHovered = (evt) => {
    this.setState({
      hovered: true
    }); 
  }

  hideHovered = (evt) => {
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
    
    // this.setTextLabel();
    // this.rescaleTextLabel();
    let isContainer = (this.type == "group" || this.type == "labelGroup" || this.type == "canvas"); 
    return (
      <div 
        id={"design-canvas-widget-" + this.id + "-" + this.uniqueID} 
        onClick={this.showWidgetFeedback.bind(this, this.element.name)}
        className={"widget-control-"  + (isContainer ? "container" : "leaf")+ (this.state.hovered ? " design-canvas-hovered" : "")}
        onMouseEnter={this.setHovered}
        onMouseLeave={this.hideHovered}
        style={{position: "absolute", left: left + "px", top: top + "px"}}>
        <SVGInline 
          style={fontSize} 
          className={"widget-control-" + this.type} 
          svg={source} 
          height={this.state.height + "px"} 
          width={this.state.width + "px"} />
      </div>); 
  }
}
