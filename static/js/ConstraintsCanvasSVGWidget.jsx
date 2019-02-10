// App.jsx
import React from "react";
import ConstraintActions from './ConstraintActions';
import SVGInline from "react-svg-inline"
import Converter from "number-to-words";

const WAIT_INTERVAL = 200; 

export default class ConstraintsCanvasSVGWidget extends React.Component {
  constructor(props) {
  	super(props); 
    this.type = props.shape.type; 
    this.id = props.id; 
    this.element = props.shape; // constraints shape object
    this.alternate = props.shape.alternate; 

    // ID for querying element from the DOM
    this.elementId = "widget-container-" + this.id; 

    // Callback to notify the parent container to re-check the solution validity
    this.displayRightClickMenu = props.displayRightClickMenu; 
    this.displayWidgetFeedback = props.displayWidgetFeedback; 
    this.checkSolutionValidity = props.checkSolutionValidit; 
    this.hideRightClickMenu = props.hideRightClickMenu; 
    this.getCurrentShapeSiblings = props.getCurrentShapeSiblings; 
    this.getCurrentShapeIndex = props.getCurrentShapeIndex;
    this.getCurrentParentNode = props.getCurrentParentNode; 
    this.isContainer = props.isContainer; 

    // Timer for handling text change events
    this.timer = null;  

    this.feedbackCallbacks = this.getFeedbackCallbacks(); 

    this.state = {
      height: this.element.orig_height,
      width: this.element.orig_width,
      order: this.element.order,  
      containerOrder: this.element.containerOrder, 
      importance: this.element.importance, 
      showLabels: this.element.labels ? true : false, 
      svgSource: props.source, 
      highlighted: props.highlighted, 
      cursorPos: 0, 
      hovered: false
    }; 
  }

  static getDerivedStateFromProps(nextProps, prevState) {
    return {
      height: prevState.height,  
      width: prevState.width, 
      order: prevState.order, 
      importance: prevState.importance, 
      showLabels: prevState.showLabels, 
      cursorPos: prevState.cursorPos,
      svgSource: nextProps.source, 
      containerOrder: prevState.containerOrder, 
      highlighted: nextProps.highlighted, 
      hovered: prevState.hovered
    }    
  }

  componentDidUpdate = (prevProps) => {
    if(prevProps.activeDesignShape != this.props.activeDesignShape && 
      this.props.activeDesignShape != undefined) {
      // Display the widget with the proper callbacks
      // Use the true flag to indicate to the PageContainer that 
      // the widget has been selected from a DesignCanvas
      this.displayWidgetFeedback(this.props.activeDesignShape, this.feedbackCallbacks, this.props.activeCanvasShape); 
    }
    else if(prevProps.activeCanvasShape != this.props.activeCanvasShape && 
      this.props.activeCanvasShape != undefined) {
      // Display the widget with the proper callbacks
      this.displayWidgetFeedback(this.props.activeCanvasShape, this.feedbackCallbacks);    
    }
  }

  getFeedbackCallbacks = () => {
    let feedbackCallbacks = {}; 
    if(this.type == "group") {
      if(!this.alternate) {
        feedbackCallbacks.setContainerOrder = this.setContainerOrder;  
      }
      
      feedbackCallbacks.setOrder = this.setOrder; 
      feedbackCallbacks.setImportanceLevel = this.setImportanceLevel; 
      feedbackCallbacks.getCurrentShapeIndex = this.getCurrentShapeIndex; 
      feedbackCallbacks.getCurrentShapeSiblings = this.getCurrentShapeSiblings; 
      feedbackCallbacks.getCurrentParentNode = this.getCurrentParentNode; 
    }
    else if(this.type == "canvas") {
      feedbackCallbacks.setContainerOrder = this.setContainerOrder
    }
    else {
      feedbackCallbacks.setOrder = this.setOrder; 
      feedbackCallbacks.getCurrentShapeIndex = this.getCurrentShapeIndex; 
      feedbackCallbacks.getCurrentShapeSiblings = this.getCurrentShapeSiblings;
      feedbackCallbacks.getCurrentParentNode = this.getCurrentParentNode; 
      feedbackCallbacks.setImportanceLevel = this.setImportanceLevel; 
    }

    return feedbackCallbacks; 
  }

  setImportanceLevel = (level) => {
    // Update the object
    this.element.importance = level; 

    this.setState({
      importance: level
    }, this.props.update);
  }

  setOrder = (value) => {
    this.element.order = value; 

    this.setState({
      order: value
    }, this.props.update); 
  }

  setContainerOrder = (orderValue) => {
    this.element.containerOrder = orderValue; 

    this.setState({
      containerOrder: orderValue
    }, this.props.update); 
  }

  showContextMenu = (evt) => {
    evt.stopPropagation();
    evt.preventDefault();

    this.displayRightClickMenu(evt, this.id); 
  }

  onMouseOver = () => {
    if(this.type != "canvas") {
      this.setState({
        hovered: true
      });
    }
  }

  onMouseOut = () => {
    if(this.type != "canvas") {
      this.setState({
        hovered: false
      }); 
    }
  }

  render () {
    const source = this.state.svgSource; 
    const height = this.state.height; 
    const width = this.state.width; 
    const importance = this.state.importance; 
    const showImportance = this.state.showImportance; 
    const showLabels = this.state.showLabels; 
    const order = this.state.order;
    const ordered = this.state.containerOrder == "important"; 
    const orderLabel = order == 0 ? "First" : "Last"; 
    const importanceLabel = importance == "high" ? "Emphasized" : (importance == "low" ? "Deemphasized" : ""); 
    const highlighted = this.state.highlighted; 
    const showOrder = this.state.order != -1 && this.state.order != undefined;  
    return (
      <div  
        onContextMenu={this.showContextMenu} 
        onClick={this.onClick}
        onMouseOver={this.onMouseOver}
        onMouseOut={this.onMouseOut}
        id={this.elementId} 
        className={"widget-container " + (highlighted ? "highlighted" : "")}>
        <div className="widget-control-row"> 
           <div>
           {source ? (<SVGInline 
              className={"widget-control-" + this.type} 
              svg={source} 
              height={this.state.height + "px"} 
              width={this.state.width + "px"} />) : undefined}
            <span 
              className="widget-control-remove-icon glyphicon glyphicon-remove"
              style={{visibility: (this.state.hovered ? "" : "hidden")}}
              onClick={this.props.removeWidgetNode.bind(this, this.props.id)}></span>
           </div>
            <div 
              className={"widget-control-info " + ((importanceLabel.length || showOrder || this.isContainer) ? "" : "hidden")}>
              {this.isContainer ? 
               (<span className={"badge " + (ordered ? "badge-success" : "badge-primary")}>{(ordered ? "Order Important" : "Order Unimportant")}
                </span>) : undefined}
              <span className={"widget-control-order badge badge-success " + (showOrder ? "" : "hidden")}>{orderLabel}</span>
              <span className={"badge " + (importance == "most" ? "badge-success " : "badge-primary ") + (importanceLabel.length ? "" : "hidden")}>
                {importanceLabel}
              </span>
            </div>
            {this.props.feedbackItems}
        </div>
      </div>); 
  }














}
