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
      height: props.shape.orig_height,
      width: props.shape.orig_width,
      order: props.shape.order,  
      element: props.shape, 
      containerOrder: props.shape.containerOrder, 
      importance: props.shape.importance, 
      showLabels: props.shape.labels ? true : false, 
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
      order: nextProps.shape.order, 
      element: nextProps.shape, 
      importance: nextProps.shape.importance, 
      showLabels: prevState.showLabels, 
      cursorPos: prevState.cursorPos,
      svgSource: nextProps.source, 
      containerOrder: nextProps.shape.containerOrder, 
      highlighted: nextProps.highlighted, 
      hovered: prevState.hovered
    }    
  }

  componentDidMount() {
    if(this.props.primarySelection) {
      this.updatePrimarySelection();
    }
  }

  componentDidUpdate = (prevProps) => {
    if(this.props.primarySelection) {
      if(this.props.primarySelection != prevProps.primarySelection) {
        this.updatePrimarySelection(); 
      }
    }
  }

  updatePrimarySelection = () => {
    if(this.props.primarySelection == this.props.shape) {
      // The shape associated with this node is currently the primary selection
      this.displayWidgetFeedback(this.props.primarySelection, this.feedbackCallbacks); 
    }
    else if(this.props.primarySelection.name == this.props.shape.name) {
      // The shape associated with this node is associated with the shape that is the primary selection
      // It is active from the DesignCanvas node
      // so set this node to be the secondary selection. 
      this.displayWidgetFeedback(this.props.primarySelection, this.feedbackCallbacks, this.props.shape); 
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

  setImportanceLevel = (level, linkedSiblings=[]) => {
    // Update the object
    this.state.element.importance = level; 

    // Update importance on linked siblings (Item Groups)
    for(let i=0; i<linkedSiblings.length; i++){
      let linkedSibling = linkedSiblings[i]; 
      linkedSibling.importance = level; 
    }

    this.setState({
      importance: level
    }, this.props.update);
  }

  setOrder = (value) => {
    this.state.element.order = value; 

    this.setState({
      order: value
    }, this.props.update); 
  }

  setContainerOrder = (orderValue, linkedSiblings=[]) => {
    this.state.element.containerOrder = orderValue; 

    // Update importance on linked siblings (Item Groups)
    for(let i=0; i<linkedSiblings.length; i++){
      let linkedSibling = linkedSiblings[i]; 
      linkedSibling.containerOrder = orderValue; 
    }

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

  onClickRemoveNodes = (evt) => {
    evt.stopPropagation();
    this.props.removeTreeNodes();
  }

  onClickClearFeedback = (evt) => {
    evt.stopPropagation();
    this.props.clearFeedback();
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
    const isCanvas = this.props.shape.type == "canvas";

    const isPrimary = this.props.primarySelection && this.props.primarySelection == this.props.shape; 
    const isSecondary = this.props.primarySelection && !isPrimary && this.props.primarySelection.name == this.props.shape.name; 
    return (
      <div  
        onContextMenu={this.showContextMenu} 
        onClick={this.onClick}
        onMouseOver={this.onMouseOver}
        onMouseOut={this.onMouseOut}
        id={this.elementId} 
        className={"widget-container " 
        + (highlighted ? "highlighted " : " ")
        + (isPrimary ? "primary-selection " : " ")
        + (isSecondary ? "secondary-selection" : "")}>
        <div className="widget-control-row"> 
           <div>
           {source ? (<SVGInline 
              className={"widget-control"} 
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
            {(isCanvas ? (<div 
              className="widget-control-remove-items"> 
                <div>
                  {/*<button 
                    type="button" 
                    className="btn btn-default canvas-node-action" 
                    disabled={!this.props.hasTreeNodes}
                    onClick={this.onClickRemoveNodes}>
                  Remove all nodes</button>*/}
                  <button 
                    type="button" 
                    className="btn btn-default canvas-node-action" 
                    disabled={!this.props.hasFeedback}
                    onClick={this.onClickClearFeedback}>Remove all feedback</button>
                </div>
                <hr className="feedback-container-separator" /> 
            </div>) : undefined)}
            {this.props.feedbackItems}
        </div>
      </div>); 
  }














}
