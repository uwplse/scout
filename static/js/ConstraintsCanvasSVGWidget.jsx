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

    // ID for querying element from the DOM
    this.elementId = "widget-container-" + this.id; 

    // Callback to notify the parent container to re-check the solution validity
    this.checkSolutionValidity =  props.checkSolutionValidity; 
    this.displayRightClickMenu = props.displayRightClickMenu; 
    this.hideRightClickMenu = props.hideRightClickMenu; 
    this.displayLabelIndicator = props.displayLabelIndicator; 
    this.createLabelsGroup = props.createLabelsGroup; 
    this.getCurrentShapeSiblings = props.getCurrentShapeSiblings; 
    this.getCurrentShapeIndex = props.getCurrentShapeIndex;
    this.isContainer = props.isContainer; 

    this.setOrder = this.setOrder.bind(this); 
    this.setContainerOrder = this.setContainerOrder.bind(this); 
    this.setLabel = this.setLabel.bind(this); 
    this.setImportanceLevel = this.setImportanceLevel.bind(this); 

    // Timer for handling text change events
    this.timer = null;  

    this.state = {
      height: this.element.height,
      width: this.element.width,
      order: this.element.order,  
      containerOrder: this.element.containerOrder, 
      importance: this.element.importance, 
      showLabels: this.element.labels ? true : false, 
      labelPosition: {
        x: 0, 
        y: 0
      }, 
      svgSource: props.source, 
      highlighted: props.highlighted, 
      hasText: false, 
      cursorPos: 0
    }; 
  }

  static getDerivedStateFromProps(nextProps, prevState) {
    return {
      height: prevState.height,  
      width: prevState.width, 
      order: prevState.order, 
      importance: prevState.importance, 
      showLabels: prevState.showLabels, 
      labelPosition: prevState.labelPosition, 
      cursorPos: prevState.cursorPos,
      svgSource: nextProps.source, 
      containerOrder: prevState.containerOrder, 
      highlighted: nextProps.highlighted
    }    
  }
  
  componentDidMount() {
    // Set the initial value for the text label
    this.setState({
      hasText: true, 
      labelPosition: this.computeLabelPosition()
    }); 
  }

  getHasText = () => {
    let rootElement = document.getElementById(this.elementId); 
    let editableText = rootElement.getElementsByTagName('text');
    if(editableText[0]) {
      return true;  
    }

    return false;
  }

  adjustElementSize = (element, includeHeight=false) => {
    let boundingRect = element.getBoundingClientRect(); 

    // Set it on the element object
    let widthRounded = Math.round(boundingRect.width); 
    let heightRounded = Math.round(boundingRect.height);

    // When height and width are updated by font size changes, update the element object. 
    let height = this.state.height; 
    if(includeHeight) {
      height = heightRounded; 
      this.element.height = heightRounded; 
    }

    this.element.width = widthRounded; 
    this.setState({
      width: widthRounded, 
      height: height
    }); 

    return boundingRect; 
  }


  setElementTyping = (typed) => {
    this.element.typed = typed; 
  }

  showContextMenu = (evt) => {
    evt.stopPropagation();
    evt.preventDefault();

    if(this.type == "text") {
      this.displayRightClickMenu(evt, this.id, {
        setLabel: this.setLabel, 
        setImportanceLevel: this.setImportanceLevel, 
        setOrder: this.setOrder
      }); 
    }
    else if(this.type == "group" || this.type == "canvas"){
      this.displayRightClickMenu(evt, this.id, {
        setImportanceLevel: this.setImportanceLevel, 
        setOrder: this.setOrder,
        setContainerOrder: this.setContainerOrder
      });     
    }
    else {
      this.displayRightClickMenu(evt, this.id, {
        setImportanceLevel: this.setImportanceLevel, 
        setOrder: this.setOrder
      }); 
    }
  }

  computeLabelPosition = () => {
    let svgElement = document.getElementById(this.elementId); 
    let svgBox = svgElement.getBoundingClientRect(); 

    return {
      x: (svgBox.width)/2, 
      y: svgBox.height + 25
    }; 
  }

  setImportanceLevel(evt, level) {
    evt.stopPropagation(); 

    // Update the object
    this.element.importance = level; 

    // Update the number of stars showing
    this.setState({
      importance: level, 
    }); 

    this.hideRightClickMenu();
    this.checkSolutionValidity();
  }

  setLabel(evt, shapeId) {
    evt.stopPropagation(); 

    // Save the labels relationship to the shape object 
    this.element.labels = shapeId; 
    this.setState({
      showLabels: true 
    }); 

    this.createLabelsGroup(this.id, shapeId); 
    this.hideRightClickMenu();
    this.checkSolutionValidity();
  }

  setOrder(evt, value) {
    evt.stopPropagation(); 

    this.element.order = value; 
    this.setState({
      order: value
    });

    this.hideRightClickMenu();
    this.checkSolutionValidity();      
  }

  setContainerOrder(evt, orderValue) {
    evt.stopPropagation(); 

    this.element.containerOrder = orderValue; 
    this.element.test = "test"; 
    this.setState({
      containerOrder: orderValue
    }); 

    this.hideRightClickMenu();
    this.checkSolutionValidity();
  }

  render () {
    const source = this.state.svgSource; 
    const height = this.state.height; 
    const width = this.state.width; 
    const importance = this.state.importance; 
    const showImportance = this.state.showImportance; 
    const showLabels = this.state.showLabels; 
    const labelPosition = this.state.labelPosition; 
    const order = this.state.order;
    const ordered = this.state.containerOrder == "important"; 

    // const orderOrdinal = Converter.toWordsOrdinal(order+1); 
    // const orderLabel = orderOrdinal.charAt(0).toUpperCase() + orderOrdinal.slice(1);
    const orderLabel = order == 0 ? "First" : "Last"; 

    const importanceLabel = importance == "most" ? "Emphasized" : (importance == "least" ? "Deemphasized" : ""); 
    const highlighted = this.state.highlighted; 

    const showOrder = this.state.order != -1 && this.state.order != undefined;  
    const enableOptions = {
      top:false, right: true, bottom:false, left: false, topRight:false, bottomRight: false, bottomLeft:false, topLeft:false
    };

    const isEditable = this.state.hasText;
    // const fontSize = (this.type == "text" ? { fontSize: this.state.fontSize } : {}); 
    return (
      <div  
        onContextMenu={this.showContextMenu} 
        suppressContentEditableWarning="true" 
        // onInput={this.updateAndResizeText}
        onBlur={this.updateTextLabel} 
        id={this.elementId} 
        className={"widget-container " + (highlighted ? "highlighted" : "")}>
        <div className="widget-control-row"> 
          <SVGInline 
            //contentEditable={isEditable} 
            className={"widget-control-" + this.type} 
            svg={source} 
            height={this.state.height + "px"} 
            width={this.state.width + "px"} />
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
        </div>
      </div>); 
  }














}
