// App.jsx
import React from "react";
import Resizable from 're-resizable';
import ConstraintActions from './ConstraintActions';
import SVGInline from "react-svg-inline"
import Converter from "number-to-words";

const WAIT_INTERVAL = 1000; 

export default class SVGWidget extends React.Component {

  // TODO: Calculate dynamically from the initial size of the SVG? 
  static initialWidths(controlType) {
    let values = {
      'button': 140, 
      'field': 238, 
      'search': 238, 
      'group': 100, 
      'labelGroup': 100, 
      'label': 83, 
      'multilineLabel': 200, 
      'image': 100, 
      'placeholder': 100
    }

    if(controlType in values) {
      return values[controlType]; 
    }

    return 0; 
  }

  static initialHeights(controlType) {
    let values = {
      'button': 34, 
      'field': 25, 
      'search': 25, 
      'group': 40, 
      'labelGroup': 40, 
      'label': 43, 
      'image': 100, 
      'placeholder': 100, 
      'multilineLabel': 80
    }

    if(controlType in values) {
      return values[controlType]; 
    }

    return 0; 
  }


  static initialLabels(controlType) {
    let values = {
      'button': 'Button', 
      'label': 'Label', 
      'field': 'Field', 
      'search': 'Search', 
      'group': 'Group', 
      'labelGroup': 'Label'
    }
    return values[controlType]; 
  }; 

  static initialFontSizes(controlType) {
    let values = {
      'label': 36, 
      'multilineLabel': 14
    }
    return values[controlType];
  }

  constructor(props) {
  	super(props); 
    this.type = props.shape.type; 
    this.controlType = props.shape.controlType; 
    this.id = props.id; 
    this.element = props.shape; // constraints shape object

    this.initialFontSize = 0; 
    if(this.type == "label") {
      this.initialFontSize = SVGWidget.initialFontSizes(this.controlType); 
    }

    // Callback to notify the parent container to re-check the solution validity
    this.checkSolutionValidity =  props.checkSolutionValidity; 
    this.displayRightClickMenu = props.displayRightClickMenu; 
    this.hideRightClickMenu = props.hideRightClickMenu; 
    this.displayLabelIndicator = props.displayLabelIndicator; 

    // Method bindings
    this.setFontSize = this.setFontSize.bind(this); 
    this.initFontSize = this.initFontSize.bind(this);
    this.setImportanceLevel = this.setImportanceLevel.bind(this); 
    this.setLabel = this.setLabel.bind(this);
    this.setOrder = this.setOrder.bind(this);
    this.setContainerOrder = this.setContainerOrder.bind(this);
    this.onElementResized = this.onElementResized.bind(this);
    this.computeLabelPosition = this.computeLabelPosition.bind(this);

    // Timer for handling text change events
    this.timer = null; 

    this.state = {
      height: SVGWidget.initialHeights(this.controlType),
      width: SVGWidget.initialWidths(this.controlType),
      order: -1,  
      fontSize: this.initialFontSize,
      importance: "normal", 
      showImportance: props.showImportanceLevels, 
      showLabels: false, 
      labelDirection: undefined, 
      labelPosition: {
        x: 0, 
        y: 0
      }, 
      showOrder: false, 
      svgSource: props.source, 
      typedGroup: props.typedGroup, 
      orderedGroup: props.orderedGroup
    }
  }

  static getDerivedStateFromProps(nextProps, prevState) {
    return {
      height: prevState.height,  
      width: prevState.width, 
      fontSize: prevState.fontSize, 
      importance: prevState.importance, 
      showImportance: prevState.showImportance, 
      showLabels: prevState.showLabels, 
      labelDirection: prevState.labelDirection, 
      labelPosition: prevState.labelPosition, 
      orderedGroup: prevState.orderedGroup,
      svgSource: nextProps.source, 
      typedGroup: nextProps.typedGroup
    }    
  }
  
  componentDidMount() {
    // Set the initial value for the text label
    this.setTextLabel(true);   

    if(this.type == "label") {
      this.initFontSize();       
    }
  }

  componentDidUpdate() {
    this.setTextLabel(false);
  }

  lockTextLabel() {
    if(this.element[ConstraintActions.locksKey] == undefined) {
      this.element[ConstraintActions.locksKey] = []; 
    } 

    if(this.element[ConstraintActions.locksKey].indexOf("label") == -1) {
      this.element[ConstraintActions.locksKey].push("label"); 
    }
  }

  handleTextChange(evt) {
    // Handle the text change on a timeout so it saves after the user finishes typing
    clearTimeout(this.timer); 
    this.timer = setTimeout(this.updateTextLabel.bind(this), WAIT_INTERVAL);  
  }

  updateTextLabel(evt) {
    console.log("updateTextLabel");
    let id = "widget-container-" + this.id; 
    let editableText = document.getElementById(id).querySelectorAll(".widget-editable-text");
    let textValue = editableText[0].innerHTML; 
    this.element.label = textValue;
    this.lockTextLabel()

    // After setting the text label, update the height and width of the parent container so that the tree size and widget size recalculates
    if(this.controlType == "label") {
      let boundingRect = editableText[0].getBoundingClientRect(); 
      let widthRounded = Math.round(boundingRect.width); 
      let heightRounded = Math.round(boundingRect.height); 

      this.setState({
        width: widthRounded, 
        height: heightRounded
      });
    }

    this.checkSolutionValidity();
  }

  adjustElementSize(element) {
    let boundingRect = element.getBoundingClientRect(); 

    // Set it on the element object
    let widthRounded = Math.round(boundingRect.width); 
    let heightRounded = Math.round(boundingRect.height);

    this.setElementSize(widthRounded, heightRounded);

    this.setState({
      width: widthRounded, 
      height: heightRounded
    });     
  }

  setTextLabel(initSize) {
    let id = "widget-container-" + this.id; 
    let svgElement = document.getElementById(id); 
    let editableText = svgElement.querySelectorAll(".widget-editable-text");
    if(editableText[0]) {
      editableText[0].innerHTML = this.element.label;   
    }

    if(initSize) {
      if(this.state.width == 0 || this.state.height == 0) {
        // give the component an initial size based on the calculated size of the text box
        let sizeContainer = svgElement.querySelectorAll(".widget-size-container"); 
        this.adjustElementSize(sizeContainer[0]);
      }
    }
  }

  setElementSize(width, height) {
    // When height and width are updated by font size changes, update the element object. 
    this.element.size.height = height; 
    this.element.size.width = width; 
  }

  setElementTyping(typed) {
    this.element.typed = typed; 
  }

  showContextMenu(evt) {
    evt.stopPropagation();
    evt.preventDefault();

    if(this.controlType == "label") {
      this.displayRightClickMenu(evt, this.id, {
        setFontSize: this.setFontSize, 
        setLabel: this.setLabel, 
        setImportanceLevel: this.setImportanceLevel, 
        setOrder: this.setOrder
      }); 
    }
    else if(this.controlType == "group"){
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

  initFontSize() {
    // Update the font size of the SVG element
    let id = "widget-container-" + this.id; 
    let svgElement  = document.getElementById(id); 

    let svgElementInline = svgElement.querySelectorAll(".SVGInline-svg"); 

    svgElementInline[0].setAttribute("font-size", this.initialFontSize); 

    // Set it on the element object as well
    this.element.fontSize = this.initialFontSize; 
  }

  setFontSize(value) {
    // Update the element object size
    let id = "widget-container-" + this.id; 
    let svgElement  = document.getElementById(id); 

    let svgElementInline = svgElement.querySelectorAll(".SVGInline-svg"); 

    // Unset these so that we can calculate a new size after the font size is changed
    svgElementInline[0].style.width = ""; 
    svgElementInline[0].style.height = ""; 

    // Needed for computing the final height and width. This will be removed when the element re-renders. 
    svgElementInline[0].setAttribute("font-size", value); 

    // Set on the element object
    this.element.fontSize = value; 

    let editableText = svgElement.querySelectorAll(".widget-editable-text");
    let boundingRect = editableText[0].getBoundingClientRect(); 
    this.setState({
      width: Math.round(boundingRect.width,0), 
      height: Math.round(boundingRect.height,0), 
      fontSize: value
    }); 

    // Close the right click menu
    this.hideRightClickMenu(); 
    this.checkSolutionValidity();
  }

  setImportanceLevel(level) {
    // Update the object
    let importance = level == 1 ? "least" : (level == 2 ? "normal" : "most"); 
    this.element.importance = importance; 

    // Update the number of stars showing
    this.setState({
      importance: importance, 
      showImportance: true
    }); 

    this.hideRightClickMenu();
    this.checkSolutionValidity();
  }

  computeLabelPosition(){
    let svgElement = document.getElementById("widget-container-" + this.id); 
    let svgBox = svgElement.getBoundingClientRect(); 

    return {
      x: (svgBox.width)/2, 
      y: svgBox.height + 25
    }; 
  }

  setLabel(shapeId, direction) {
    // Save the labels relationship to the shape object 
    this.element.labels = shapeId; 

    let labelPosition = this.computeLabelPosition();

    // Notify the constraints canvas that it should set the label decorator arrow
    this.setState({
      showLabels: true, 
      labelDirection: direction, 
      labelPosition: labelPosition
    }); 

    this.hideRightClickMenu();
    this.checkSolutionValidity();
  }

  setTypedGroup(value) {
    if(value) {
      this.setState({
        typedGroup: true
      }); 
    }
  }

  setOrder(index) {
    this.element.order = index; 

    this.setState({
      showOrder: true,
      order: index
    }); 

    this.hideRightClickMenu(); 
    this.checkSolutionValidity();
  }

  setContainerOrder(orderValue) {
    this.element.containerOrder = orderValue; 

    let orderedValue = orderValue == "important"; 
    this.setState({
      orderedGroup: orderedValue
    }); 

    this.hideRightClickMenu(); 
    this.checkSolutionValidity();
  }

  onElementResized(evt, direction, element, delta) {
    // When resizing finishes, update the size of the element
    this.adjustElementSize(element);
  }

  render () {
    const source = this.state.svgSource; 
    const height = this.state.height; 
    const width = this.state.width; 
    const importance = this.state.importance; 
    const showImportance = this.state.showImportance; 
    const showLabels = this.state.showLabels; 
    const labelDirection = this.state.labelDirection; 
    const labelPosition = this.state.labelPosition; 
    const typedGroup = this.state.typedGroup;
    const orderedGroup = this.state.orderedGroup; 
    const order = this.state.order;
    const orderOrdinal = Converter.toWordsOrdinal(order+1); 
    const orderLabel = orderOrdinal.charAt(0).toUpperCase() + orderOrdinal.slice(1); 

    const showOrder = this.state.showOrder;  
    this.setElementSize(width, height); 
    this.setElementTyping(typedGroup);
    const enableOptions = {
      top:false, right: true, bottom:false, left: false, topRight:false, bottomRight: false, bottomLeft:false, topLeft:false
    };

    const isEditable = this.controlType != "group";
    const fontSize = (this.type == "label" ? { fontSize: this.state.fontSize } : {}); 
    return (
      <Resizable maxWidth={300} minWidth={50} enable={enableOptions} onResizeStop={this.onElementResized}>
        <div onContextMenu={this.showContextMenu.bind(this)} suppressContentEditableWarning="true" onInput={this.handleTextChange.bind(this)} 
            contentEditable={isEditable} id={"widget-container-" + this.id} className="widget-container">
          <div className="widget-control-row"> 
            <SVGInline style={fontSize} className={"widget-control-" + this.controlType} svg={source} height={this.state.height + "px"} width={this.state.width + "px"} />
            <div className={"widget-control-labels " + (showLabels ? " " : "hidden ") + (labelDirection == "below" ? "widget-control-arrow-down" : "widget-control-arrow-up")}
                style={{top: labelPosition.y + "px", left: labelPosition.x + "px"}}>
            </div>
            <div className="widget-control-info">
              <div className="widget-control-info-left">
              {this.controlType == "group" ? 
               (<span className={"label " + (typedGroup ? "label-success" : "label-info")}>{typedGroup ? "Typed" : "Untyped"}</span>) : undefined}
              {this.controlType == "group" ? 
               (<span className={"label " + (orderedGroup ? "label-success" : "label-info")}>{orderedGroup ? "Ordered" : "Unordered"}</span>) : undefined}
              </div>
              <div className="widget-control-info-right">
                <span className={"widget-control-order label label-info " + (showOrder ? "" : "hidden")}>{orderLabel}</span>
                <div className={"widget-control-importance " + (showImportance ? "" : "hidden")}> 
                  <span className="glyphicon glyphicon-star" aria-hidden="true"></span>
                  <span className={"glyphicon " + (importance == "least" ? "glyphicon-star-empty" : "glyphicon-star")} aria-hidden="true"></span>
                  <span className={"glyphicon " + (importance == "least" || importance == "normal" ? "glyphicon-star-empty" : "glyphicon-star")}></span>
                </div>
              </div>
            </div>
          </div>
        </div>
      </Resizable>); 
  }














}
