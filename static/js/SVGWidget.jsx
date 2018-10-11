// App.jsx
import React from "react";
import Resizable from 're-resizable';
import ConstraintActions from './ConstraintActions';
import SVGInline from "react-svg-inline"
import Converter from "number-to-words";
import Constants from "./Constants";

const WAIT_INTERVAL = 1000; 

export default class SVGWidget extends React.Component {
  constructor(props) {
  	super(props); 
    this.type = props.shape.type; 
    this.controlType = props.shape.controlType; 
    this.id = props.id; 
    this.element = props.shape; // constraints shape object

    this.initialFontSize = 0; 
    if(this.type == "label") {
      this.initialFontSize = Constants.controlFontSizes(this.controlType);
      this.element.fontSize = this.initialFontSize;  
    }

    // Callback to notify the parent container to re-check the solution validity
    this.checkSolutionValidity =  props.checkSolutionValidity; 
    this.displayRightClickMenu = props.displayRightClickMenu; 
    this.hideRightClickMenu = props.hideRightClickMenu; 
    this.displayLabelIndicator = props.displayLabelIndicator; 
    this.createLabelsGroup = props.createLabelsGroup; 
    this.getCurrentShapeSiblings = props.getCurrentShapeSiblings; 
    this.getCurrentShapeIndex = props.getCurrentShapeIndex;
    this.isContainer = props.isContainer; 

    // Timer for handling text change events
    this.timer = null;  

    this.state = {
      height: this.element.size.height,
      width: this.element.size.width,
      order: (this.element.order ? this.element.order : -1),  
      ordered: this.element.ordered, 
      fontSize: (this.element.fontSize ? this.element.fontSize : this.initialFontSize),
      importance: this.element.importance, 
      showImportance: props.showImportanceLevels,
      showOrder: false,  
      showLabels: this.element.labels ? true : false, 
      labelPosition: {
        x: 0, 
        y: 0
      }, 
      svgSource: props.source, 
      highlighted: props.highlighted, 
      hasText: false
    }; 
  }

  static getDerivedStateFromProps(nextProps, prevState) {
    return {
      height: prevState.height,  
      width: prevState.width, 
      order: prevState.order, 
      ordered: prevState.ordered, 
      fontSize: prevState.fontSize, 
      importance: prevState.importance, 
      showImportance: prevState.showImportance, 
      showLabels: prevState.showLabels, 
      labelPosition: prevState.labelPosition, 
      showOrder: prevState.showOrder,
      svgSource: nextProps.source, 
      highlighted: nextProps.highlighted
    }    
  }
  
  componentDidMount() {
    // Set the initial value for the text label
    this.setTextLabel(true); 
    let hasText = this.getHasText();
    this.setState({
      hasText: hasText, 
      labelPosition: this.computeLabelPosition()
    }); 
  }

  componentDidUpdate() {
    this.setTextLabel(false);
  }

  lockTextLabel = () => {
    if(this.element[ConstraintActions.locksKey] == undefined) {
      this.element[ConstraintActions.locksKey] = []; 
    } 

    if(this.element[ConstraintActions.locksKey].indexOf("label") == -1) {
      this.element[ConstraintActions.locksKey].push("label"); 
    }
  }

  getHasText = () => {
    let id = "widget-container-" + this.id; 
    let svgElement = document.getElementById(id); 
    let editableText = svgElement.querySelectorAll(".widget-editable-text");
    if(editableText[0]) {
      return true;  
    }

    return false;
  }

  handleTextChange = (evt) => {
    // Handle the text change on a timeout so it saves after the user finishes typing
    clearTimeout(this.timer); 
    this.timer = setTimeout(this.updateTextLabel, WAIT_INTERVAL);  
  }

  updateTextLabel = (evt) => {
    let id = "widget-container-" + this.id; 
    let editableText = document.getElementById(id).querySelectorAll(".widget-editable-text");
    let textValue = editableText[0].innerHTML; 
    console.log(textValue);
    this.element.label = textValue;
    this.lockTextLabel()

    // Update the height and widht of the parent container so the height recalculates
    if(this.type == "label") {
      let textBounding = editableText[0].getBoundingClientRect(); 
      let widthRounded = Math.round(textBounding.width); 
      let heightRounded = Math.round(textBounding.height); 
      this.setElementSize(widthRounded, heightRounded);

      // Measure and set the baseline value
      let textSizeMeasure = document.getElementById(id).querySelectorAll(".widget-size-measure"); 
      if(textSizeMeasure[0]){
        let textSizeBounding = textSizeMeasure[0].getBoundingClientRect(); 
        let baseline = textBounding.y - textSizeBounding.y
        this.element.baseline = baseline; 
      }
    }

    this.checkSolutionValidity();
  }

  adjustElementSize = (element) => {
    let boundingRect = element.getBoundingClientRect(); 

    // Set it on the element object
    let widthRounded = Math.round(boundingRect.width); 
    let heightRounded = Math.round(boundingRect.height);

    this.setElementSize(widthRounded, heightRounded);  
  }

  setTextLabel = (initSize) => {
    console.log("update text label");
    let id = "widget-container-" + this.id; 
    let svgElement = document.getElementById(id); 
    let editableText = svgElement.querySelectorAll(".widget-editable-text");
    if(editableText[0]) {
      editableText[0].innerHTML = this.element.label; 

      // Measure and set the baseline value
      let textSizeMeasure = document.getElementById(id).querySelectorAll(".widget-size-measure"); 
      if(textSizeMeasure[0]){
        let textBounding = editableText[0].getBoundingClientRect();
        let textSizeBounding = textSizeMeasure[0].getBoundingClientRect(); 
        let baseline = textBounding.y - textSizeBounding.y
        this.element.baseline = baseline; 
      }  
    }

    if(initSize) {
      if(this.state.width == 0 || this.state.height == 0) {
        // give the component an initial size based on the calculated size of the text box
        let sizeContainer = svgElement.querySelectorAll(".widget-size-container"); 
        if(sizeContainer[0]) {
          this.adjustElementSize(sizeContainer[0]);
        }
      }
    }
  }

  setElementFontSize = (fontSize) => {
    this.element.fontSize = fontSize; 
    this.setState({
      fontSize: fontSize
    }); 
  }

  setElementSize = (width, height) => {
    // When height and width are updated by font size changes, update the element object. 
    this.element.size.height = height; 
    this.element.size.width = width; 
    this.setState({
      width: width, 
      height: height
    });
  }

  setElementTyping = (typed) => {
    this.element.typed = typed; 
  }

  showContextMenu = (evt) => {
    evt.stopPropagation();
    evt.preventDefault();

    if(this.type == "label") {
      this.displayRightClickMenu(evt, this.id, {
        setFontSize: this.setFontSize, 
        setLabel: this.setLabel, 
        setImportanceLevel: this.setImportanceLevel, 
        setOrder: this.setOrder
      }); 
    }
    else if(this.controlType == "group" || this.controlType == "page"){
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
    let svgElement = document.getElementById("widget-container-" + this.id); 
    let svgBox = svgElement.getBoundingClientRect(); 

    return {
      x: (svgBox.width)/2, 
      y: svgBox.height + 25
    }; 
  }

  setFontSize = (value) => {
    return (evt) => {
      evt.stopPropagation(); 

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
      this.setElementFontSize(value);

      let editableText = svgElement.querySelectorAll(".widget-editable-text");
      let boundingRect = editableText[0].getBoundingClientRect(); 

      let roundedWidth = Math.round(boundingRect.width,0); 
      let roundedHeight = Math.round(boundingRect.height,0); 
      this.setElementSize(roundedWidth, roundedHeight);

      this.checkSolutionValidity();
    }
  }

  setImportanceLevel = (level) => {
    return (evt) => {
      evt.stopPropagation(); 

      // Update the object
      this.element.importance = level; 

      // Update the number of stars showing
      this.setState({
        importance: level, 
        showImportance: true
      }); 

      this.hideRightClickMenu();
      this.checkSolutionValidity();
    }
  }

  setLabel = (shapeId) => {
    return (evt) => {
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
  }

  setOrder = (value) => {
    return (evt) => {
      evt.stopPropagation(); 

      this.element.order = value; 
      this.setState({
        order: value, 
        showOrder: (value != -1 && value != undefined)
      });

      this.hideRightClickMenu();
      this.checkSolutionValidity();      
    }
  }

  setContainerOrder = (orderValue) => {
    return (evt) => {
      evt.stopPropagation(); 

      this.element.containerOrder = orderValue; 

      let orderedValue = orderValue == "important"; 
      this.setState({
        ordered: orderedValue
      }); 

      this.hideRightClickMenu();
      this.checkSolutionValidity();
    }
  }

  render () {
    console.log('render SVGWidget'); 
    const source = this.state.svgSource; 
    const height = this.state.height; 
    const width = this.state.width; 
    const importance = this.state.importance; 
    const showImportance = this.state.showImportance; 
    const showLabels = this.state.showLabels; 
    const labelPosition = this.state.labelPosition; 
    const order = this.state.order;
    const ordered = this.state.ordered; 
    const orderOrdinal = Converter.toWordsOrdinal(order+1); 
    const orderLabel = orderOrdinal.charAt(0).toUpperCase() + orderOrdinal.slice(1); 
    const importanceLabel = importance == "most" ? "Emphasized" : (importance == "least" ? "Deemphasized" : ""); 
    const highlighted = this.state.highlighted; 

    const showOrder = this.state.showOrder;  
    const enableOptions = {
      top:false, right: true, bottom:false, left: false, topRight:false, bottomRight: false, bottomLeft:false, topLeft:false
    };

    const isEditable = this.state.hasText;
    const fontSize = (this.type == "label" ? { fontSize: this.state.fontSize } : {}); 
    return (
      <div  
        onContextMenu={this.showContextMenu} 
        suppressContentEditableWarning="true" 
        onInput={this.handleTextChange} 
        id={"widget-container-" + this.id} 
        className={"widget-container " + (highlighted ? "highlighted" : "")}>
        <div className="widget-control-row"> 
          <SVGInline 
            contentEditable={isEditable} 
            style={fontSize} 
            className={"widget-control-" + this.controlType} 
            svg={source} 
            height={this.state.height + "px"} 
            width={this.state.width + "px"} />
            <div 
              className={"widget-control-info " + ((showImportance || showOrder || this.isContainer) ? "" : "hidden")}>
              {this.isContainer ? 
               (<span className={"badge " + (ordered ? "badge-success" : "badge-primary")}>{(ordered ? "Order Important" : "Order Unimportant")}
                </span>) : undefined}
              <span className={"widget-control-order badge badge-success " + (showOrder ? "" : "hidden")}>{orderLabel}</span>
              <span className={"badge " + (importance == "most" ? "badge-success " : "badge-primary ") + (showImportance ? "" : "hidden")}>
                {importanceLabel}
              </span>
            </div>
        </div>
      </div>); 
  }














}
