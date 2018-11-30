// App.jsx
import React from "react";
import ConstraintActions from './ConstraintActions';
import SVGInline from "react-svg-inline"
import Converter from "number-to-words";
import Constants from "./Constants";

const WAIT_INTERVAL = 200; 

export default class ConstraintsCanvasSVGWidget extends React.Component {
  constructor(props) {
  	super(props); 
    this.type = props.shape.type; 
    this.id = props.id; 
    this.element = props.shape; // constraints shape object

    // ID for querying element from the DOM
    this.elementId = "widget-container-" + this.id; 

    this.initialFontSize = 0; 
    if(this.type == "text") {
      this.initialFontSize = Constants.controlFontSizes(this.type);
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

    this.setOrder = this.setOrder.bind(this); 
    this.setContainerOrder = this.setContainerOrder.bind(this); 
    this.setLabel = this.setLabel.bind(this); 
    this.setImportanceLevel = this.setImportanceLevel.bind(this); 

    // Timer for handling text change events
    this.timer = null;  

    this.state = {
      height: this.element.size.height,
      width: this.element.size.width,
      order: this.element.order,  
      containerOrder: this.element.containerOrder, 
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
      hasText: false, 
      cursorPos: 0
    }; 
  }

  static getDerivedStateFromProps(nextProps, prevState) {
    return {
      height: prevState.height,  
      width: prevState.width, 
      order: prevState.order, 
      fontSize: prevState.fontSize, 
      importance: prevState.importance, 
      showImportance: prevState.showImportance, 
      showLabels: prevState.showLabels, 
      labelPosition: prevState.labelPosition, 
      showOrder: prevState.showOrder,
      cursorPos: prevState.cursorPos,
      svgSource: nextProps.source, 
      containerOrder: prevState.containerOrder, 
      highlighted: nextProps.highlighted
    }    
  }
  
  componentDidMount() {
    // Set the initial value for the text label
    this.initTextLabel(); 
    this.setState({
      hasText: true, 
      labelPosition: this.computeLabelPosition()
    }); 
  }

  componentDidUpdate() {
    // if(this.state.hasText) {
    //   console.log("compoennt update");
    //   this.setTextLabel(false);      
    // }
  }

  // lockTextLabel = () => {
  //   if(this.element[ConstraintActions.locksKey] == undefined) {
  //     this.element[ConstraintActions.locksKey] = []; 
  //   } 

  //   if(this.element[ConstraintActions.locksKey].indexOf("label") == -1) {
  //     this.element[ConstraintActions.locksKey].push("label"); 
  //   }
  // }

  getHasText = () => {
    let rootElement = document.getElementById(this.elementId); 
    let editableText = rootElement.getElementsByTagName('text');
    if(editableText[0]) {
      return true;  
    }

    return false;
  }

  initTextLabel = () => {
    let rootElement = document.getElementById(this.elementId); 
    let svgElement = rootElement.getElementsByTagName('svg');
    if(svgElement[0]) {
      let textValue = svgElement[0].textContent; 
      if(textValue && textValue.length) {
        this.element.label = textValue; 
      }
    }
  }

  // handleTextChange = (evt) => {
  //   // Handle the text change on a timeout so it saves after the user finishes typing
  //   clearTimeout(this.timer); 
  //   this.timer = setTimeout(this.updateAndResizeText, WAIT_INTERVAL);  
  // }

  // updateAndResizeText = (evt) => {
  //   console.log("resize text area");
  //   // Update the height and widht of the parent container so the height recalculates
  //   if(this.state.hasText) {
  //     let cursor = window.getSelection(); 
  //     let cursorPos = cursor.baseOffset; 
  //     this.setState({
  //       cursorPos: cursorPos
  //     });

  //     let editableText = document.getElementById(this.elementId).querySelectorAll(".widget-editable-text");

  //     let textValue = editableText[0].innerHTML; 
  //     this.element.label = textValue;

  //     if(this.type == "label") {
  //       let textBounding = this.adjustElementSize(editableText[0]);

  //       // Measure and set the baseline value
  //       let textSizeMeasure = document.getElementById(this.elementId).querySelectorAll(".widget-size-measure"); 
  //       if(textSizeMeasure[0]){
  //         let textSizeBounding = textSizeMeasure[0].getBoundingClientRect(); 
  //         let baseline = textBounding.y - textSizeBounding.y
  //         this.element.baseline = baseline; 
  //       }
  //     }
  //   }    
  // }

  updateTextLabel = (evt) => {
    console.log("udpate text label")
    // Get the actual value out of the text area and update
    // it on the object and lock the value
    // trigger the constraints checking
    // this.lockTextLabel();

    // Set the cursor positon back to 0 
    this.setState({
      cursorPos: 0
    });

    this.checkSolutionValidity();
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
      this.element.size.height = heightRounded; 
    }

    this.element.size.width = widthRounded; 
    this.setState({
      width: widthRounded, 
      height: height
    }); 

    return boundingRect; 
  }

  // setTextLabel = (initSize) => {
  //   let svgElement = document.getElementById(this.elementId); 
  //   let editableText = svgElement.querySelectorAll(".widget-editable-text");
  //   if(editableText[0]) {
  //     console.log("set text");
  //     editableText[0].innerHTML = this.element.label; 

  //     let range = document.createRange(); 
  //     var sel = window.getSelection(); 
  //     var textNode = editableText[0].childNodes[0]; 
  //     if(textNode && this.state.cursorPos != 0) {
  //       range.setStart(textNode, this.state.cursorPos);
  //       range.collapse(true);
  //       sel.removeAllRanges(); 
  //       sel.addRange(range);
  //     }

  //     // Measure and set the baseline value
  //     let textSizeMeasure = document.getElementById(this.elementId).querySelectorAll(".widget-size-measure"); 
  //     if(textSizeMeasure[0]){
  //       let textBounding = editableText[0].getBoundingClientRect();
  //       let textSizeBounding = textSizeMeasure[0].getBoundingClientRect(); 
  //       let baseline = textBounding.y - textSizeBounding.y
  //       this.element.baseline = baseline; 
  //     }  
  //   }

  //   if(initSize) {
  //     if(this.state.width == 0 || this.state.height == 0) {
  //       // give the component an initial size based on the calculated size of the text box
  //       let sizeContainer = svgElement.querySelectorAll(".widget-size-container"); 
  //       if(sizeContainer[0]) {
  //         this.adjustElementSize(sizeContainer[0]);
  //       }
  //     }
  //   }
  // }

  setElementTyping = (typed) => {
    this.element.typed = typed; 
  }

  showContextMenu = (evt) => {
    evt.stopPropagation();
    evt.preventDefault();

    if(this.type == "text") {
      this.displayRightClickMenu(evt, this.id, {
        setFontSize: this.setFontSize, 
        setLabel: this.setLabel, 
        setImportanceLevel: this.setImportanceLevel, 
        setOrder: this.setOrder
      }); 
    }
    else if(this.type == "group" || this.type == "page"){
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

  setFontSize = (value) => {
    return (evt) => {
      evt.stopPropagation(); 

      // Update the element object size
      let svgElement  = document.getElementById(this.elementId); 

      let svgElementInline = svgElement.querySelectorAll(".SVGInline-svg"); 

      // Unset these so that we can calculate a new size after the font size is changed
      svgElementInline[0].style.width = ""; 
      svgElementInline[0].style.height = ""; 

      // Needed for computing the final height and width. This will be removed when the element re-renders. 
      svgElementInline[0].setAttribute("font-size", value); 

      // Set on the element object
      this.setElementFontSize(value);

      let editableText = svgElement.querySelectorAll(".widget-editable-text");
      this.adjustElementSize(editableText[0]);

      this.checkSolutionValidity();
    }
  }

  setImportanceLevel(evt, level) {
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
      order: value, 
      showOrder: (value != -1 && value != undefined)
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

    const showOrder = this.state.showOrder;  
    const enableOptions = {
      top:false, right: true, bottom:false, left: false, topRight:false, bottomRight: false, bottomLeft:false, topLeft:false
    };

    const isEditable = this.state.hasText;
    const fontSize = (this.type == "text" ? { fontSize: this.state.fontSize } : {}); 
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
            style={fontSize} 
            className={"widget-control-" + this.type} 
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
