// App.jsx
import React from "react";
import Resizable from 're-resizable';
import ConstraintActions from './ConstraintActions';
import SVGInline from "react-svg-inline"

const WAIT_INTERVAL = 1000; 

export default class SVGWidget extends React.Component {

  static initialWidths(controlType) {
    let values = {
      'button': 140, 
      'field': 238, 
      'search': 238, 
      'group': 100, 
      'labelGroup': 100, 
      'label': 100
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
      'label': 40
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

  constructor(props) {
  	super(props); 
    this.type = props.shape.type; 
    this.controlType = props.shape.controlType; 
    this.id = props.id; 
    this.element = props.shape; // constraints shape object
    this.svgSource = props.source; 

    // Callback to notify the parent container to re-check the solution validity
    this.checkSolutionValidity =  props.checkSolutionValidity; 
    this.displayFontSizeSelector = props.displayFontSizeSelector; 
    this.hideFontSizeSelector = props.hideFontSizeSelector; 

    // Method bindings
    this.setFontSize = this.setFontSize.bind(this); 
    this.onElementResized = this.onElementResized.bind(this);

    this.state = {
      height: SVGWidget.initialHeights(this.controlType),
      width: SVGWidget.initialWidths(this.controlType)
    }
  }

  componentWillMount() {
    this.timer = null; 
  }

  componentDidMount() {
    // Set the initial value for the text label
    this.setTextLabel(true);   
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

    // let svgViewBox = element.querySelectorAll(".SVGInline-svg"); 
    // svgViewBox[0].removeAttribute("viewBox");

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

      // Adjust the initial translation of the text to center it in the middle (only for buttons)
      let bboxText = editableText[0].getBoundingClientRect();
      let heightLocation = (this.state.height/2);
      if(this.controlType == "button") {
        editableText[0].style.transform = "translate(" + this.state.width/2 + "px," + heightLocation + "px)";  
      }
      else if(this.controlType == "label") {
        editableText[0].style.transform = "translate(0px," + heightLocation + "px)";  
      }  
    }

    // let svgViewBox = svgElement.querySelectorAll(".SVGInline-svg"); 
    // svgViewBox[0].removeAttribute("viewBox");

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

  showFontSizeSelector(evt) {
    evt.stopPropagation();
    evt.preventDefault();

    // Call the parents method to construct the font size selector
    this.displayFontSizeSelector(evt, this.setFontSize);
  }

  setFontSize(value) {
    // Update the font size of the SVG element
    let id = "widget-container-" + this.id; 
    let svgElement  = document.getElementById(id); 

    let svgElementInline = svgElement.querySelectorAll(".SVGInline-svg"); 

    // Unset these so that we can calculate a new size after the font size is changed
    svgElementInline[0].style.width = ""; 
    svgElementInline[0].style.height = ""; 
    svgElementInline[0].style.fontSize = value + "px";

    let editableText = svgElement.querySelectorAll(".widget-editable-text");

    // Update the element object size
    let boundingRect = editableText[0].getBoundingClientRect(); 
    this.setState({
      width: boundingRect.width, 
      height: boundingRect.height
    })

    this.hideFontSizeSelector(); 
  }

  onElementResized(evt, direction, element, delta) {
    // When resizing finishes, update the size of the element
    this.adjustElementSize(element);
  }

  render () {
    const source = this.svgSource; 
    const height = this.state.height; 
    const width = this.state.width; 
    this.setElementSize(width, height); 
    const enableOptions = {
      top:false, right: true, bottom:false, left: false, topRight:false, bottomRight: false, bottomLeft:false, topLeft:false
    };

    let field

    return (
      <Resizable maxWidth={300} minWidth={50} enable={enableOptions} onResizeStop={this.onElementResized}>
        <div onContextMenu={this.showFontSizeSelector.bind(this)} suppressContentEditableWarning="true" onInput={this.handleTextChange.bind(this)} 
            contentEditable="true" id={"widget-container-" + this.id} className="widget-container">
          <SVGInline className={"widget-control-" + this.controlType} svg={source} height={this.state.height + "px"} width={this.state.width + "px"} />
        </div>
      </Resizable>); 
  }














}
