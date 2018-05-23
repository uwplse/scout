// App.jsx
import React from "react";
import ConstraintActions from './ConstraintActions';
import SVGInline from "react-svg-inline"

const WAIT_INTERVAL = 1000; 

export default class SVGWidget extends React.Component {

  static initialWidthValues(type) {
    let values = {
      'button': 165, 
      'label': 75, 
      'field':  250, 
      'group': 120, 
      'labelGroup': 120
    }; 
    return values[type]; 
  }; 

  static initialHeightValues(type) {
    let values =  {
      'button': 40, 
      'label': 30, 
      'field': 25, 
      'group': 40,
      'labelGroup': 40
    };
    return values[type];
  }; 

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

    this.state = {
      height: props.height, 
      width: props.width
    }
  }

  componentWillMount() {
    this.timer = null; 
  }

  componentDidMount() {
    // Set the initial value for the text label
    this.setTextLabel();
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
    let id = "widget-container-" + this.id; 
    let editableText = document.getElementById(id).querySelectorAll(".widget-editable-text");
    let textValue = editableText[0].innerHTML; 
    this.element.label = textValue;
    this.lockTextLabel()
    this.checkSolutionValidity();
  }

  setTextLabel() {
    let id = "widget-container-" + this.id; 
    let editableText = document.getElementById(id).querySelectorAll(".widget-editable-text");
    if(editableText[0]) {
      editableText[0].innerHTML = this.element.label;       
    }
  }

  setElementSize(height, width) {
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

    let editableText = svgElement.querySelectorAll(".widget-editable-text");
    editableText[0].style.fontSize = value + "px"; 


    // Update the element object size
    let boundingRect = editableText[0].getBoundingClientRect(); 
    this.setState({
      width: boundingRect.width, 
      height: boundingRect.height
    })

    this.hideFontSizeSelector(); 
  }

  render () {
    const source = this.svgSource; 
    const height = this.state.height; 
    const width = this.state.width; 
    this.setElementSize(height, width); 

    return (
      <div onContextMenu={this.showFontSizeSelector.bind(this)} suppressContentEditableWarning="true" onInput={this.handleTextChange.bind(this)} 
          contentEditable="true" id={"widget-container-" + this.id} className="widget-container">
        <SVGInline svg={source} height={this.state.height + "px"} width={this.state.width + "px"} />
      </div>); 
  }














}
