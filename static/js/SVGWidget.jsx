// App.jsx
import React from "react";
import ConstraintActions from './ConstraintActions';
import SVGInline from "react-svg-inline"

const WAIT_INTERVAL = 1000; 

export default class SVGWidget extends React.Component {

  static initialWidthValues(type) {
    let values = {
      'button': 165, 
      'text': 75, 
      'field':  250, 
      'group': 120, 
      'labelGroup': 120
    }; 
    return values[type]; 
  }; 

  static initialHeightValues(type) {
    let values =  {
      'button': 40, 
      'text': 30, 
      'field': 25, 
      'group': 40,
      'labelGroup': 40
    };
    return values[type];
  }; 

  constructor(props) {
  	super(props); 
    this.type = props.type; 
    this.id = props.id; 
    this.element = props.shape; // constraints shape object
    this.svgSource = props.source; 
    this.height = props.height; 
    this.width = props.width; 

    // Callback to notify the parent container to re-check the solution validity
    this.checkSolutionValidity =  props.checkSolutionValidity; 
  }

  componentWillMount() {
    this.timer = null; 
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
    console.log("handleTextChange"); 
    clearTimeout(this.timer); 
    this.timer = setTimeout(this.updateTextLabel.bind(this), WAIT_INTERVAL);  
  }

  updateTextLabel(evt) {
    console.log("udpating the text label"); 
    // this.element.label = 
    let id = "widget-container-" + this.id; 
    let editableText = document.getElementById(id).querySelectorAll("#widget-editable-text");
    let textValue = editableText[0].innerHTML; 
    this.element.label = textValue;
    this.lockTextLabel()
    this.checkSolutionValidity();
  }

  render () {
    const source = this.svgSource; 
    return (
      <div suppressContentEditableWarning="true" onInput={this.handleTextChange.bind(this)} 
          contentEditable="true" id={"widget-container-" + this.id} className="widget-container">
        <SVGInline svg={source} height={this.height + "px"} width={this.width + "px"} />
      </div>); 
  }














}
