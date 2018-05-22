// App.jsx
import React from "react";
import FabricHelpers from './FabricHelpers';
import ConstraintActions from './ConstraintActions';

export default class SVGWidget extends React.Component {
  
  static initialWidthValues(type) {
    let values = {
      'button': 120, 
      'text': 120, 
      'field':  120, 
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
    this.imgSource = props.source; 

    // Callback to notify the parent container to re-check the solution validity
    this.checkSolutionValidity =  props.checkSolutionValidity; 
  }

  lockTextLabel(shape) {
    if(shape[ConstraintActions.locksKey] == undefined) {
      shape[ConstraintActions.locksKey] = []; 
    } 

    if(shape[ConstraintActions.locksKey].indexOf("label") == -1) {
      shape[ConstraintActions.locksKey].push("label"); 
    }
  }

  // addLabelGroupToCanvas() {
  //   let groupRect = FabricHelpers.getGroup(0,0, 120, 40, {
  //     stroke: 'red', 
  //     groupType: 'Label', 
  //     strokeDashArray: [5,5]
  //   });

  //   this.canvas.add(groupRect)
  // }

  // addGroupToCanvas() {
  //   let groupRect = FabricHelpers.getGroup(0, 0, 120, 40, {
  //     stroke: '#39a1f4', 
  //     groupType: 'Group', 
  //     strokeDashArray: [5,5]
  //   });

  //   this.canvas.add(groupRect); 
  // }

  render () {
    const source = this.imgSource; 
    return (
      <div className={"widget-container " + this.type}>
        <img src={source} />
      </div>); 
  }














}
