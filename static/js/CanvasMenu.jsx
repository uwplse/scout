// App.jsx
import React from "react";
import CanvasMenuActions from "./CanvasMenuActions"; 

class CanvasMenuItem extends React.Component {
  constructor(props) {
  	super(props); 
  	this.menuTrigger = props.menuTrigger;  // Pass this along from parent so we can return the shape/selected menu item combination when the menu closes
  	this.action = props.action; 
  	this.property = props.property; 
  }

  render () {
  	// The bind will send the menu trigger (JSON shape object) and selected item (text) back to the canvas to propogate it back to the constraints canvas
	// let menuProperty = menuTextToProperty[this.text]; 
	let menuText = this.action.label; 
	return <li className="canvas-menu-item" onClick={this.props.onClick.bind(this, this.menuTrigger, this.action)} >{menuText}</li>; 
  }
}

export default class CanvasMenu extends React.Component {
  constructor(props) {
  	super(props); 
  	this.menuShown = props.menuShown; 
  	this.menuTrigger = props.menuTrigger; // This is the JSON of the shape that triggered the menu open 
  }

  getAction(constraint, constraintsMenu) {
      // Find the corresponding shape on the cosntraints canvas for the menu trigger shape
      // Use the state of that shape to determine what shows up
      let constraintsCanvasShape = this.menuTrigger.constraintsCanvasShape; 
      if(constraintsCanvasShape[CanvasMenuActions.locksKey] 
        && constraintsCanvasShape[CanvasMenuActions.locksKey].indexOf(constraint) >= 0) {
        // The constraint is active and set to true, show the undo option
        return constraintsMenu[constraint]["undo"]; 
      } else {
        // Show the do option
        return constraintsMenu[constraint]["do"]; 
      }    
  }

  constructMenuOptions() {
  	let menuItems = []; 
  	for(let elementConstraint in CanvasMenuActions.elementConstraints) {
  		if(CanvasMenuActions.elementConstraints.hasOwnProperty(elementConstraint)) {
  			// Check if this property is set on the menu trigger already to 
  			// Decide whether to show the do or undo option 
  			let elementAction = this.getAction(elementConstraint, CanvasMenuActions.elementConstraints); 
	  		menuItems.push(<CanvasMenuItem onClick={this.props.onClick} action={elementAction} menuTrigger={this.menuTrigger} key={elementConstraint} />);
  		}
  	}

    // Group constraints
    if (this.menuTrigger.type == "group") {
      for(let groupConstraint in CanvasMenuActions.groupConstraints) {
        if(CanvasMenuActions.groupConstraints.hasOwnProperty(groupConstraint)) {
          let groupAction = this.getAction(groupConstraint, CanvasMenuActions.groupConstraints); 
          menuItems.push(<CanvasMenuItem onClick={this.props.onClick} action={groupAction} menuTrigger={this.menuTrigger} key={groupConstraint} />);
        }
      }
    }

  	return menuItems; 
  }

  render () {
  	let menuItems = this.constructMenuOptions();
	return <ul className="canvas-menu">{menuItems}</ul>; 
  }
}


// Menu items
// - Element cl