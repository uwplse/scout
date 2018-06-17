// App.jsx
import React from "react";
import ConstraintActions from "./ConstraintActions"; 

class CanvasMenuItem extends React.Component {
  constructor(props) {
  	super(props); 
  	this.menuTrigger = props.menuTrigger;  // Pass this along from parent so we can return the shape/selected menu item combination when the menu closes
  	this.action = props.action; 
    this.actionType = props.actionType;
  	this.property = props.property; 
  }

  render () {
  	// The bind will send the menu trigger (JSON shape object) and selected item (text) back to the canvas to propogate it back to the constraints canvas
	  // let menuProperty = menuTextToProperty[this.text]; 
	  let menuText = this.action[this.actionType].getFeedbackMessage(this.menuTrigger);
	  return (<li>
            <a href="#" tabIndex="-1" onClick={this.props.onClick.bind(this, this.menuTrigger, this.action, this.actionType)}>{menuText}</a>
          </li>); 
  }
}

// TODO: Implementation for relational constraints
// MOve all object update logic to an onClick in the MenuItem class (we have the objects we need to update on the menuTrigger)
// Then make notifyCanvas method to notify the parent canvas of the update
// Then make a notifyPage method to notify the parent container to resolve the constraints
// Make two different types of menu items
// One is relational (updates 2 or more shapes and the constraint canvs shape)
// One is singular (updates only one shape)

export default class CanvasMenu extends React.Component {
  constructor(props) {
  	super(props); 
  	this.menuShown = props.menuShown; 
  	this.menuTrigger = props.menuTrigger; // This is the JSON of the shape that triggered the menu open 
    this.getConstraintsCanvasShape = props.getConstraintsCanvasShape; // Gets the shape on the constraints canvas used to construct the menu options

    this.state = {
      left: props.left, 
      top: props.top
    }
  }

  getAction(constraint, constraintsMenu) {
      // Find the corresponding shape on the cosntraints canvas for the menu trigger shape
      // Use the state of that shape to determine what shows up
      let constraintsCanvasShape = this.getConstraintsCanvasShape(this.menuTrigger.name);
      if(constraintsCanvasShape[ConstraintActions.locksKey]
        && constraintsCanvasShape[ConstraintActions.locksKey].indexOf(constraint) >= 0) {
        // The constraint is active and set to true, show the undo option
        return { type: "undo", action: constraintsMenu[constraint]}; 
      } else {
        // Show the do option
        return { type: "do", action: constraintsMenu[constraint]}; 
      }    
  }

  getMenuItems(menuCollection) {
    let menuItems = []; 
    for(let constraint in menuCollection) {
      if(menuCollection.hasOwnProperty(constraint)) {
        // Check if this property is set on the menu trigger already to 
        // Decide whether to show the do or undo option 
        let action = this.getAction(constraint, menuCollection); 
        menuItems.push(<CanvasMenuItem onClick={this.props.onClick} action={action.action} actionType={action.type} menuTrigger={this.menuTrigger} key={constraint} />);
      }
    }

    return menuItems; 
  }

  getRelationalMenuItems() {
    // These are just hard coded right now, they don't do anything
    let menuItems = []; 
    menuItems.push((<li>
        <a href="#" tabIndex="-1">Keep global alignment.</a>
      </li>)); 
    menuItems.push((<li>
        <a href="#" tabIndex="-1">Keep alignment relative to container.</a>
      </li>)); 
    menuItems.push((<li>
        <a href="#" tabIndex="-1">Keep position relative to container.</a>
      </li>)); 
    menuItems.push((<li>
        <a href="#" tabIndex="-1">Keep position relative to neighbor 1.</a>
      </li>)); 
    menuItems.push((<li>
        <a href="#" tabIndex="-1">Keep position relative to neighbor 2.</a>
      </li>)); 
    return menuItems;
  }

  render () {
  	let elementItems = this.getMenuItems(ConstraintActions.elementConstraints);
    let groupItems = []; 
    let canvasItems = []; 
    let relationalItems = [];

    if(this.menuTrigger.type != "page" && this.menuTrigger.type != "canvas") {
      relationalItems = this.getRelationalMenuItems();
    }

    if(this.menuTrigger.type == "group" || this.menuTrigger.type == "labelGroup" || this.menuTrigger.type == "page") {
      groupItems = this.getMenuItems(ConstraintActions.groupConstraints); 
    }

    if(this.menuTrigger.type == "canvas") {
      canvasItems = this.getMenuItems(ConstraintActions.canvasConstraints); 
    }

    // if(this.menuTrigger.type == "element" || this.menuTrigger.type == "group") {
    //   // Relational constraints
    //   relationalItems = this.getRelationalMenuItems(); 
    // }
    const menuLeft = this.state.left; 
    const menuTop = this.state.top;

	  return (
      <div className="right-click-menu-container dropdown" style={{left: menuLeft + "px", top: menuTop + "px", display: "block"}} >
        <ul className="dropdown-menu" style={{display: "block"}}>
        <li role="separator" className="divider divider-top">Element</li>
        {elementItems}
        {groupItems.length ? 
          (<li role="separator" className="divider">Container</li>) : undefined}
        {groupItems.length ? groupItems : undefined}
        {canvasItems.length ? (
          <li role="separator" className="divider">Global</li>) : undefined}
        {canvasItems.length ? canvasItems : undefined}  
        {relationalItems.length ? (
          <li role="separator" className="divider">Relational</li>) : undefined}
        {relationalItems.length ? relationalItems : undefined}  
        </ul>
      </div>
    );
  }
}


// Menu items
// - Element cl