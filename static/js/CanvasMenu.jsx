// App.jsx
import React from "react";
import ConstraintActions from "./ConstraintActions"; 

class CanvasMenuItem extends React.Component {
  constructor(props) {
  	super(props); 
  	this.menuTrigger = props.menuTrigger;  // Pass this along from parent so we can return the shape/selected menu item combination when the menu closes
  	this.action = props.action; 
    this.undoAction = props.undoAction; 
  	this.property = props.property; 
  }

  render () {
  	// The bind will send the menu trigger (JSON shape object) and selected item (text) back to the canvas to propogate it back to the constraints canvas
	  // let menuProperty = menuTextToProperty[this.text]; 
	  let menuText = this.action.label; 
	  return <li className="canvas-menu-item" onClick={this.props.onClick.bind(this, this.menuTrigger, this.action, this.undoAction)} >{menuText}</li>; 
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
  }

  getAction(constraint, constraintsMenu) {
      // Find the corresponding shape on the cosntraints canvas for the menu trigger shape
      // Use the state of that shape to determine what shows up
      let constraintsCanvasShape = this.menuTrigger.constraintsCanvasShape; 
      if(constraintsCanvasShape[ConstraintActions.locksKey] 
        && constraintsCanvasShape[ConstraintActions.locksKey].indexOf(constraint) >= 0) {
        // The constraint is active and set to true, show the undo option
        return { do: constraintsMenu[constraint]["undo"], undo: constraintsMenu[constraint]["do"] }; 
      } else {
        // Show the do option
        return { do: constraintsMenu[constraint]["do"], undo: constraintsMenu[constraint]["undo"] }; 
      }    
  }

  getMenuItems(menuCollection) {
    let menuItems = []; 
    for(let constraint in menuCollection) {
      if(menuCollection.hasOwnProperty(constraint)) {
        // Check if this property is set on the menu trigger already to 
        // Decide whether to show the do or undo option 
        let action = this.getAction(constraint, menuCollection); 
        menuItems.push(<CanvasMenuItem onClick={this.props.onClick} action={action.do} undoAction={action.undo} menuTrigger={this.menuTrigger} key={constraint} />);
      }
    }

    return menuItems; 
  }

  getRelationalMenuItems() {
    let menuCollection = ConstraintActions.relationalConstraints; 


  }

  render () {
  	let elementItems = this.getMenuItems(ConstraintActions.elementConstraints);
    let groupItems = null; 
    let pageItems = null; 
    if(this.menuTrigger.type == "group") {
      groupItems = this.getMenuItems(ConstraintActions.groupConstraints); 
    }

    if(this.menuTrigger.type == "page") {
      pageItems = this.getMenuItems(ConstraintActions.pageConstraints); 
    }

    if(this.menuTrigger.type == "element" || this.menuTrigger.type == "group") {
      // Relational constraints
      relationalItems = this.getRelationalMenuItems(); 
    }

	  return (
      <div className="canvas-menu">
        <span className="canvas-menu-label">Element</span>
        <ul className="canvas-menu-list">{elementItems}</ul>
        { groupItems ? <span className="canvas-menu-label">Group</span> : null }
        { groupItems ? <ul className="canvas-menu-list">{groupItems}</ul> : null }
        { pageItems ? <span className="canvas-menu-label">Page</span> : null }
        { pageItems ? <ul className="canvas-menu-list">{pageItems}</ul> : null}
      </div>
    );
  }
}


// Menu items
// - Element cl