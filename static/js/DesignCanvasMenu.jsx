// App.jsx
import React from "react";
import ConstraintActions from "./ConstraintActions"; 

class DesignCanvasMenuItem extends React.Component {
  constructor(props) {
  	super(props); 
  	this.menuTrigger = props.menuTrigger;  // Pass this along from parent so we can return the shape/selected menu item combination when the menu closes
  	this.action = props.action; 
    this.actionType = props.actionType;
  	this.property = props.property; 
  }

  render () {
  	// The bind will send the menu trigger (JSON shape object) and selected item (text) back to the canvas to propogate it back to the constraints canvas
	  let menuText = this.action[this.actionType].getFeedbackMessage(this.menuTrigger);
	  return (<li>
            <a
              href="#" 
              tabIndex="-1" 
              onClick={this.props.onClick(this.menuTrigger, this.action, this.actionType)}>
                {menuText}
            </a>
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

export default class DesignCanvasMenu extends React.Component {
  constructor(props) {
  	super(props); 
    this.getConstraintsCanvasShape = props.getConstraintsCanvasShape; // Gets the shape on the constraints canvas used to construct the menu options

    this.state = {
      left: props.left, 
      top: props.top, 
      menuTrigger: props.menuTrigger // This is the JSON of the shape that triggered the menu open
    }
  }

  componentDidUpdate() {
    console.log("component updated"); 
    console.log(this.state.menuTrigger.type); 
  }

  static getDerivedStateFromProps(nextProps, prevState) {
    return {
      left: nextProps.left, 
      top: nextProps.top, 
      menuTrigger: nextProps.menuTrigger
    };     
  }

  getAction(constraint, constraintsMenu) {
      // Find the corresponding shape on the cosntraints canvas for the menu trigger shape
      // Use the state of that shape to determine what shows up
      let constraintsCanvasShape = this.getConstraintsCanvasShape(this.state.menuTrigger.name);
      if(constraintsCanvasShape[ConstraintActions.locksKey]
        && constraintsCanvasShape[ConstraintActions.locksKey].indexOf(constraint) >= 0) {
        if(constraintsCanvasShape[constraint] == this.state.menuTrigger[constraint]) {
          // The constraint is active and set to true, show the undo option
          return { type: "undo", action: constraintsMenu[constraint]};           
        }
        else {
          return { type: "do", action: constraintsMenu[constraint]};  
        }
      } else {
        // Show the do option
        return { type: "do", action: constraintsMenu[constraint]}; 
      }    
  }

  getRelationalMenuItems() {
    // These are just hard coded right now, they don't do anything
    let menuItems = []; 
    // menuItems.push((<li>
    //     <a href="#" tabIndex="-1">Keep global alignment.</a>
    //   </li>)); 
    // menuItems.push((<li>
    //     <a href="#" tabIndex="-1">Keep alignment relative to container.</a>
    //   </li>)); 
    // menuItems.push((<li>
    //     <a href="#" tabIndex="-1">Keep position relative to container.</a>
    //   </li>)); 
    menuItems.push((<li>
        <a href="#" tabIndex="-1">Keep position relative to neighbor 1.</a>
      </li>)); 
    menuItems.push((<li>
        <a href="#" tabIndex="-1">Keep position relative to neighbor 2.</a>
      </li>)); 

    // Appear below/adjacent to the neighbor element
    // Appear above/adjacent to the neighbor element

    return menuItems;
  }

  render () {
    console.log("render");
    console.log(this.state.menuTrigger.name);
    const isContainer = this.state.menuTrigger.type == "group" || this.state.menuTrigger.type == "labelGroup" || this.state.menuTrigger.type == "page"; 
    const menuLeft = this.state.left; 
    const menuTop = this.state.top;
    const relational = this.getRelationalMenuItems();
	  return (
      <div className="right-click-menu-container dropdown" style={{left: menuLeft + "px", top: menuTop + "px", display: "block"}} >
        <ul className="dropdown-menu" style={{display: "block"}}>
        {this.state.menuTrigger.type != "canvas" ? 
          (<li role="separator" className="divider divider-top">Element</li>) : undefined}
        {this.state.menuTrigger.type != "canvas" ? 
            Object.keys(ConstraintActions.elementConstraints).map((key) => {
              let action = this.getAction(key, ConstraintActions.elementConstraints);
              let menuItemKey = this.state.menuTrigger.name + "_" + key; 
              return (<DesignCanvasMenuItem onClick={this.props.onClick} 
                        action={action.action} 
                        actionType={action.type} 
                        menuTrigger={this.state.menuTrigger} 
                        key={menuItemKey} />);
            }) : undefined}

        {isContainer ? 
          (<li role="separator" className="divider divider-top">Container</li>) : undefined}
        {isContainer ? 
            Object.keys(ConstraintActions.groupConstraints).map((key) => {
              let action = this.getAction(key, ConstraintActions.groupConstraints);
              return (<DesignCanvasMenuItem onClick={this.props.onClick} 
                        action={action.action} 
                        actionType={action.type} 
                        menuTrigger={this.state.menuTrigger} 
                        key={key} />);
            }) : undefined}
        {this.state.menuTrigger.type != "canvas" ? 
          (<li role="separator" className="divider divider-top">Relational</li>) : undefined}
        {this.state.menuTrigger.type != "canvas" ? relational : undefined} 
        {this.state.menuTrigger.type == "canvas" ? 
          (<li role="separator" className="divider divider-top">Canvas</li>) : undefined}
        {this.state.menuTrigger.type == "canvas" ? 
            Object.keys(ConstraintActions.canvasConstraints).map((key) => {
              let action = this.getAction(key, ConstraintActions.canvasConstraints);
              return (<DesignCanvasMenuItem onClick={this.props.onClick} 
                        action={action.action} 
                        actionType={action.type} 
                        menuTrigger={this.state.menuTrigger} 
                        key={key} />);
            }) : undefined}  
        </ul>
      </div>
    );
  }
}