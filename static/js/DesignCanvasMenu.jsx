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
	  let menuText = this.action[this.actionType].getFeedbackMessage(this.property, this.menuTrigger);
	  return (<li>
            <a
              href="#" 
              tabIndex="-1" 
              onClick={this.props.onClick(this.menuTrigger, this.action, this.actionType, this.property)}>
                {menuText}
            </a>
          </li>); 
  }
}

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

  getKeepAction(constraint, constraintsMenu) {
      // Find the corresponding shape on the cosntraints canvas for the menu trigger shape
      // Use the state of that shape to determine what shows up
      let constraintsCanvasShape = this.getConstraintsCanvasShape(this.state.menuTrigger.name);
      if(constraintsCanvasShape["locks"]
        && constraintsCanvasShape["locks"].indexOf(constraint) >= 0) {
        if(constraintsCanvasShape[constraint] == this.state.menuTrigger[constraint]) {
          // The constraint is active and set to true, show the undo option
          return { type: "undo", action: constraintsMenu["keep"]};           
        }
        else {
          return { type: "do", action: constraintsMenu["keep"]};  
        }
      } else {
        // Show the do option
        return { type: "do", action: constraintsMenu["keep"]}; 
      }    
  }

  getPreventAction(constraint, constraintsMenu) {
      // Find the corresponding shape on the cosntraints canvas for the menu trigger shape
      // Use the state of that shape to determine what shows up
      let constraintsCanvasShape = this.getConstraintsCanvasShape(this.state.menuTrigger.name);
      if(constraintsCanvasShape["prevents"]
        && constraintsCanvasShape["prevents"].indexOf(constraint) >= 0) {
        if(constraintsCanvasShape[constraint] == this.state.menuTrigger[constraint]) {
          // The constraint is active and set to true, show the undo option
          return { type: "undo", action: constraintsMenu["prevent"]};           
        }
        else {
          return { type: "do", action: constraintsMenu["prevent"]};  
        }
      } else {
        // Show the do option
        return { type: "do", action: constraintsMenu["prevent"]}; 
      }    
  }

  getRelationalMenuItems() {
    // These are just hard coded right now, they don't do anything
    let menuItems = []; 
    menuItems.push((<li>
        <a href="#" tabIndex="-1">Keep global <i>position</i>. (TBD)</a>
      </li>)); 
    menuItems.push((<li>
        <a href="#" tabIndex="-1">Keep <i>position</i> relative to container. (TBD)</a>
      </li>)); 
    menuItems.push((<li>
        <a href="#" tabIndex="-1">Keep <i>position</i> relative to sibling 1. (TBD)</a>
      </li>)); 
    menuItems.push((<li>
        <a href="#" tabIndex="-1">Keep <i>position</i> relative to sibling 2. (TBD)</a>
      </li>)); 
    menuItems.push((<li>
        <a href="#" tabIndex="-1">Keep <i>position</i> relative to sibling 2. (TBD)</a>
      </li>)); 
    menuItems.push((<li>
        <a href="#" tabIndex="-1">Keep global <i>alignment</i>. (TBD)</a>
      </li>)); 
    menuItems.push((<li>
        <a href="#" tabIndex="-1">Keep <i>alignment</i> relative to container. (TBD)</a>
      </li>)); 
    menuItems.push((<li>
        <a href="#" tabIndex="-1">Keep <i>alignment</i> relative to sibling 2. (TBD)</a>
      </li>)); 
    menuItems.push((<li>
        <a href="#" tabIndex="-1">Keep <i>alignment</i> relative to sibling 2. (TBD)</a>
      </li>)); 
    menuItems.push((<li>
        <a href="#" tabIndex="-1">Keep <i>after/below</i> sibling 1. (TBD)</a>
      </li>)); 
    menuItems.push((<li>
        <a href="#" tabIndex="-1">Keep <i>before/above</i> sibling 2. (TBD)</a>
      </li>)); 


    // Appear below/adjacent to the neighbor element
    // Appear above/adjacent to the neighbor element

    // For elements
// Keep position relative to group. 
// Keep position relative to neighbor 1/2. 
// Keep global alignment. 
// Keep alignment relative to group. 
// Keep alignment relative to neighbor 1/2. 
// Keep before/after neighbor 1/2.

    return menuItems;
  }

  render () {
    console.log("render");
    console.log(this.state.menuTrigger.name);
    const isContainer = this.state.menuTrigger.type == "group"; 
    const menuLeft = this.state.left; 
    const menuTop = this.state.top;
    const relational = this.getRelationalMenuItems();
	  return (
      <div className="right-click-menu-container dropdown" style={{left: menuLeft + "px", top: menuTop + "px", display: "block"}} >
        <ul className="dropdown-menu" style={{display: "block"}}>
        {this.state.menuTrigger.type != "canvas" ? 
          (<li role="separator" className="divider divider-top">Element (Keep)</li>) : undefined}
        {this.state.menuTrigger.type != "canvas" ? 
            ConstraintActions.elementConstraints.values.map((key) => {
              let action = this.getKeepAction(key, ConstraintActions.elementConstraints);
              let menuItemKey = this.state.menuTrigger.name + "_" + key; 
              return (<DesignCanvasMenuItem onClick={this.props.onClick} 
                        action={action.action} 
                        actionType={action.type} 
                        menuTrigger={this.state.menuTrigger} 
                        property={key}
                        key={menuItemKey} />);
            }) : undefined}
        {this.state.menuTrigger.canvas_child == true ? 
          ConstraintActions.canvasChildConstraints.values.map((key) => {
            let action = this.getKeepAction(key, ConstraintActions.canvasChildConstraints); 
            let menuItemKey = this.state.menuTrigger.name + "_" + key; 
            return (<DesignCanvasMenuItem onClick={this.props.onClick} 
                        action={action.action}
                        actionType={action.type}
                        menuTrigger={this.state.menuTrigger}
                        property={key}
                        key={menuItemKey}/>); 
          }) : undefined}
        {this.state.menuTrigger.type != "canvas" ? 
          (<li role="separator" className="divider divider-top">Element (Prevent)</li>) : undefined}
        {this.state.menuTrigger.type != "canvas" ? 
            ConstraintActions.elementConstraints.values.map((key) => {
              let action = this.getPreventAction(key, ConstraintActions.elementConstraints);
              let menuItemKey = this.state.menuTrigger.name + "_" + key; 
              return (<DesignCanvasMenuItem onClick={this.props.onClick} 
                        action={action.action} 
                        actionType={action.type} 
                        menuTrigger={this.state.menuTrigger} 
                        property={key}
                        key={menuItemKey} />);
            }) : undefined}
        {this.state.menuTrigger.canvas_child == true ? 
          ConstraintActions.canvasChildConstraints.values.map((key) => {
            let action = this.getPreventAction(key, ConstraintActions.canvasChildConstraints); 
            let menuItemKey = this.state.menuTrigger.name + "_" + key; 
            return (<DesignCanvasMenuItem onClick={this.props.onClick} 
                        action={action.action}
                        actionType={action.type}
                        menuTrigger={this.state.menuTrigger}
                        property={key}
                        key={menuItemKey}/>); 
          }) : undefined}
        {isContainer ? 
          (<li role="separator" className="divider">Group (Keep)</li>) : undefined}
        {isContainer ? 
            ConstraintActions.groupConstraints.values.map((key) => {
              let action = this.getKeepAction(key, ConstraintActions.groupConstraints);
              return (<DesignCanvasMenuItem onClick={this.props.onClick} 
                        action={action.action} 
                        actionType={action.type} 
                        menuTrigger={this.state.menuTrigger} 
                        property={key}
                        key={key} />);
            }) : undefined}
        {isContainer ? 
          (<li role="separator" className="divider">Group (Prevent)</li>) : undefined}
        {isContainer ? 
            ConstraintActions.groupConstraints.values.map((key) => {
              let action = this.getPreventAction(key, ConstraintActions.groupConstraints);
              return (<DesignCanvasMenuItem onClick={this.props.onClick} 
                        action={action.action} 
                        actionType={action.type} 
                        menuTrigger={this.state.menuTrigger} 
                        property={key}
                        key={key} />);
            }) : undefined}
        {/*this.state.menuTrigger.type != "canvas" ? 
          (<li role="separator" className="divider">Relational</li>) : undefined*/}
        {/*this.state.menuTrigger.type != "canvas" ? relational : undefined*/} 
        {this.state.menuTrigger.type == "canvas" ? 
          (<li role="separator" className="divider divider-top">Canvas (Keep)</li>) : undefined}
        {this.state.menuTrigger.type == "canvas" ? 
            ConstraintActions.canvasConstraints.values.map((key) => {
              let action = this.getKeepAction(key, ConstraintActions.canvasConstraints);
              return (<DesignCanvasMenuItem onClick={this.props.onClick} 
                        action={action.action} 
                        actionType={action.type} 
                        menuTrigger={this.state.menuTrigger} 
                        property={key}
                        key={key} />);
            }) : undefined}  
        {this.state.menuTrigger.type == "canvas" ? 
          (<li role="separator" className="divider divider-top">Canvas (Prevent)</li>) : undefined}
        {this.state.menuTrigger.type == "canvas" ? 
            ConstraintActions.canvasConstraints.values.map((key) => {
              let action = this.getPreventAction(key, ConstraintActions.canvasConstraints);
              return (<DesignCanvasMenuItem onClick={this.props.onClick} 
                        action={action.action} 
                        actionType={action.type} 
                        menuTrigger={this.state.menuTrigger} 
                        property={key}
                        key={key} />);
            }) : undefined}  
        </ul>
      </div>
    );
  }
}