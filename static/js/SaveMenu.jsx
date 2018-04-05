// App.jsx
import React from "react";

class SaveMenuItem extends React.Component {
  constructor(props) {
  	super(props); 
  	this.label = props.label; 
    this.action = props.action; 
    this.onClick = props.onClick; 
  }

  render () {
    const menuAction = this.props.onClick;
    const action = this.props.action;
	  return <li onClick={menuAction.bind(this,action)} className="canvas-menu-item">{this.label}</li>; 
  }
}

export default class SaveMenu extends React.Component {
  constructor(props) {
  	super(props); 
    this.left = props.left; 
    this.top = props.top; 
    this.menuAction = props.menuAction; 
  }

  constructSaveMenu() {
  	let menuItems = []; 

    menuItems.push(<SaveMenuItem key="save" onClick={this.menuAction} action="save" label="Save this design." />); 
    menuItems.push(<SaveMenuItem key="trash" onClick={this.menuAction} action="trash" label="Trash this design." />); 

  	return menuItems; 
  }

  render () {
  	const menuItems = this.constructSaveMenu();
    return (
      <div style={{left: this.left, top: this.top}} className={"canvas-menu-container " + (menuItems.length ? "" : "hidden")}>
        <ul className="canvas-menu-list">{menuItems}</ul>
      </div>); 
  }
}
