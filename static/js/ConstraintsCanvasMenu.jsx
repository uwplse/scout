// App.jsx
import React from "react";

class ConstraintsCanvasMenuItem extends React.Component {
  constructor(props) {
  	super(props); 
  	this.label = props.label; 
  }

  render () {
	  return <li className="canvas-menu-item">{this.label}</li>; 
  }
}

export default class ConstraintsCanvasMenu extends React.Component {
  constructor(props) {
  	super(props); 
  	this.menuTrigger = props.menuTrigger;
  }

  constructConstraintsMenu() {
  	let menuItems = []; 

    let locks = this.menuTrigger["locks"]; 
    if(locks) {
      for(var i=0; i<locks.length; i++) {
        var lock = locks[i]; 
        menuItems.push(<ConstraintsCanvasMenuItem label={lock + " " + this.menuTrigger[lock]} key={lock} />); 
      }      
    }

  	return menuItems; 
  }

  render () {
  	let menuItems = this.constructConstraintsMenu();
    if(!menuItems.length) {
        menuItems.push(<ConstraintsCanvasMenuItem label="None." key="none" />);
    }

	  return <ul className="canvas-menu">{menuItems}</ul>; 
  }
}
