// App.jsx
import React from "react";

class CanvasMenuItem extends React.Component {
  constructor(props) {
  	super(props); 
  	this.text = props.text; 
  }

  render () {
	return <li className="canvas-menu-item">{this.text}</li>; 
  }
}

export default class CanvasMenu extends React.Component {
  constructor(props) {
  	super(props); 
  	this.menuOptions = ["Keep position here."]; 
  	this.menuShown = props.menuShown; 
  }

  render () {
  	let menuItems = []; 
	this.menuOptions.forEach((menu) => {
	  menuItems.push(
	    <CanvasMenuItem key={menu} text={menu} />
	  );
	});

	return <ul className="canvas-menu">{menuItems}</ul>; 
  }
}
