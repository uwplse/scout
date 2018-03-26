// App.jsx
import React from "react";

const menuTextToProperty = {
	'Keep position here.': {
		'label': 'locked_position', 
		'value': true
	},
	'Unlock position.': {
		'label': 'locked_position',
		'value': false
	}
}

class CanvasMenuItem extends React.Component {
  constructor(props) {
  	super(props); 
  	this.text = props.text; 
  	this.menuTrigger = props.menuTrigger;  // Pass this along from parent so we can return the shape/selected menu item combination when the menu closes
  }

  render () {
  	// The bind will send the menu trigger (JSON shape object) and selected item (text) back to the canvas to propogate it back to the constraints canvas
	let menuProperty = menuTextToProperty[this.text]; 
	return <li className="canvas-menu-item" onClick={this.props.onClick.bind(this, this.menuTrigger, menuProperty)} >{this.text}</li>; 
  }
}

export default class CanvasMenu extends React.Component {
  constructor(props) {
  	super(props); 
  	this.menuOptions = ["Keep position here."]; 
  	this.menuShown = props.menuShown; 
  	this.menuTrigger = props.menuTrigger; // This is the JSON of the shape that triggered the menu open 
  }

  render () {
  	let menuItems = []; 
	this.menuOptions.forEach((menu) => {
	  menuItems.push(
	    <CanvasMenuItem onClick={this.props.onClick} menuTrigger={this.menuTrigger} key={menu} text={menu} />
	  );
	});

	return <ul className="canvas-menu">{menuItems}</ul>; 
  }
}
