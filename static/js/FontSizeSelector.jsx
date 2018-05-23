// App.jsx
import React from "react";
import ConstraintActions from "./ConstraintActions"; 

class FontSizeSelectorItem extends React.Component {
  constructor(props) {
  	super(props); 
    this.value = props.value; 
    this.onClick = props.onClick; 
  }

  render () {
    var self = this;
	  return <li className="font-size-selector-menu-item" onClick={function() { self.onClick(self.value); }}>{self.value}</li>; 
  }
}

export default class FontSizeSelector extends React.Component {
  constructor(props) {
  	super(props); 
    this.onClick = props.onClick; 
    this.fontSizes = [12, 16, 18, 20, 22, 28, 30, 32, 36, 40, 48]; 
  }

  getMenuItems() {
    let menuItems = []; 
    for(var i=0; i<this.fontSizes.length; i++) {
      let size = this.fontSizes[i];
      menuItems.push(<FontSizeSelectorItem key={size} value={size} onClick={this.onClick} menuTrigger={this.menuTrigger}/>);
    }

    return menuItems; 
  }

  render () {
  	let fontSelectorItems = this.getMenuItems();
	  return (
      <ul className="font-size-selector-menu">{fontSelectorItems}</ul>
    );
  }
}