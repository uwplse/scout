// App.jsx
import React from "react";
import ConstraintActions from "./ConstraintActions"; 

class FontSizeMenuItem extends React.Component {
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

class ImportanceMenuItem extends React.Component {
  constructor(props) {
    super(props); 
    this.onClick = props.onClick; 
    this.numStars = props.numStars;
  }

  render () {
    var self = this;
    let stars = []; 
    for(var i=0; i<this.numStars; i++) {
      stars.push(<span className="glyphicon glyphicon-star" aria-hidden="true"></span>); 
    }
    return <li className="importance-selector-menu-item" onClick={function() { self.onClick(this.numStars); }}>{stars}</li>; 
  }
}

export default class RightClickMenu extends React.Component {
  constructor(props) {
  	super(props); 
    this.setFontSize = props.setFontSize;
    this.setImportanceLevel = props.setImportanceLevel; 
    this.fontSizes = [12, 16, 18, 20, 22, 28, 30, 32, 36, 40, 48]; 
    this.importanceLevels = [3, 2, 1]; 
  }

  getFontSizeMenuItems() {
    let menuItems = []; 
    for(var i=0; i<this.fontSizes.length; i++) {
      let size = this.fontSizes[i];
      menuItems.push(<FontSizeMenuItem key={size} value={size} onClick={this.setFontSize} />);
    }

    return menuItems; 
  }

  getImportanceMenuItems() {
    let menuItems = []; 
    for(var i=0; i<this.importanceLevels.length; i++) {
      let level = this.importanceLevels[i]; 
      menuItems.push(<ImportanceMenuItem key={level} numStars={level} onClick={this.setImportanceLevel} />);
    }

    return menuItems; 
  }

  render () {
  	let fontSelectorItems = this.getFontSizeMenuItems();
    let importanceMenuItems = this.getImportanceMenuItems();
	  return (
      <div className="right-click-menu">
        <ul className="font-size-selector-menu">{fontSelectorItems}</ul>
        <ul className="importance-selector-menu">{importanceMenuItems}</ul>
      </div>
    );
  }
}