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
	  return <li className="right-click-menu-item" onClick={function() { self.onClick(self.value); }}>{self.value}</li>; 
  }
}

class LabelMenuItem extends React.Component {
  constructor(props) {
    super(props); 
    this.shapeId = props.shapeId; 
    this.shapeLabel = props.shapeLabel; 
    this.direction = props.direction; 
    this.onClick = props.onClick; 
  }

  render () {
    var self = this;
    let label = this.shapeLabel + " (" + this.direction + ")"; 
    return <li className="right-click-menu-item" onClick={function() { self.onClick(self.shapeId, self.direction); }}>{label}</li>; 
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
      stars.push(<span key={i} className="glyphicon glyphicon-star" aria-hidden="true"></span>); 
    }
    return <li className="right-click-menu-item" onClick={function() { self.onClick(self.numStars); }}>{stars}</li>; 
  }
}

export default class RightClickMenu extends React.Component {
  constructor(props) {
  	super(props); 
    this.setFontSize = props.setFontSize;
    this.setImportanceLevel = props.setImportanceLevel; 
    this.setLabel = props.setLabel; 
    this.shapeID = props.shapeID; 

    // A method in constraints canvas to get sibling elements to the element launching this menu
    // It will return a set of lables to display as child menu items
    this.getSiblingLabelItems = props.getSiblingLabelItems; 
    this.fontSizes = [12, 16, 18, 20, 22, 28, 30, 32, 36, 40, 48]; 
    this.importanceLevels = [3, 2, 1]; 

    // Method bindings
    this.openFontSizeMenu = this.openFontSizeMenu.bind(this); 
    this.openLabelMenu = this.openLabelMenu.bind(this);
    this.openImportanceMenu = this.openImportanceMenu.bind(this);

    this.state = {
      fontSizeMenuLocation: {
        top: 0, 
        left: 0
      }, 
      importanceMenuLocation: {
        top: 0, 
        left: 0
      }, 
      labelMenuLocation: {
        top: 0, 
        left: 0
      }, 
      left: props.left, 
      top: props.top, 
      fontSizeMenuShown: false, 
      importanceMenuShown: false, 
      labelMenuShown: false
    }
  }

  componentDidMount() {
    if(this.setFontSize != undefined) {
      this.computeSubMenuPositions();
    }
  }

  computeSubMenuPositions() {
    // Compute the left positioning of the submenu based on the width of this container
    let rightClickMenu = document.getElementById("right-click-menu-container"); 
    let bbox = rightClickMenu.getBoundingClientRect(); 
    let left = bbox.width; 

    let fontMenu = document.getElementById("font-size-menu-label"); 
    let fontLabelBox = fontMenu.getBoundingClientRect(); 

    let labelMenu = document.getElementById("label-menu-label"); 
    let labelBox = labelMenu.getBoundingClientRect(); 

    this.setState({
      fontSizeMenuLocation: {
        top: labelBox.height, 
        left: left
      }, 
      importanceMenuLocation: {
        top: fontLabelBox.height + labelBox.height, 
        left: left
      }, 
      labelMenuLocation: {
        top: 0, 
        left: left
      }
    }); 
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

  getLabelItems() {
    // Label items should return the text of the sibling element and the shape ID
    let labelItems = this.getSiblingLabelItems(this.shapeID); 
    let menuItems = []; 
    for(var i=0; i<labelItems.length; i++) {
      let label = labelItems[i]; 
      menuItems.push(<LabelMenuItem key={i} shapeId={label.id} shapeLabel={label.label} direction={label.direction} onClick={this.setLabel} />); 
    }
    return menuItems; 
  }

  openFontSizeMenu() {
    // Close other menus if they are open
    this.setState({
      importanceMenuShown: false, 
      labelMenuShown: false, 
      fontSizeMenuShown: true
    });
  }

  openImportanceMenu() {
    // Close other menus if they are open
    this.setState({
      fontSizeMenuShown: false, 
      labelMenuShown: false,
      importanceMenuShown: true
    }); 
  }

  openLabelMenu() {
   // Close other menus if they are open
    this.setState({
      fontSizeMenuShown: false, 
      labelMenuShown: true,
      importanceMenuShown: false
    }); 
  }

  render () {
    // Font size selecting is only enabled for label controls
    let fontSizeSelectorItems = [];
    if(this.setFontSize) {
      fontSizeSelectorItems = this.getFontSizeMenuItems();
    }

    let labelItems = []; 
    if(this.setLabel) {
      labelItems = this.getLabelItems();
    }

    const fontSizeShown = this.setFontSize != undefined; 
    const labelShown = this.setLabel != undefined; 

    // Importance will be enabled for all controls
    let importanceMenuItems = this.getImportanceMenuItems();

    const fontSizeLeft = this.state.fontSizeMenuLocation.left; 
    const fontSizeTop = this.state.fontSizeMenuLocation.top; 
    const importanceLeft = this.state.importanceMenuLocation.left; 
    const importanceTop = this.state.importanceMenuLocation.top; 
    const labelLeft = this.state.labelMenuLocation.left; 
    const labelTop = this.state.labelMenuLocation.top; 
    const menuLeft = this.state.left; 
    const menuTop = this.state.top; 
    const importanceMenuShown = this.state.importanceMenuShown; 
    const fontSizeMenuShown = this.state.fontSizeMenuShown; 
    const labelMenuShown = this.state.labelMenuShown; 

	  return (
      <div id="right-click-menu-container" style={{left: menuLeft + "px", top: menuTop + "px"}} className="right-click-menu-container">
        {(labelShown ? (
            <div id="label-menu-label" className="right-click-menu-label" onClick={this.openLabelMenu}> 
              <span>Labels</span>
              <span className="glyphicon glyphicon-chevron-right" aria-hidden="true"></span>
            </div>) : undefined)}
        {((labelShown && labelMenuShown)? 
          (<div  style={{left: labelLeft + "px", top: labelTop + "px"}} className="right-click-submenu-container">
            <ul className="right-click-menu">{labelItems}</ul>
          </div>) : undefined)}
        {(fontSizeShown ? (
            <div id="font-size-menu-label" className="right-click-menu-label" onClick={this.openFontSizeMenu}> 
              <span>Font Sizes</span>
              <span className="glyphicon glyphicon-chevron-right" aria-hidden="true"></span>
            </div>) : undefined)}
        {((fontSizeShown && fontSizeMenuShown)? 
          (<div  style={{left: fontSizeLeft + "px", top: fontSizeTop + "px"}} className="right-click-submenu-container">
            <ul className="right-click-menu">{fontSizeSelectorItems}</ul>
          </div>) : undefined)}
        {(fontSizeShown ? 
          (<div id="importance-menu-label" className="right-click-menu-label" onClick={this.openImportanceMenu}>
            <span>Importance Levels</span>
            <span className="glyphicon glyphicon-chevron-right" aria-hidden="true"></span>
          </div>) : undefined)}
        {((!fontSizeShown || importanceMenuShown) ? 
          (<div className="right-click-submenu-container" style={{left: importanceLeft + "px", top: importanceTop + "px"}}>
            <ul className="right-click-menu">{importanceMenuItems}</ul>
          </div>) : undefined)}
      </div>
    );
  }
}