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
    this.fontSizes = [12, 16, 18, 20, 22, 28, 30, 32, 36, 40, 48]; 
    this.importanceLevels = [3, 2, 1]; 

    // Method bindings
    this.openFontSizeMenu = this.openFontSizeMenu.bind(this); 
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
      left: props.left, 
      top: props.top, 
      fontSizeMenuShown: false, 
      importanceMenuShown: false, 
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

    this.setState({
      fontSizeMenuLocation: {
        top: 0, 
        left: left
      }, 
      importanceMenuLocation: {
        top: fontLabelBox.height, 
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

  openFontSizeMenu() {
    // Close other menus if they are open
    this.setState({
      importanceMenuShown: false
    });

    this.setState({
      fontSizeMenuShown: true
    }); 
  }

  openImportanceMenu() {
    // Close other menus if they are open
    this.setState({
      fontSizeMenuShown: false
    });

    this.setState({
      importanceMenuShown: true
    }); 
  }

  render () {
    // Font size selecting is only enabled for label controls
    let fontSizeSelectorItems = [];
    if(this.setFontSize) {
      fontSizeSelectorItems = this.getFontSizeMenuItems();
    }

    const fontSizeShown = this.setFontSize != undefined; 

    // Importance will be enabled for all controls
    let importanceMenuItems = this.getImportanceMenuItems();

    const fontSizeLeft = this.state.fontSizeMenuLocation.left; 
    const fontSizeTop = this.state.fontSizeMenuLocation.top; 
    const importanceLeft = this.state.importanceMenuLocation.left; 
    const importanceTop = this.state.importanceMenuLocation.top; 
    const menuLeft = this.state.left; 
    const menuTop = this.state.top; 
    const importanceMenuShown = this.state.importanceMenuShown; 
    const fontSizeMenuShown = this.state.fontSizeMenuShown; 

	  return (
      <div id="right-click-menu-container" style={{left: menuLeft + "px", top: menuTop + "px"}} className="right-click-menu-container">
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