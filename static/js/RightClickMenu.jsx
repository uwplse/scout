// App.jsx
import React from "react";
import ConstraintActions from "./ConstraintActions"; 
import Converter from "number-to-words";

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

class OrderMenuItem extends React.Component {
  constructor(props) {
    super(props); 
    this.index = props.index;  
    this.onClick = props.onClick; 
  }

  render () {
    var self = this;
    let label = "Keep " + Converter.toOrdinal(this.index+1) + "."; 
    return <li className="right-click-menu-item" onClick={function() { self.onClick(self.index); }}>{label}</li>; 
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
    this.setFontSize = props.menuCallbacks.setFontSize; 
    this.setImportanceLevel = props.menuCallbacks.setImportanceLevel; 
    this.setLabel = props.menuCallbacks.setLabel; 
    this.setOrder = props.menuCallbacks.setOrder;  
    this.shapeID = props.shapeID; 

    // A method in constraints canvas to get sibling elements to the element launching this menu
    // It will return a set of lables to display as child menu items
    this.getSiblingLabelItems = props.getSiblingLabelItems; 
    this.getCurrentShapeIndex = props.getCurrentShapeIndex; 
    this.fontSizes = [12, 16, 18, 20, 22, 28, 30, 32, 36, 40, 48]; 
    this.importanceLevels = [3, 2, 1]; 

    // Method bindings
    this.openFontSizeMenu = this.openFontSizeMenu.bind(this); 
    this.openLabelMenu = this.openLabelMenu.bind(this);
    this.openImportanceMenu = this.openImportanceMenu.bind(this);
    this.openOrderMenu = this.openOrderMenu.bind(this);

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
      orderMenuLocation: {
        top: 0, 
        left: 0
      },
      left: props.left, 
      top: props.top, 
      fontSizeMenuShown: false, 
      importanceMenuShown: false, 
      labelMenuShown: false, 
      orderMenuShown: false
    }
  }

  componentDidMount() {
    this.computeSubMenuPositions();
  }

  computeSubMenuPositions() {
    // Compute the left positioning of the submenu based on the width of this container
    let rightClickMenu = document.getElementById("right-click-menu-container"); 
    let bbox = rightClickMenu.getBoundingClientRect(); 
    let left = bbox.width; 

    let importanceMenu = document.getElementById("importance-menu-label");
    let importanceMenuBox = importanceMenu.getBoundingClientRect(); 

    let importanceLocation = {
      top: 0, 
      left: left
    }; 

    let orderMenu = document.getElementById("order-menu-label");
    let orderMenuBox = orderMenu.getBoundingClientRect(); 
    let orderLocation = {
      top: importanceMenuBox.height, 
      left: left
    }; 

    let labelLocation = this.state.labelMenuLocation; 
    let fontLocation = this.state.fontSizeMenuLocation; 
    if(this.setFontSize) {
      let labelMenu = document.getElementById("label-menu-label"); 
      let labelBox = labelMenu.getBoundingClientRect(); 

      labelLocation = {
        top: orderLocation.top + orderMenuBox.height, 
        left: left
      }; 

      fontLocation = {
        top: labelLocation.top + labelBox.height, 
        left: left
      }; 
    }

    this.setState({
      importanceMenuLocation: importanceLocation, 
      orderMenuLocation: orderLocation, 
      labelMenuLocation: labelLocation, 
      fontSizeMenuLocation: fontLocation
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

  getOrderMenuItems() {
    let menuItems = []; 

    let index = this.getCurrentShapeIndex(this.shapeID); 
    menuItems.push(<OrderMenuItem key={this.shapeID} index={index} onClick={this.setOrder} />); 
    return menuItems; 
  }

  openFontSizeMenu() {
    // Close other menus if they are open
    this.setState({
      importanceMenuShown: false, 
      labelMenuShown: false, 
      fontSizeMenuShown: true, 
      orderMenuShown: false
    });
  }

  openImportanceMenu() {
    // Close other menus if they are open
    this.setState({
      fontSizeMenuShown: false, 
      labelMenuShown: false,
      importanceMenuShown: true, 
      orderMenuShown: false
    }); 
  }

  openLabelMenu() {
   // Close other menus if they are open
    this.setState({
      fontSizeMenuShown: false, 
      labelMenuShown: true,
      importanceMenuShown: false, 
      orderMenuShown: false
    }); 
  }

  openOrderMenu() {
   // Close other menus if they are open
    this.setState({
      fontSizeMenuShown: false, 
      labelMenuShown: false,
      importanceMenuShown: false, 
      orderMenuShown: true
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
    let orderMenuItems = this.getOrderMenuItems();

    const fontSizeLeft = this.state.fontSizeMenuLocation.left; 
    const fontSizeTop = this.state.fontSizeMenuLocation.top; 
    const importanceLeft = this.state.importanceMenuLocation.left; 
    const importanceTop = this.state.importanceMenuLocation.top; 
    const labelLeft = this.state.labelMenuLocation.left; 
    const labelTop = this.state.labelMenuLocation.top; 
    const orderLeft = this.state.orderMenuLocation.left; 
    const orderTop = this.state.orderMenuLocation.top; 
    const menuLeft = this.state.left; 
    const menuTop = this.state.top; 
    const importanceMenuShown = this.state.importanceMenuShown; 
    const fontSizeMenuShown = this.state.fontSizeMenuShown; 
    const labelMenuShown = this.state.labelMenuShown; 
    const orderMenuShown = this.state.orderMenuShown; 

	  return (
      <div id="right-click-menu-container" style={{left: menuLeft + "px", top: menuTop + "px"}} className="right-click-menu-container">
        <div id="importance-menu-label" className="right-click-menu-label" onClick={this.openImportanceMenu}>
          <span>Importance Levels</span>
          <span className="glyphicon glyphicon-chevron-right" aria-hidden="true"></span>
        </div>
        {importanceMenuShown ? 
          (<div className="right-click-submenu-container" style={{left: importanceLeft + "px", top: importanceTop + "px"}}>
            <ul className="right-click-menu">{importanceMenuItems}</ul>
          </div>) : undefined}
        <div id="order-menu-label" className="right-click-menu-label" onClick={this.openOrderMenu}>
          <span>Order</span>
          <span className="glyphicon glyphicon-chevron-right" aria-hidden="true"></span>
        </div>
        {orderMenuShown ? 
          (<div className="right-click-submenu-container" style={{left: orderLeft + "px", top: orderTop + "px"}}>
            <ul className="right-click-menu">{orderMenuItems}</ul>
          </div>) : undefined}
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
      </div>
    );
  }
}