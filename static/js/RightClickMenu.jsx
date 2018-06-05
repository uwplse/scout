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
    let label = "Keep " + Converter.toWordsOrdinal(this.index+1) + "."; 
    return <li className="right-click-menu-item" onClick={function() { self.onClick(self.index); }}>{label}</li>; 
  }
}

class ContainerOrderMenuItem extends React.Component {
  constructor(props) {
    super(props); 
    this.currentOrderValue = props.currentOrderValue;  
    this.onClick = props.onClick; 
  }

  render () {
    var self = this;
    let newOrder = this.currentOrderValue == "important" ? "unimportant" : "important"; 
    let label = "Make order " + newOrder + "."; 
    return <li className="right-click-menu-item" onClick={function() { self.onClick(newOrder); }}>{label}</li>; 
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
    this.setContainerOrder = props.menuCallbacks.setContainerOrder; 
    this.shapeID = props.shapeID; 

    // A method in constraints canvas to get sibling elements to the element launching this menu
    // It will return a set of lables to display as child menu items
    this.getSiblingLabelItems = props.getSiblingLabelItems; 
    this.getCurrentShapeSiblings = props.getCurrentShapeSiblings; 
    this.getCurrentShapeIndex = props.getCurrentShapeIndex; 
    this.getCurrentShapeOrder = props.getCurrentShapeOrder; 
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
    // this.computeSubMenuPositions();
  }

  computeSubMenuPositions() {
    // Compute the left positioning of the submenu based on the width of this container
    let rightClickMenu = document.getElementById("right-click-menu-container"); 
    let bbox = rightClickMenu.getBoundingClientRect(); 
    let left = bbox.width; 

    let importanceMenu = document.getElementById("importance-menu-label");
    let importanceMenuBox = importanceMenu.getBoundingClientRect(); 

    let currentTop = 0; 
    let importanceLocation = {
      top: currentTop, 
      left: left
    }; 

    currentTop = currentTop + importanceMenuBox.height; 
    let orderLocation = this.state.orderMenuLocation; 
    if(this.setOrder) {
      let orderMenu = document.getElementById("order-menu-label");
      if(orderMenu) {
        let orderMenuBox = orderMenu.getBoundingClientRect(); 

        orderLocation = {
          top: currentTop, 
          left: left
        }; 

        currentTop = currentTop + orderMenuBox.height; 
      }
    }

    let labelLocation = this.state.labelMenuLocation; 
    let fontLocation = this.state.fontSizeMenuLocation; 
    if(this.setFontSize) {
      let labelMenu = document.getElementById("label-menu-label"); 
      if(labelMenu) {
        let labelBox = labelMenu.getBoundingClientRect(); 
        labelLocation = {
          top: currentTop, 
          left: left
        }; 

        currentTop = currentTop + labelBox.height; 
        fontLocation = {
          top: currentTop, 
          left: left
        };
      } 
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

    // Decide whether to show the order menu item based on the index of the shape in the 
    // parent container.
    let shapeIndex = this.getCurrentShapeIndex(this.shapeID); 
    let siblings = this.getCurrentShapeSiblings(this.shapeID); 
    let showOrderMenu = (shapeIndex == 0 || shapeIndex == (siblings.length - 1)); 

    if(showOrderMenu) {
      menuItems.push(<OrderMenuItem key={this.shapeID} index={shapeIndex} onClick={this.setOrder} />); 
    }

    if(this.setContainerOrder) {
      let currentOrder = this.getCurrentShapeOrder(this.shapeID); 
      menuItems.push(<ContainerOrderMenuItem key={this.shapeID} currentOrderValue={currentOrder} onClick={this.setContainerOrder} />); 
    }

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
    const orderShown = this.setOrder != undefined && orderMenuItems.length; 

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
      <div id="right-click-menu-container" className="right-click-menu-container dropdown" data-toggle="dropdown" style={{left: menuLeft + "px", top: menuTop + "px", display: "block"}}>
        <ul className="dropdown-menu" style={{display: "block"}}>
          <li className="dropdown-submenu">
            <a tabIndex="-1" href="#" onClick={this.openImportanceMenu}>Importance Levels<span className="caret"></span></a>
            { importanceMenuShown ? <ul style={{display: "block" }} className="dropdown-menu">{importanceMenuItems}</ul> : undefined } 
          </li> 
        {orderShown ? 
          (<li className="dropdown-submenu">
              <a tabIndex="-1" href="#" onClick={this.openOrderMenu}>Order<span className="caret"></span></a>
              { orderMenuShown ? <ul style={{display: "block" }} className="dropdown-menu">{orderMenuItems}</ul> : undefined } 
            </li>) : undefined}

        {labelShown ? 
          (<li className="dropdown-submenu">
              <a tabIndex="-1" href="#" onClick={this.openLabelMenu}>Labels<span className="caret"></span></a>
              { labelMenuShown ? <ul style={{display: "block" }} className="dropdown-menu">{labelItems}</ul> : undefined } 
            </li>) : undefined}

        {fontSizeShown ? 
          (<li className="dropdown-submenu">
              <a tabIndex="-1" href="#" onClick={this.openFontSizeMenu}>Font Size<span className="caret"></span></a>
              { fontSizeMenuShown ? <ul style={{display: "block" }} className="dropdown-menu">{fontSizeSelectorItems}</ul> : undefined } 
            </li>) : undefined}
        </ul>
      </div>
    );
  }
}