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
	  return <li className="right-click-menu-item" onClick={function(evt) { self.onClick(evt, self.value); }}>{self.value}</li>; 
  }
}

class LabelMenuItem extends React.Component {
  constructor(props) {
    super(props); 
    this.shapeId = props.shapeId; 
    this.shapeLabel = props.shapeLabel; 
    this.onClick = props.onClick; 
  }

  render () {
    var self = this;
    return <li className="right-click-menu-item" onClick={function(evt) { self.onClick(evt, self.shapeId); }}>{this.shapeLabel}</li>; 
  }
}

class OrderCheckbox extends React.Component {
  constructor(props) {
    super(props); 
    this.index = props.index;  
    this.currentOrder = props.currentOrder; 
    this.onClick = props.onClick; 
  }

  render () {
    var self = this;
    let label = "Keep " + Converter.toWordsOrdinal(this.index+1) + "."; 
    return (<div className="form-check">
                <input className="form-check-input" type="checkbox" checked={this.currentOrder != -1 && this.currentOrder != undefined} 
                  onClick={function(evt) { 
                    self.currentOrder = (self.currentOrder == -1 || self.currentOrder == undefined ? self.index : -1); 
                    self.onClick(evt, self.currentOrder); 
                  }} />
                <label className="form-check-label" for="defaultCheck1">
                  {label}
                </label>
              </div>); 
  }
}

class ContainerOrderCheckbox extends React.Component {
  constructor(props) {
    super(props); 
    this.currentOrderValue = props.currentOrderValue;  
    this.onClick = props.onClick; 
  }

  render () {
    var self = this;
    let newOrder = this.currentOrderValue == "important" ? "unimportant" : "important"; 
    return (<div className="form-check">
                <input className="form-check-input"  
                onClick={function(evt) { 
                  self.currentOrderValue = newOrder; 
                  self.onClick(evt, newOrder); 
                }} 
                type="checkbox" checked={this.currentOrderValue == "important"} id="defaultCheck1" />
                <label className="form-check-label" for="defaultCheck1">
                  Order Important
                </label>
              </div>);   
  }
}

class ImportanceMenuItem extends React.Component {
  constructor(props) {
    super(props); 
    this.onClick = props.onClick; 
    this.importanceLevel = props.importanceLevel; 
    this.label = (this.importanceLevel == "most" ? "More Emphasis" : (this.importanceLevel == "least" ? "Less Emphasis" : "Normal Emphasis")); 
  }

  render () {
    var self = this;
    return <li className="right-click-menu-item" onClick={function(evt) { self.onClick(evt, self.importanceLevel); }}>{this.label}</li>; 
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
    this.getSiblingLabelItem = props.getSiblingLabelItem; 
    this.getCurrentShapeSiblings = props.getCurrentShapeSiblings; 
    this.getCurrentShapeIndex = props.getCurrentShapeIndex; 
    this.getCurrentShapeOrder = props.getCurrentShapeOrder; 
    this.getCurrentShapeImportance = props.getCurrentShapeImportance; 
    this.getCurrentContainerOrder = props.getCurrentContainerOrder; 
    this.fontSizes = [12, 16, 18, 20, 22, 28, 30, 32, 36, 40, 48]; 

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

    let currentImportance = this.getCurrentShapeImportance(this.shapeID); 
    if(currentImportance != "most") {
      menuItems.push(<ImportanceMenuItem key={"most"} importanceLevel="most" onClick={this.setImportanceLevel} />); 
    }
    
    if(currentImportance != "least") {
      menuItems.push(<ImportanceMenuItem key={"least"} importanceLevel="least" onClick={this.setImportanceLevel} />);      
    }

    if(currentImportance != "normal") {
      menuItems.push(<ImportanceMenuItem key={"normal"} importanceLevel="normal" onClick={this.setImportanceLevel} />);      
    }

    return menuItems; 
  }

  getLabelItems() {
    // Label items should return the text of the sibling element and the shape ID
    let labelItems = this.getSiblingLabelItem(this.shapeID); 
    let menuItems = []; 
    for(var i=0; i<labelItems.length; i++) {
      let label = labelItems[i]; 
      menuItems.push(<LabelMenuItem key={i} shapeId={label.id} shapeLabel={label.label} onClick={this.setLabel} />); 
    }
    return menuItems; 
  }

  getOrderCheckBox() {
    let checkbox = []; 

    // Decide whether to show the order menu item based on the index of the shape in the 
    // parent container.
    let shapeIndex = this.getCurrentShapeIndex(this.shapeID); 
    let siblings = this.getCurrentShapeSiblings(this.shapeID);
    let currOrder = this.getCurrentShapeOrder(this.shapeID);  
    let showOrderCheckbox = (shapeIndex == 0 || shapeIndex == (siblings.length - 1)); 

    if(showOrderCheckbox) {
      checkbox.push(<OrderCheckbox key={this.shapeID} currentOrder={currOrder} index={shapeIndex} onClick={this.setOrder} />); 
    }

    return checkbox;   
  }

  getContainerOrderCheckbox() {
    let checkbox = []; 

    if(this.setContainerOrder) {
      let currentOrder = this.getCurrentContainerOrder(this.shapeID); 
      checkbox.push(<ContainerOrderCheckbox key={this.shapeID} currentOrderValue={currentOrder} onClick={this.setContainerOrder} />); 
    }

    return checkbox; 
  }

  openFontSizeMenu(evt) {
    evt.stopPropagation(); 

    // Close other menus if they are open
    this.setState({
      importanceMenuShown: false, 
      labelMenuShown: false, 
      fontSizeMenuShown: true, 
      orderMenuShown: false
    });
  }

  openImportanceMenu(evt) {
    evt.stopPropagation(); 

    // Close other menus if they are open
    this.setState({
      fontSizeMenuShown: false, 
      labelMenuShown: false,
      importanceMenuShown: true, 
      orderMenuShown: false
    }); 
  }

  openLabelMenu(evt) {
    evt.stopPropagation(); 

   // Close other menus if they are open
    this.setState({
      fontSizeMenuShown: false, 
      labelMenuShown: true,
      importanceMenuShown: false, 
      orderMenuShown: false
    }); 
  }

  openOrderMenu(evt) {
    evt.stopPropagation(); 

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

    let containerOrderCheckbox = this.getContainerOrderCheckbox();
    const containerOrderShown = this.setContainerOrder != undefined && containerOrderCheckbox.length; 

    let orderCheckbox = this.getOrderCheckBox(); 
    const orderShown = this.setOrder != undefined && orderCheckbox.length; 

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
            <a tabIndex="-1" href="#" onClick={this.openImportanceMenu}>Emphasis<span className="caret"></span></a>
            { importanceMenuShown ? <ul style={{display: "block" }} className="dropdown-menu">{importanceMenuItems}</ul> : undefined } 
          </li> 
        {orderShown ? 
          (<li className="dropdown-submenu">
              {orderCheckbox}
            </li>) : undefined}
        {containerOrderShown ? 
          (<li className="dropdown-submenu">
              {containerOrderCheckbox}
            </li>) : undefined}
        {labelShown ? 
          (<li className="dropdown-submenu">
              <a tabIndex="-1" href="#" onClick={this.openLabelMenu}>Labels<span className="caret"></span></a>
              { labelMenuShown ? <ul style={{display: "block" }} className="dropdown-menu">{labelItems}</ul> : undefined } 
            </li>) : undefined}

        {/*fontSizeShown ? 
          (<li className="dropdown-submenu">
              <a tabIndex="-1" href="#" onClick={this.openFontSizeMenu}>Font Size<span className="caret"></span></a>
              { fontSizeMenuShown ? <ul style={{display: "block" }} className="dropdown-menu">{fontSizeSelectorItems}</ul> : undefined } 
            </li>) : undefined*/}
        </ul>
      </div>
    );
  }
}