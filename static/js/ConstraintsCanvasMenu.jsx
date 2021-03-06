// App.jsx
import React from "react";
import ConstraintActions from "./ConstraintActions"; 
import Converter from "number-to-words";

class OrderMenuItem extends React.Component {
  constructor(props) {
    super(props); 
    this.index = props.index;  
    this.currentOrder = props.currentOrder; 
    this.onClick = props.onClick; 
  }

  render () {
    let self = this; 
    // let position = Converter.toWordsOrdinal(this.index+1) 
    let orderPosition = this.index == 0 ? "first" : "last"; 

    let label = (this.currentOrder == -1 || this.currentOrder == undefined) ? 
                  "Keep " + orderPosition + "." : "Don't keep " + orderPosition + ".";
    let newOrder = (this.currentOrder == -1 || this.currentOrder == undefined ? this.index : -1); 

    return (<li>
              <a tabIndex="-1" href="#" 
                onClick={function (evt) { self.onClick(evt, newOrder); }}>
                {label}
              </a>
            </li>); 
  }
}

class ContainerOrderMenuItem extends React.Component {
  constructor(props) {
    super(props); 
    this.currentOrderValue = props.currentOrderValue;  
    this.onClick = props.onClick; 
  }

  render () {
    let self = this; 
    let newOrder = this.currentOrderValue == "important" ? "unimportant" : "important"; 
    let label = "The order is " + (this.currentOrderValue == "important" ? "unimportant." : "important."); 
    return (<li>
              <a onClick={function (evt) { self.onClick(evt, newOrder); }} tabIndex="-1" href="#">
                {label}
              </a>
            </li>);   
  }
}

class ImportanceMenuItem extends React.Component {
  constructor(props) {
    super(props); 
    this.onClick = props.onClick; 
    this.importanceLevel = props.importanceLevel; 
    this.label = (this.importanceLevel == "most" ? "Add more emphasis." : (this.importanceLevel == "least" ? "Add less emphasis." : "Add normal emphasis.")); 
  }

  render () {
    let self = this; 
    return <li> 
              <a onClick={function(evt) { self.onClick(evt, self.importanceLevel); }} tabIndex="-1" href="#">
                {this.label}
              </a>
          </li>; 
  }
}

export default class ConstraintsCanvasMenu extends React.Component {
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
    this.getBeforeAndAfterSiblings = props.getBeforeAndAfterSiblings; 
    this.getCurrentShapeSiblings = props.getCurrentShapeSiblings; 
    this.getCurrentShapeIndex = props.getCurrentShapeIndex; 
    this.getCurrentShapeOrder = props.getCurrentShapeOrder; 
    this.getCurrentShapeImportance = props.getCurrentShapeImportance; 
    this.getCurrentContainerOrder = props.getCurrentContainerOrder; 
    this.getCurrentShapeType = props.getCurrentShapeType; 
    this.fontSizes = [12, 16, 18, 20, 22, 28, 30, 32, 36, 40, 48]; 

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

  getImportanceMenuItems = () => {
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

  getOrderMenuItems = () => {
    let orderMenuItems = []; 

    // Decide whether to show the order menu item based on the index of the shape in the 
    // parent container.
    let shapeType = this.getCurrentShapeType(this.shapeID); 
    let shapeIndex = this.getCurrentShapeIndex(this.shapeID); 
    let siblings = this.getCurrentShapeSiblings(this.shapeID);
    let currOrder = this.getCurrentShapeOrder(this.shapeID);  
    let showOrderMenuItem = (!siblings.prev || !siblings.next) && shapeType != "canvas";  

    if(showOrderMenuItem) {
      orderMenuItems.push(<OrderMenuItem key={this.shapeID} currentOrder={currOrder} index={shapeIndex} onClick={this.setOrder} />); 
    }

    return orderMenuItems;   
  }

  getContainerOrderMenuItems = () => {
    let menuItems = []; 

    if(this.setContainerOrder) {
      let currentOrder = this.getCurrentContainerOrder(this.shapeID); 
      menuItems.push(<ContainerOrderMenuItem key={this.shapeID} currentOrderValue={currentOrder} onClick={this.setContainerOrder} />); 
    }

    return menuItems; 
  }


  openFontSizeMenu = (evt) => {
    evt.stopPropagation(); 

    // Close other menus if they are open
    this.setState({
      importanceMenuShown: false, 
      labelMenuShown: false, 
      fontSizeMenuShown: true, 
      orderMenuShown: false
    });
  }

  openImportanceMenu = (evt) => {
    evt.stopPropagation(); 

    // Close other menus if they are open
    this.setState({
      fontSizeMenuShown: false, 
      labelMenuShown: false,
      importanceMenuShown: true, 
      orderMenuShown: false
    }); 
  }

  openLabelMenu = (evt) => {
    evt.stopPropagation(); 

   // Close other menus if they are open
    this.setState({
      fontSizeMenuShown: false, 
      labelMenuShown: true,
      importanceMenuShown: false, 
      orderMenuShown: false
    }); 
  }

  openOrderMenu = (evt) => {
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

    // let labelItems = []; 
    // if(this.setLabel) {
    //   labelItems = this.getLabelItems();
    // }

    const fontSizeShown = this.setFontSize != undefined; 
    const labelShown = this.setLabel != undefined; 

    // Importance will be enabled for all controls
    let importanceMenuItems = this.getImportanceMenuItems();
    const importanceShown = this.setImportanceLevel != undefined && importanceMenuItems.length; 

    let containerOrderMenuItems = this.getContainerOrderMenuItems();
    const containerOrderShown = this.setContainerOrder != undefined && containerOrderMenuItems.length; 

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
      <div id="right-click-menu-container" 
        className="right-click-menu-container dropdown" 
        data-toggle="dropdown" 
        style={{left: menuLeft + "px", top: menuTop + "px", display: "block"}}>
        <ul className="dropdown-menu" style={{display: "block"}}>
          {/*<li className="dropdown-submenu">
            <a tabIndex="-1" href="#" onClick={this.openImportanceMenu}>Set the emphasis to ...<span className="caret"></span></a>
            { importanceMenuShown ? <ul style={{display: "block" }} className="dropdown-menu">{importanceMenuItems}</ul> : undefined } 
          </li>*/}
        {importanceShown ? importanceMenuItems : undefined}
        {/*labelShown ? labelItems : undefined*/}
        {orderShown ? orderMenuItems : undefined}
        {containerOrderShown ? containerOrderMenuItems : undefined}
        </ul>
      </div>
    );
  }
}