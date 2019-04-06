// App.jsx
import React from "react";
import '../css/DesignMenu.css';

class DesignMenuItem extends React.Component {
  constructor(props) {
  	super(props); 
  	this.label = props.label; 
    this.action = props.action; 
    this.onClick = props.onClick;
  }

  render () {
    const menuAction = this.props.onClick;
    const action = this.props.action;
	  return <li 
            onClick={function() { menuAction(action); }} 
            className="canvas-actions-menu-item">{this.label}
          </li>; 
  }
}

export default class DesignMenu extends React.Component {
  constructor(props) {
  	super(props); 
    this.left = props.left; 
    this.top = props.top; 
    this.menuAction = props.menuAction; 
  }

  constructDesignMenu = () => {
  	let menuItems = []; 
    let save = (<span className="glyphicon glyphicon-star" aria-hidden="true"></span>); 
    let trash = (<span className="glyphicon glyphicon-trash" aria-hidden="true"></span>);
    let zoom = (<span className="glyphicon glyphicon-zoom-in" aria-hidden="true"></span>); 
    let consider = (<span className="glyphicon glyphicon-wrench" aria-hidden="true"></span>); 

    if(this.props.showConsider) {
      menuItems.push(<DesignMenuItem key="consider" onClick={this.menuAction} action="consider" label={consider} />); 
    }

    if(this.props.showSave) {
      menuItems.push(<DesignMenuItem key="save" onClick={this.menuAction} action="save" label={save} />); 
    }

    if(this.props.showTrash) {
      menuItems.push(<DesignMenuItem key="trash" onClick={this.menuAction} action="trash" label={trash} />); 
    }

    if(this.props.showZoom) {
      menuItems.push(<DesignMenuItem key="zoom" onClick={this.menuAction} action="zoom" label={zoom} />); 
    }

    // Temporary to show the cost value on a design 
    // let roundedCost = this.props.cost.toFixed(3); 
    // menuItems.push(<DesignMenuItem key="cost" label={roundedCost} />); 

  	return menuItems; 
  }

  render () {
  	const menuItems = this.constructDesignMenu();
    return (
      <div 
        style={{left: this.left, top: this.top, display: (this.props.hidden ? "none" : ""), 
        opacity: (this.props.visible ? 1 : 0)}} 
        className={"canvas-actions-container " + (menuItems.length ? "" : "hidden")}>
        <div className="canvas-actions-menu-container">
          <ul className="canvas-actions-menu">{menuItems}</ul>
          {/*<div 
            className="canvas-actions-indicators">
            <span className="canvas-actions-new-indicator glyphicon glyphicon-asterisk"></span>
          </div>*/}
        </div>
      </div>); 
  }
}
