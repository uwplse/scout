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

    menuItems.push(<DesignMenuItem key="save" onClick={this.menuAction} action="save" label={save} />); 
    menuItems.push(<DesignMenuItem key="trash" onClick={this.menuAction} action="trash" label={trash} />); 

    if(this.props.showZoom) {
      menuItems.push(<DesignMenuItem key="zoom" onClick={this.menuAction} action="zoom" label={zoom} />); 
    }

  	return menuItems; 
  }

  render () {
  	const menuItems = this.constructDesignMenu();
    return (
      <div 
        style={{left: this.left, top: this.top, display: (this.props.visible ? "" : "none")}} 
        className={"canvas-actions-container " + (menuItems.length ? "" : "hidden")}>
        <div class="canvas-actions-menu-container">
          <ul className="canvas-actions-menu">{menuItems}</ul>
          <div 
            className="canvas-actions-indicators" 
            style={{display: (this.props.new ? "" : "none")}}>
            <span className="canvas-actions-new-indicator glyphicon glyphicon-asterisk"></span>
          </div>
        </div>
      </div>); 
  }
}
