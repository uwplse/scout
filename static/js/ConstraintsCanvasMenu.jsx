// App.jsx
import React from "react";

class ConstraintsCanvasMenuItem extends React.Component {
  constructor(props) {
  	super(props); 
  	this.label = props.label; 
  }

  render () {
	  return <li className="canvas-menu-item">{this.label}</li>; 
  }
}

export default class ConstraintsCanvasMenu extends React.Component {
  constructor(props) {
  	super(props); 
  	this.menuTrigger = props.menuTrigger;
    this.left = props.left; 
    this.top = props.top; 
    this.id = props.menuID; 

    this.state = {
      menuShown: props.menuShown
    };
  }

  componentWillReceiveProps(nextProps) {
    if(nextProps.menuShown !== this.props.menuShown){
        this.setState({menuShown:nextProps.menuShown});
    }  
  }

  constructConstraintsMenu() {
  	let menuItems = []; 

    let locks = this.menuTrigger["locks"]; 
    if(locks) {
      for(var i=0; i<locks.length; i++) {
        var lock = locks[i]; 
        var label = this.menuTrigger[lock];
        if(lock == "location") {
          label = " x: " + this.menuTrigger[lock].x + ", y: " + this.menuTrigger[lock].y;
        } 

        menuItems.push(<ConstraintsCanvasMenuItem label={lock + " " + label} key={lock} />); 
      }      
    } else {
      menuItems.push(<ConstraintsCanvasMenuItem label="none." key="none" />);
    }

  	return menuItems; 
  }

  render () {
  	const menuItems = this.constructConstraintsMenu();
    const menuShown = this.state.menuShown;
    return (
      <div style={{left: this.left, top: this.top}} className={"canvas-menu-container " + (menuShown ? "" : "hidden")}>
        <ul className="canvas-menu-list">{menuItems}</ul>
      </div>); 
  }
}
