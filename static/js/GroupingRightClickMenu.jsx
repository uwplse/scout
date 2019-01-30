// App.jsx
import React from "react";

class GroupingMenuItem extends React.Component {
  constructor(props) {
    super(props); 
    this.onClick = props.onClick; 
    this.label = props.label;
    this.disabled = props.disabled;  
  }

  render () {
    let self = this; 
    return <li className={(this.disabled ? "dropdown-disabled" : "")}> 
              <a onClick={this.onClick.bind(this, this.props.shapeID)} tabIndex="-1" href="#">
                {this.label}
              </a>
          </li>; 
  }
}

export default class GroupingRightClickMenu extends React.Component {
  constructor(props) {
  	super(props); 
  }

  render () {
    const groupMenuItem = <GroupingMenuItem 
      shapeID={this.props.shapeID} 
      onClick={this.props.groupSelected} 
      label={"Group"}
      disabled={!this.props.groupElements} />;
    const ungroupMenuItem = <GroupingMenuItem 
      onClick={this.props.ungroupSelected} 
      shapeID={this.props.shapeID}
      label={"Ungroup"}
      disabled={this.props.groupElements} />;

    const menuItems = [groupMenuItem, ungroupMenuItem]; 

    if(this.props.typeGroupSize > 1) {
      const repeatGroupMenuItem = <GroupingMenuItem
        onClick={this.props.createRepeatGroup}
        shapeID={this.props.shapeID}
        label={"Create repeat group"}
        disabled={false} />;
      menuItems.push(repeatGroupMenuItem);
    }

	  return (
      <div id="right-click-menu-container" 
        className="right-click-menu-container dropdown" 
        data-toggle="dropdown" 
        style={{left: this.props.menuLeft + "px", top: this.props.menuTop + "px", display: "block"}}>
        <ul className="dropdown-menu" style={{display: "block"}}>
          {menuItems}
        </ul>
      </div>
    );
  }
}