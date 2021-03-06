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
              <a onClick={(!this.disabled ? this.onClick.bind(this, this.props.shapeID) : undefined)} tabIndex="-1" href="#">
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
      disabled={this.props.isGroup} />;
    const ungroupMenuItem = <GroupingMenuItem 
      onClick={this.props.ungroupSelected} 
      shapeID={this.props.shapeID}
      label={"Ungroup"}
      disabled={!this.props.isGroup} />;

    const menuItems = [groupMenuItem, ungroupMenuItem]; 

    let groupToType = this.props.typeGroupSize >= 1; 
    let isTyped = this.props.isTyped; 
    if(groupToType || isTyped) {
      const repeatGroupMenuItem = <GroupingMenuItem
        onClick={this.props.createRepeatGroup}
        shapeID={this.props.shapeID}
        label={"Create repeat group"}
        disabled={isTyped} />;

      menuItems.push(repeatGroupMenuItem);
      const removeRepeatGroupMenuItem = <GroupingMenuItem
        onClick={this.props.removeRepeatGroup}
        shapeID={this.props.shapeID}
        label={"Remove repeat group"}
        disabled={!isTyped} />;
      menuItems.push(removeRepeatGroupMenuItem);
    }

    if(!this.props.containsGroup) {
      const alternateGroupMenuItem = <GroupingMenuItem
        onClick={this.props.createAlternateGroup}
        shapeID={this.props.shapeID}
        label={"Create alternate group"}
        disabled={this.props.isAlternate} />;

      menuItems.push(alternateGroupMenuItem);
      const removeAlternateGroupMenuItem = <GroupingMenuItem
        onClick={this.props.removeAlternateGroup}
        shapeID={this.props.shapeID}
        label={"Remove alternate group"}
        disabled={!this.props.isAlternate} />;
      menuItems.push(removeAlternateGroupMenuItem);
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