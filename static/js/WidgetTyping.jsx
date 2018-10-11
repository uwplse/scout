// App.jsx
import React from "react";

export default class WidgetTyping extends React.Component {
  constructor(props) {
  	super(props);
    this.createRepeatGroup = props.createRepeatGroup;
    this.closeAlert = props.closeTypingAlert;   
    this.groupID = props.groupID;   
    this.type = props.type;  
    this.groupSize = props.groupSize; 
  }

  render () {
    return (
      <div className="alert alert-info alert-dismissable designs-canvas-container-alert" role="alert">
        <button 
          onClick={this.closeAlert(this.groupID)} 
          type="button" 
          className="close" 
          aria-label="Close">
          <span aria-hidden="true">&times;</span>
        </button>
        Click <a href="#" onClick={this.createRepeatGroup(this.groupID, true, this.groupSize)}
          className="alert-link">here</a> to make this a <strong>repeat group</strong>. 
      </div>); 
  }
}
