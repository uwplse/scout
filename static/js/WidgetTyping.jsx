// App.jsx
import React from "react";

export default class WidgetTyping extends React.Component {
  constructor(props) {
  	super(props);
    this.setTypingOnGroup = props.setTypingOnGroup;
    this.closeAlert = props.closeTypingAlert;   
    this.groupID = props.groupID;   
    this.type = props.type;  
    this.groupSize = props.groupSize; 
  }

  render () {
    var self = this;
    return (
      <div className="alert alert-info alert-dismissable widget-control-typing" role="alert">
        <button onClick={function() { self.closeAlert(self.groupID) }} type="button" className="close" aria-label="Close">
          <span aria-hidden="true">&times;</span>
        </button>
        Click <a href="#" onClick={function() { self.setTypingOnGroup(self.groupID, true, self.groupSize); }} className="alert-link">here</a> to make this a <strong>repeat grid</strong> group. 
      </div>); 
  }
}
