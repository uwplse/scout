// App.jsx
import React from "react";

export default class WidgetTyping extends React.Component {
  constructor(props) {
  	super(props);
    this.setTypedGroup = props.setTypedGroup;  
    this.shapeID = props.shapeID;    
  }

  render () {
    var self = this;
    return (
      <div className="widget-control-typing">
        Make this a typed group? 
        <span className="widget-control-typing-yes" onClick={function() { self.setTypedGroup(self.shapeID, "Yes"); }}>Yes</span>
        <span className="widget-control-typing-no" onClick={function() { self.setTypedGroup(self.shapeID, "No"); }}>No</span>
      </div>); 
  }
}
