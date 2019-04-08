// App.jsx
import React from "react";
import '../css/DesignMenu.css';

export default class FeedbackSeparator extends React.Component {
  constructor(props) {
  	super(props); 
  	this.label = props.label; 
  }

  render () {
    const menuAction = this.props.onClick;
    const action = this.props.action;
	  return (<div className="feedback-container-separator-group">
             <span className="feedback-container-separator" />
             <span className="feedback-container-separator-label">{this.label}</span>
            <span className="feedback-container-separator" />
            </div>); 
  }
}