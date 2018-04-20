// App.jsx
import React from "react";
import FabricHelpers from './FabricHelpers';

export default class WidgetFeedback extends React.Component {
  constructor(props) {
  	super(props);
    this.feedbackMessage = props.message; 
  }

  render () {
    return (
      <div className="widget-feedback-container">
        <div className="widget-feedback">
          <ul className="widget-feedback-items">
            <li>{this.feedbackMessage}</li>
          </ul>
        </div>
      </div>); 
  }
}
