// App.jsx
import React from "react";
import FabricHelpers from './FabricHelpers';

export default class WidgetFeedback extends React.Component {
  constructor(props) {
  	super(props);
    this.feedbackMessage = props.message; 
    this.updateConstraintsCanvas = props.updateConstraintsCanvas; 
    this.id = props.id; 
    this.parentShape = props.parentShape; 
    this.action = props.action; 
  }

  render () {
    var self = this;
    return (
      <div className="widget-feedback-container">
        <div className="widget-feedback">
          <ul className="widget-feedback-items">
            <li className="widget-feedback-items-list"> 
              <span className="widget-feedback-items-label">
              {this.feedbackMessage}
              </span>
              <button className="widget-feedback-items-remove" onClick={
                  function() { 
                    self.updateConstraintsCanvas(self.parentShape, undefined, self.action, "undo"); 
                  }}>
                <span className="glyphicon glyphicon-minus" aria-hidden="true"></span>
              </button>
            </li>
          </ul>
        </div>
      </div>); 
  }
}
