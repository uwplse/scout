// App.jsx
import React from "react";
import '../css/FeedbackContainer.css';

export default class FeedbackContainer extends React.Component {
  constructor(props) {
  	super(props);
  }

  render () {
    return (
        <div className="panel panel-primary feedback-container">
          <div className="panel-heading"> 
            <h3 className="panel-title">Feedback
            </h3>
          </div>
          <div tabIndex="1" className="panel-body"> 
          </div>
      </div>); 
  }
}
