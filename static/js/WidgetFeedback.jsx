// App.jsx
import React from "react";
import '../css/WidgetFeedback.css'; 

export default class WidgetFeedback extends React.Component {
  constructor(props) {
  	super(props);
    this.feedbackMessage = props.message; 
    this.updateConstraintsCanvas = props.updateConstraintsCanvas; 
    this.id = props.id; 
    this.shape = props.shape; 
    this.action = props.action; 
    this.type = props.type; 
    this.property = props.property; 
    this.value = props.value;
    
    this.state = {
      highlighted: props.highlighted
    }
  }

  static getDerivedStateFromProps(nextProps, prevState) {
    return {
      highlighted: nextProps.highlighted
    }    
  }

  onClick = (evt) => {
    // Prevent from reaching the selected node and unselecting it. 
    evt.stopPropagation(); 

    this.action["undo"].updateConstraintsCanvasShape(this.property, this.shape, this.value);

    // If there are any linkedShapes, we should also update their feedback as well 
    for(let i=0; i<this.props.linkedShapes.length; i++) {
      this.action["undo"].updateConstraintsCanvasShape(this.property, this.props.linkedShapes[i],  this.value);      
    } 

    // Notify the ConstraintsCanvas to update its rendering
    this.props.update(this.shape, this.property, this.value); 
  }

  render () {
    var highlighted = this.state.highlighted; 
    return (
      <div className="widget-feedback-container">
        <div className="widget-feedback">
          <ul className={"widget-feedback-items " + (highlighted ? "highlighted" : "")}>
            <li className="widget-feedback-items-list"> 
              <span className="widget-feedback-items-label">
              {this.feedbackMessage}
              </span>
              <button 
                className={"widget-feedback-items-remove " + (highlighted ? "highlighted" : "")} 
                onClick={this.onClick}>
                <span className="glyphicon glyphicon-minus" aria-hidden="true"></span>
              </button>
            </li>
          </ul>
        </div>
      </div>); 
  }
}
