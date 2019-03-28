// App.jsx
import React from "react";
import '../css/DesignCanvasContainer.css';

export default class DesignCanvasContainer extends React.Component {
  render () {
    return (
      <div>
        <div className="design-body">
        {this.props.designCanvases}
        </div>
        {this.props.saved ? (<hr className="feedback-container-separator" />) : undefined}
      </div>); 
  }
}