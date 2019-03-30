// App.jsx
import React from "react";
import '../css/DesignCanvasContainer.css';

export default class DesignCanvasContainer extends React.Component {
  render () {
    return (this.props.saved ? 
      <div>
        <div className="design-body">
        {this.props.designCanvases}
        </div>
        <hr className="feedback-container-separator" />
      </div> : 
	    <div className="design-body">
	    {this.props.designCanvases}
	    </div>
     ); 
  }
}