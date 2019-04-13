// App.jsx
import React from "react";
import '../css/DesignCanvasContainer.css';

export default class DesignCanvasContainer extends React.Component {
  render () {
    return (this.props.saved ? 
      <div className="design-canvas-container-saved">
        <div className="design-body design-body-saved">
        {this.props.designCanvases}
        </div>
        <hr className="design-canvas-container-separator" />
      </div> : 
	    <div className="design-body">
	    {this.props.designCanvases}
	    </div>
     ); 
  }
}