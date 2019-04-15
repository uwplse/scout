// App.jsx
import React from "react";
import '../css/DesignCanvasContainer.css';

export default class DesignCanvasContainer extends React.Component {
  render () {
    return (
	    <div className={"design-body " + (this.props.saved ? "saved-body" : "")}>
      {(this.props.saved ? this.props.designCanvases : undefined)}
      {!this.props.saved && this.props.designCanvases && this.props.designCanvases.length ? 
        <div className="design-body-valid">
  	    {this.props.designCanvases}
        </div> : undefined}
      {!this.props.saved && this.props.invalidDesignCanvases && this.props.invalidDesignCanvases.length ? 
        <div className="design-body-invalid"> 
          {this.props.invalidDesignCanvases}
        </div> : undefined}
	    </div>
     ); 
  }
}

        /*<hr className="design-canvas-container-separator" />*/
