// App.jsx
import React from "react";

export default class Importer extends React.Component {
  constructor(props) {
  	super(props); 

    this.state  = {
      
    }
  }

  // Draw 
  importSVG(evt) {

  }

  render () {
    return (<button className="import-button" onClick={this.importSVG}>Import an SVG</div>); 
  }
}