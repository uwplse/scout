// App.jsx
import React from "react";

export default class Importer extends React.Component {
  constructor(props) {
  	super(props); 

    // Bind the method to the context of this class
    this.importSVG = this.importSVG.bind(this); 

    this.state  = {
      disabled: false, 
      svg: undefined
    }
  }

  // Draw 
  importSVG(evt) {
    // Update the state
    this.state.disabled = false; 

    this.state.svg = <svg>; 

    // Must be included to notify React to update the state
    this.setState({
      disabled: this.state.disabled
    });
  }

  render () {
    let disabled = this.state.disabled; 
    let svg = this.state.svg; 
    return (<div>
      <button disabled={this.state.disabled} className={(this.state.disabled ? "disabled" : "")} onClick={this.importSVG}>Import an SVG</button>
      {this.state.svg}
      </div>); 
  }
}