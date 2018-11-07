// App.jsx
import React from "react";
import SVGInline from "react-svg-inline"; 

export default class WidgetsContainerSVGWidget extends React.Component {
  constructor(props) {
  	super(props);

    this.state = {
      selector: "widgets-container-svg-widget-" + props.id
    }
  }

  componentDidMount() {
    // Set the initial size using the viewBox attribute
    this.setWidgetSizeFromViewBox();
  }

  setWidgetSizeFromViewBox = () => {
    let svgRoot = document.getElementById(this.state.selector); 
    if(svgRoot) { 
      let svgElement = svgRoot.getElementsByTagName('svg');  
      if(svgElement && svgElement.length) {
        let element = svgElement[0]; 
        let viewBox = element.getAttribute("viewBox"); 
        let parts = viewBox.split(" "); 
        if(parts.length == 4) {
          let width = parseFloat(parts[2]); 
          let height = parseFloat(parts[3]); 

          this.setState({
            width: width, 
            height: height
          }); 
        }
      }
    }
  }

  render () {
    return (
        <SVGInline
          id={this.state.selector}
          className="widget-control-svg"
          height={this.state.height + "px"} width={this.state.width + "px"} 
          svg={ this.props.svgData } 
          onClick={this.props.addShapeToConstraintsCanvas(this.props.id,this.props.svgData, this.state.width, this.state.height)} />);
  }
}
