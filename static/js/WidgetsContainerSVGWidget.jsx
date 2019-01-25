// App.jsx
import React from "react";
import SVGInline from "react-svg-inline"; 

export default class WidgetsContainerSVGWidget extends React.Component {
  constructor(props) {
  	super(props);

    this.state = {
      type: props.type,
      selector: "widgets-container-svg-widget-" + props.id
    }
  }

  componentDidMount() {
    // Set the initial size using the viewBox attribute
    this.initializeSizeAndType();
  }
  
  containsNotText(node) {
    // Parse the SVG to determine if it only contains a text node, then the type is "text"
    // else the type will be "element". Only inferring two types for now as we don't need specialized
    // rules in the solver for different element types other than "text"

    // Find leaf nodes, if the leaf node is anything other than a text node, return false
    // otherwise keep 
    if(node.children && node.children.length) {
      for(let i=0; i<node.children.length; i++) {
        let result = this.containsNotText(node.children[i]); 
        if(result) {
          return result; 
        }
      }
    }
    else {
      // Get the tagName of the element
      let tagName = node.tagName; 
      if(tagName != "text" && tagName != "title" && tagName != "tspan") {
        return true; 
      }
    }

    return false; 
  }

  initializeSizeAndType = () => {
    let svgRoot = document.getElementById(this.state.selector); 
    if(svgRoot) { 
      let svgElement = svgRoot.getElementsByTagName('svg');  
      if(svgElement && svgElement.length) {
        // Initialize the width and height from the viewBox attribute
        let element = svgElement[0]; 
        let viewBox = element.getAttribute("viewBox"); 
        let parts = viewBox.split(" "); 
        if(parts.length == 4) {
          let width = Math.round(parseFloat(parts[2])); 
          let height = Math.round(parseFloat(parts[3])); 
          this.setState({
            width: width, 
            height: height
          }); 
        }

        // Initialize the element type: 
        // Contains leaf level nodes other than text -> 'element'
        // Contains only text leaf level nodes -> 'text'
        if(this.state.type != "group") {
          let containsNotText = this.containsNotText(element); 
          let type = containsNotText ? 'element' : 'text'; 
          console.log(type);
          this.setState({
            type: type
          }); 
        }
      }
    }
  }

  render () {
    return (
        <SVGInline
          id={this.state.selector}
          style={{display: (this.props.visible ? "" : "none")}}
          className="widget-control-svg"
          height={this.state.height + "px"} width={this.state.width + "px"} 
          svg={ this.props.svgData } 
          onClick={this.props.addShapeToConstraintsCanvas(this.props.id,this.props.svgData, this.state.type, this.state.width, this.state.height)} />);
  }
}
