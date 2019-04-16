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

  initializeSizeAndType = () => {
    let svgRoot = document.getElementById(this.state.selector); 
    if(svgRoot) { 
      let svgElement = svgRoot.getElementsByTagName('svg');  
      if(svgElement && svgElement.length) {
        // Initialize the width and height from the viewBox attribute
        let element = svgElement[0]; 
        let viewBox = element.getAttribute("viewBox"); 
        if(viewBox) {
          let parts = viewBox.split(" "); 
          if(parts.length == 4) {
            let width = Math.round(parseFloat(parts[2])); 
            let height = Math.round(parseFloat(parts[3])); 
            this.setState({
              width: width, 
              height: height
            }); 
          }
        }
        else {
          let widthAttr = element.getAttribute("width"); 
          let heightAttr = element.getAttribute("height"); 
          let width = Math.round(parseFloat(widthAttr)); 
          let height = Math.round(parseFloat(heightAttr));
          this.setState({
            width: width, 
            height: height
          }); 
        }

        // Initialize the element type: 
        // Contains leaf level nodes other than text -> 'element'
        // Contains only text leaf level nodes -> 'text'
        if(this.state.type != "group") {
          let type_attr = element.getAttribute("type"); 
          let type = type_attr ? type_attr : "element"; 
          this.setState({
            type: type
          }); 
        }
      }
    }
  }

  render () {
    return (
        <div className="widget-control-container"> 
          {(this.state.type == "separator" ? <span className="widget-control-label">(Separator)</span> : undefined)}
          <SVGInline
            id={this.state.selector}
            style={{display: (this.props.visible || this.props.type == "group" ? "" : "none")}}
            className="widget-control"
            height={this.state.height + "px"} width={this.state.width + "px"} 
            svg={ this.props.svgData } 
            onClick={this.props.addShapeToConstraintsCanvas(this.props.id,this.props.svgData, this.state.type, this.state.width, this.state.height)} />
        </div>);

  }
}
