// App.jsx
import React from "react";
import ConstraintsCanvasSVGWidget from './ConstraintsCanvasSVGWidget';

export default class ConstraintsCanvasContainerSVGWidget extends React.Component {
  constructor(props) {
    super(props); 
  }

  render() {
    return (
      <ConstraintsCanvasSVGWidget 
        key={this.props.id} 
        shape={this.props.shape} 
        id={this.props.id}
        source={this.props.source}
        isContainer={this.props.isContainer}
        highlighted={this.props.highlighted}
        typed={this.props.typed}
        item={this.props.item}
        checkSolutionValidity={this.props.checkSolutionValidity} 
        displayRightClickMenu={this.props.displayRightClickMenu}
        hideRightClickMenu={this.props.hideRightClickMenu}
        createLabelsGroup={this.props.createLabelsGroup}
        getCurrentShapeSiblings={this.props.getCurrentShapeSiblings}
        getCurrentShapeIndex={this.props.getCurrentShapeIndex} />); 
  }
}