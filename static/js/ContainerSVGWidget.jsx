// App.jsx
import React from "react";
import SVGWidget from './SVGWidget';

export default class ContainerSVGWidget extends React.Component {
  constructor(props) {
    super(props); 
  }

  render() {
    return (
      <SVGWidget 
        key={this.props.id} 
        shape={this.props.shape} 
        id={this.props.id}
        source={this.props.source}
        isContainer={this.props.isContainer}
        highlighted={this.props.highlighted}
        showImportanceLevels={this.props.showImportanceLevels}
        checkSolutionValidity={this.props.checkSolutionValidity} 
        displayRightClickMenu={this.props.displayRightClickMenu}
        hideRightClickMenu={this.props.hideRightClickMenu}
        createLabelsGroup={this.props.createLabelsGroup}
        getCurrentShapeSiblings={this.props.getCurrentShapeSiblings}
        getCurrentShapeIndex={this.props.getCurrentShapeIndex} />); 
  }
}