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
        feedbackItems={this.props.feedbackItems}
        typingAlerts={this.props.typingAlerts}
        highlighted={this.props.highlighted}
        typed={this.props.typed}
        item={this.props.item}
        displayRightClickMenu={this.props.displayRightClickMenu}
        displayWidgetFeedback={this.props.displayWidgetFeedback}
        getCurrentShapeSiblings={this.props.getCurrentShapeSiblings}
        getCurrentShapePrevNextSiblings={this.props.getCurrentShapePrevNextSiblings}
        getCurrentShapeIndex={this.props.getCurrentShapeIndex}
        getCurrentParentNode={this.props.getCurrentParentNode}
        activeCanvasShape={this.props.activeCanvasShape}
        primarySelection={this.props.primarySelection}
        removeWidgetNode={this.props.removeWidgetNode}
        update={this.props.update}  />); 
  }
}