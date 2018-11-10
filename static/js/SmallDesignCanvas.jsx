// App.jsx
import React from "react";
import {
  ConnectDragSource,
  DragSource,
  DragSourceConnector,
  DragSourceMonitor,
} from 'react-dnd'
import DesignCanvas from './DesignCanvas';

class SmallDesignCanvas extends React.Component {
  render () {
    // Drag and drop components
    const { connectDragSource } = this.props; 
    return (
      connectDragSource &&
      connectDragSource(
          <div>
            <DesignCanvas 
              key={this.props.key} 
              id={this.props.id} 
              elements={this.props.elements}
              savedState={this.props.savedState}
              valid={this.props.valid}
              conflicts={this.props.conflicts}
              added={this.props.added}
              removed={this.props.removed}
              zoomed={this.props.zoomed}
              invalidated={this.props.invalidated}
              svgWidgets={this.props.svgWidgets}
              getConstraintsCanvasShape={this.props.getConstraintsCanvasShape}
              updateConstraintsCanvas={this.props.updateConstraintsCanvasFromDesignCanvas}
              highlightAddedWidget={this.props.highlightAddedWidget}
              highlightWidgetFeedback={this.props.highlightWidgetFeedback}
              saveDesignCanvas={this.props.saveDesignCanvas} 
              trashDesignCanvas={this.props.trashDesignCanvas}
              zoomInOnDesignCanvas={this.props.zoomInOnDesignCanvas}
              getRelativeDesigns={this.props.getRelativeDesigns}
              closeRightClickMenus={this.props.closeRightClickMenus} />
      </div>)); 
  }
}

const designCanvasDragSource = {
  beginDrag(props) {
    return {
      id: props.id,
    }
  },
  endDrag(props, monitor) {
    const item = monitor.getItem()
    const dropResult = monitor.getDropResult()

    if (dropResult) {
      console.log("You dropped " + item.id + " into " + dropResult.id); 
    }
  }
}

export default DragSource('SmallDesignCanvas', designCanvasDragSource, 
  (connect, monitor) => ({
    connectDragSource: connect.dragSource(),
    isDragging: monitor.isDragging()
}))(SmallDesignCanvas)