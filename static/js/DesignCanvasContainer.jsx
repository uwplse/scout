// App.jsx
import React from "react";
import '../css/DesignCanvasContainer.css';
import {
  DropTarget,
  DropTargetConnector,
  DropTargetMonitor,
  ConnectDropTarget,
} from 'react-dnd'

function collect(connect, monitor) {
  return {
    connectDropTarget: connect.dropTarget(),
    isOver: monitor.isOver(),
    canDrop: monitor.canDrop(),
  }; 
}

const boxTarget = {
  drop(props, monitor) {
    if (props.onDrop) {
      let item = monitor.getItem(); 
      let dropResult = monitor.getDropResult(); 

      // Pass in the ID of the design canvas to move 
      props.onDrop(item.id); 
    }
  },
}

class DesignCanvasContainer extends React.Component {
  render () {
    const { connectDropTarget } = this.props
    return (
      connectDropTarget &&
      connectDropTarget(
        <div 
          className="design-body">
          {this.props.designCanvases}
        </div>)); 
  }
}

export default DropTarget('SmallDesignCanvas', boxTarget, collect)(DesignCanvasContainer)