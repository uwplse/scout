import React from "react";
import {
  DropTarget,
  DropTargetConnector,
  DropTargetMonitor,
  ConnectDropTarget,
} from 'react-dnd'; 
import { NativeTypes } from 'react-dnd-html5-backend'; 

const { FILE } = NativeTypes; 

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
      props.onDrop(props, monitor)
    }
  },
}

class WidgetsContainer extends React.Component {
  constructor(props) {
    super(props); 
  }

  render() {
    const { canDrop, isOver, connectDropTarget } = this.props
    const isActive = canDrop && isOver
    const hasWidgets = this.props.widgets.length; 
    return (
      connectDropTarget &&
      connectDropTarget(
        <div className="panel panel-primary widgets-container">
          <div className="panel-heading"> 
            <h3 className="panel-title">Widgets</h3>
          </div>  
          <div className="panel-body widgets-panel">         
           {(hasWidgets ? 
              this.props.widgets : 
              (<form 
                className="box has-advanced-upload" method="post" 
                action="" 
                encType="multipart/form-data">
                <div className="box__input">
                  <svg className="box__icon" xmlns="http://www.w3.org/2000/svg" width="50" height="43" viewBox="0 0 50 43">
                    <path d="M48.4 26.5c-.9 0-1.7.7-1.7 1.7v11.6h-43.3v-11.6c0-.9-.7-1.7-1.7-1.7s-1.7.7-1.7 1.7v13.2c0 .9.7 1.7 1.7 1.7h46.7c.9 0 1.7-.7 1.7-1.7v-13.2c0-1-.7-1.7-1.7-1.7zm-24.5 6.1c.3.3.8.5 1.2.5.4 0 .9-.2 1.2-.5l10-11.6c.7-.7.7-1.7 0-2.4s-1.7-.7-2.4 0l-7.1 8.3v-25.3c0-.9-.7-1.7-1.7-1.7s-1.7.7-1.7 1.7v25.3l-7.1-8.3c-.7-.7-1.7-.7-2.4 0s-.7 1.7 0 2.4l10 11.6z"></path>
                  </svg>
                  <label><span className="box__dragndrop">Drag your SVGs here.</span>.</label>
                </div>
                <div className="box__uploading">Uploading&hellip;</div>
                <div className="box__success">Done!</div>
                <div className="box__error">Error! <span></span>.</div>
              </form>))}
          </div>
        </div>
      )
    ); 
  }
}

export default DropTarget([FILE], boxTarget, collect)(WidgetsContainer)