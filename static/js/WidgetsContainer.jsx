import React from "react";
import '../css/WidgetsContainer.css';
import {
  DropTarget,
  DropTargetConnector,
  DropTargetMonitor,
  ConnectDropTarget,
} from 'react-dnd'; 
import { NativeTypes } from 'react-dnd'; 
import WidgetsContainerSVGWidget from "./WidgetsContainerSVGWidget"; 

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

    this.state = {
      hovered: false
    };
  }

  onDragOver = () => {
    console.log("onDragOver");
    this.setState({
      hovered: true
    }); 
  }

  onDragLeave = () => {
    this.setState({
      hovered: false
    }); 
  }

  onDrop = () => {
    this.setState({
      hovered: false
    });
  }


  render() {
    const { connectDropTarget } = this.props
    const visibleWidgets = this.props.widgets.filter((widget) => { return (widget.visible); }); 
    const hasVisibleWidgets = visibleWidgets.length;
    const expandedClass = (!this.state.collapsed ? "glyphicon-chevron-left" : "glyphicon-chevron-right");
    const buttonGroupClass = (!this.state.collapsed ? "" : "widgets-button-collapsed");  
    const expanded = !this.props.widgetsCollapsed; 

    const widgets = this.props.widgets.map((widget) => {
      if(!widget.item && (widget.visible || widget.type == "group")) { // Items cannot be directly added as they are children of typed groups
        return (<WidgetsContainerSVGWidget 
          className="widget-control" 
          id={widget.id}
          visible={widget.visible}
          svgData={widget.svgData}
          type={widget.type}
          addShapeToConstraintsCanvas={this.props.addShapeToConstraintsCanvas}/>  
        ); 
      }
      return undefined;
    });

    return (
      connectDropTarget &&
      connectDropTarget(
        <div className={"panel panel-primary widgets-container " 
        + (expanded ? "" : "widgets-container-collapsed")}>
          <div className="panel-heading"> 
            <h3 
              className={"panel-title " + (expanded ? "" : "collapsed")}>
              Widgets
            </h3>
            <div 
              className={"btn-group header-button-group " 
              + (expanded ? "" : "collapsed")}>
              <button type="button" className="btn btn-default design-canvas-button" 
                onClick={this.props.onClick}>Clear Widgets</button>
            </div>
            <div 
              className={"btn-group header-button-group " + buttonGroupClass}> 
              <button type="button" className={"btn btn-default glyphicon " + expandedClass}
                onClick={this.props.toggleWidgetsPanel}></button>
            </div>
          </div>  
          <div 
            className={"panel-body widgets-panel " 
            + (expanded ? "" : "collapsed")}
            onDragOver={this.onDragOver}
            onDragLeave={this.onDragLeave}
            onDrop={this.onDrop}>         
           {hasVisibleWidgets ? 
              widgets : 
              (<form 
                className={"box has-advanced-upload " + (this.state.hovered ? "hovered" : "")} 
                method="post" 
                action="" 
                encType="multipart/form-data">
                <div className="box__input">
                  <svg className="box__icon" xmlns="http://www.w3.org/2000/svg" width="50" height="43" viewBox="0 0 50 43">
                    <path d="M48.4 26.5c-.9 0-1.7.7-1.7 1.7v11.6h-43.3v-11.6c0-.9-.7-1.7-1.7-1.7s-1.7.7-1.7 1.7v13.2c0 .9.7 1.7 1.7 1.7h46.7c.9 0 1.7-.7 1.7-1.7v-13.2c0-1-.7-1.7-1.7-1.7zm-24.5 6.1c.3.3.8.5 1.2.5.4 0 .9-.2 1.2-.5l10-11.6c.7-.7.7-1.7 0-2.4s-1.7-.7-2.4 0l-7.1 8.3v-25.3c0-.9-.7-1.7-1.7-1.7s-1.7.7-1.7 1.7v25.3l-7.1-8.3c-.7-.7-1.7-.7-2.4 0s-.7 1.7 0 2.4l10 11.6z"></path>
                  </svg>
                  <div className="card card-body bg-light"><span className="box__dragndrop">Drag and drop your SVG interface elements here.</span></div>
                </div>
                <div className="box__uploading">Uploading&hellip;</div>
                <div className="box__success">Done!</div>
                <div className="box__error">Error! <span></span>.</div>
              </form>)}
          </div>
        </div>
      )
    ); 
  }
}

export default DropTarget([FILE], boxTarget, collect)(WidgetsContainer)