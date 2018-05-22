import React from "react";
import SVGWidget from './SVGWidget';
import WidgetFeedback from './WidgetFeedback';
import SortableTree, { removeNodeAtPath, getNodeAtPath } from 'react-sortable-tree';
import 'react-sortable-tree/style.css'; // This only needs to be imported once in your app

export default class ConstraintsCanvas extends React.Component {
  constructor(props) {
  	super(props); 

    // Callback to update a shape on the constraints canvas through the PageContainer so that it can validate the current state
    this.updateConstraintsCanvas = props.updateConstraintsCanvas; 
    this.checkSolutionValidity =  props.checkSolutionValidity; 

    // This collection contains the set of shapes on the constraints canvas
    this.constraintsShapesMap = {};
    this.widgetTreeNodeMap = {};

    this.canvasWidth = 375; 
    this.canvasHeight = 667; 

    this.defaultControlWidth = 120; 
    this.defaultControlHeight = 40; 
    this.defaultFeedbackHeight = 40; 
    this.rowPadding = 10; 

    this.state = { 
      constraintModified: false, 
      treeData: [], 
      pageFeedbackWidgets: []
    }; 
  }

  componentDidMount() {
    // Create an object to represent the  top level canvas shape
    let canvas = {
      "name": _.uniqueId(),
      "type": "canvas", 
      "children": [],
      "location": {
        x: 0, 
        y: 0
      }, 
      "size": {
        width: this.canvasWidth, 
        height: this.canvasHeight
      }   
    }

    this.canvasLevelShape = canvas;
    this.constraintsShapesMap[canvas.name] = canvas; 
 
    // Create an object to represent the page level object (A container for shapes at the root level)
    let page = {
      "name": _.uniqueId(),
      "type": "page", 
      "children": []
    }

    this.constraintsShapesMap[page.name] = page; 
    this.pageLevelShape = page; 
    canvas.children.push(page); 
  }

  getWidget(shape, type, src) {
    let shapeId = shape.name;
    return (<SVGWidget 
              key={shapeId} 
              shape={shape} 
              id={shapeId} 
              type={type}
              source={src}
              width={shape.size.width}
              height={shape.size.height}
              checkSolutionValidity={this.checkSolutionValidity} />);
  }

  addShapeOfTypeToCanvas(src, type) {
    let shape = this.createConstraintsCanvasShapeObject(type); 
    // Initialize size values 
    shape.size = {}; 
    shape.size.height = SVGWidget.initialHeightValues(shape.type);
    shape.size.width = SVGWidget.initialWidthValues(shape.type);

    let shapeId = shape.name;
    let widget = this.getWidget(shape, type, src); 

    let newTreeNode = {
        title: widget, 
        subtitle: []
    }; 

    this.widgetTreeNodeMap[shapeId] = newTreeNode; 
    this.setState(state => ({
      treeData: this.state.treeData.concat(newTreeNode)
    }), this.checkSolutionValidity);
  }

  getWidgetFeedback(shapeId, parentShape, action, message, highlighted){
    return (<WidgetFeedback 
              key={shapeId} 
              id={shapeId} 
              parentShape={parentShape}
              action={action}
              message={message} 
              highlighted={highlighted}
              updateConstraintsCanvas={this.updateConstraintsCanvas}/>); 
  }

  getConstraintsCanvasShape(shapeID) {
    return this.constraintsShapesMap[shapeID]; 
  }

  highlightWidgetFeedback(shapeId, lock, highlighted) {
    // Find the widget with this shape ID in the constraints tree
    let treeNode = this.widgetTreeNodeMap[shapeId]; 
    let feedbackItems = undefined; 
    if(treeNode != undefined) {
      feedbackItems = treeNode.subtitle; 
    }else {
      feedbackItems = this.state.pageFeedbackWidgets; 
    }

    // Find the corresponding feedback item
    let feedbackIndex = -1; 
    for(var i=0; i<feedbackItems.length; i++) {
      if(feedbackItems[i].props.action["do"].key == lock) {
        feedbackIndex = i; 
      }
    }

    if(feedbackIndex > -1) {
      let feedbackItem = feedbackItems[feedbackIndex]; 

      // Highlight parameter can be true or false which determines whether the new feedback item is highlighted or unhighlighted
      let newFeedbackItem = this.getWidgetFeedback(shapeId, feedbackItem.props.parentShape, feedbackItem.props.action, feedbackItem.props.message, highlighted); 
      
      // Splice out the old item 
      feedbackItems.splice(feedbackIndex, 1); 
      feedbackItems.splice(feedbackIndex, 0, newFeedbackItem); 
    }

    this.setState(state => ({
      treeData: this.state.treeData
    }));      
  }

  updateWidgetFeedbacks(shape, action, actionType) {    
    // The shape was already updated so we just need to re-render the tree to get the new sizes
    // Add WidgetFeedbackItem to correct item in the tree

    // Find the corresponding tree node
    let shapeId = shape.name; 
    let uniqueId = _.uniqueId();

    if(shape.type == "canvas") {
      // Add the feedback widgets to the page level instead
      if(actionType == "do") {
        let message = action[actionType].getFeedbackMessage(shape);
        let id = shapeId + "_" + uniqueId; 

        let widgetFeedback = this.getWidgetFeedback(id, shape, action, message);
        this.state.pageFeedbackWidgets.push(widgetFeedback);   
      }else {
        // Remove the feedback widget from the page level
        let feedbackItems = this.state.pageFeedbackWidgets; 
        let feedbackIndex = -1; 
        for(var i=0; i<feedbackItems.length; i++){
          if(feedbackItems[i].props.action[actionType].key == action[actionType].key) {
            feedbackIndex = i; 
          }
        }

        if(feedbackIndex > -1) {
          this.state.pageFeedbackWidgets.splice(feedbackIndex, 1);
        }
      }

      this.setState(state => ({
        pageFeedbackWidgets: this.state.pageFeedbackWidgets
      })); 
    } else {
      let treeNode = this.widgetTreeNodeMap[shapeId]; 

      // Check whether to remove or add a widget feedback item
      if(actionType == "do") {
        let message = action[actionType].getFeedbackMessage(shape);
        let id = shapeId + "_" + uniqueId; 
        let widgetFeedback = this.getWidgetFeedback(id, shape, action, message);
        treeNode.subtitle.push(widgetFeedback);       
      } else {
        // Remove the corresponding widget feedback item
        var feedbackItems = treeNode.subtitle; 
        var feedbackIndex = -1; 
        for(var i=0; i<feedbackItems.length; i++){
          if(feedbackItems[i].props.action[actionType].key == action[actionType].key) {
            feedbackIndex = i; 
          }
        }

        // Remove the item at that indexx
        if(feedbackIndex > -1) {
          treeNode.subtitle.splice(feedbackIndex, 1);        
        }
      }

      this.setState(state => ({
        treeData: this.state.treeData
      }));      
    }
  }

  getShapeHierarchy() {
    // Not supporting hiearchical trees yet
    let treeNodes = this.state.treeData; 

    // Convert this into a hierarchical structure
    let shapes = [];
    for(var i=0; i<treeNodes.length; i++){
      var treeNode = treeNodes[i]; 
      if(treeNode.children){
        this.getShapeChildren(treeNode); 
      }

      var shape = treeNode.title.props.shape; 

      // Add it to the page level shape
      shapes.push(shape); 
    }

    this.pageLevelShape.children = shapes;
    return this.canvasLevelShape;
  }

  getShapeChildren(node) {
    let shape = node.title.props.shape; 
    shape.children = []; 
    for(var i=0; i<node.children.length; i++){
      let child = node.children[i]; 
      
      // Add the child shape object to the shape children
      let childShape = child.title.props.shape; 
      shape.children.push(childShape); 

      if(child.children){
        this.getShapeChildren(child);
      }
    }
  }


  createConstraintsCanvasShapeObject(type) {  
    // Set up the object that will keep the current state of this shape
    // And be passed with a set of information to the server for solving
    let shape = {
      "name": _.uniqueId(),
      "label": type, 
      "type": type 
    }

    if (type == "group" || type == "labelGroup") {
      shape.children = []; 
    }

    this.constraintsShapesMap[shape["name"]] = shape; 

    return shape;
  }

  calculateRowHeight({treeIndex, node, path}) {
    let rowHeight = 40

    // Row height
    let subtitles = node.subtitle; 
    let numFeedback = subtitles ? subtitles.length : 0; 

    return this.rowPadding + rowHeight + (numFeedback * this.defaultFeedbackHeight); 
  }

  canReparentWidgetNode({node, nextParent, prevPath, nextPath}) {
    if(nextParent == null || (nextParent && (nextParent.title.props.type == "group" || nextParent.title.props.type == "labelGroup"))) {
        return true;
    }

    return false;
  }

  onMoveNode({ treeData, node, nextParentNode, prevPath, prevTreeIndex, nextPath, nextTreeIndex }) {
    // Called whenever a node is moved in the tree
    // Tree updates have already been made by this point so we don't need to do this in a callback
    this.checkSolutionValidity();
  }

  removeWidgetNode(path){
    const getNodeKey = ({ treeIndex }) => treeIndex;

    // Remove the widget from the tree node map
    let treeNode = getNodeAtPath({
        treeData: this.state.treeData, 
        path, 
        getNodeKey,
    }); 

    let shapeID = treeNode.node.title.props.id; 
    delete this.widgetTreeNodeMap[shapeID]; 

    // Delete the entry in the constraints canvas shape map 
    delete this.constraintsShapesMap[shapeID];

    this.setState(state => ({
      treeData: removeNodeAtPath({
        treeData: this.state.treeData, 
        path, 
        getNodeKey,
      })
    }), this.checkSolutionValidity); 
  }

  render () {
    const shapes = this.constraintsShapes; 
    const pageFeedbacks = this.state.pageFeedbackWidgets;
    var self = this;

    // Process the queue of shapes to add to the canvas
	  return (
      <div className="panel-body" id="constraints-canvas-container" tabIndex="1">
        <div className="constraints-canvas-page-feedback">
          {pageFeedbacks}
        </div>
        <div className="widgets-sortable-tree">
          { /*             rowHeight={this.calculateRowHeight.bind(this)} */}
          <SortableTree
            treeData={this.state.treeData}
            onChange={treeData => this.setState({ treeData })}
            canDrop={this.canReparentWidgetNode.bind(this)}
            onMoveNode={this.onMoveNode.bind(this)}
            rowHeight={this.calculateRowHeight.bind(this)}
            generateNodeProps={({node, path}) => ({
              buttons: [
                <button className="widgets-sortable-tree-remove" onClick={function() { self.removeWidgetNode(path); }}>
                  <span className="glyphicon glyphicon-minus" aria-hidden="true"></span>
                </button>
              ]
            })}
          />
        </div>
      </div>
    );
  }
}
