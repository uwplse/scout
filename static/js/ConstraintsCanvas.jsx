import React from "react";
import FabricHelpers from './FabricHelpers.js';
import Widget from './Widget';
import WidgetFeedback from './WidgetFeedback';
import SortableTree, { removeNodeAtPath, getNodeAtPath } from 'react-sortable-tree';
import 'react-sortable-tree/style.css'; // This only needs to be imported once in your app

export default class ConstraintsCanvas extends React.Component {
  constructor(props) {
  	super(props); 

    // This collection contains the set of shapes on the constraints canvas
    this.constraintsShapesMap = [];
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

  addShapeOfTypeToCanvas(type) {
    let shape = this.createConstraintsCanvasShapeObject(type); 

    let shapeId = shape["name"];
    let widget = <Widget key={shapeId} shape={shape} id={shapeId} type={type} height={this.defaultControlHeight} width={this.defaultControlWidth}/>;

    let newTreeNode = {
        title: widget, 
        subtitle: []
    }; 

    this.widgetTreeNodeMap[shapeId] = newTreeNode; 
    this.setState(state => ({
      treeData: this.state.treeData.concat(newTreeNode)
    }));
  }

  updateWidgetFeedbacks(shape, action, actionType) {    
    // The shape was already updated so we just need to re-render the tree to get the new sizes
    // Add WidgetFeedbackItem to correct item in the tree

    // Find the corresponding tree node
    let shapeId = shape.name; 
    let uniqueId = _.uniqueId();

    if(shape.type == "page") {
      // Add the feedback widgets to the page level instead
      if(actionType == "do") {
        let message = action.getFeedbackMessage(shape);
        let widgetFeedback = <WidgetFeedback key={shapeId + "_" + uniqueId} feedbackKey={action.key} message={message} />; 
        this.state.pageFeedbackWidgets.push(widgetFeedback);   
      }else {
        // Remove the feedback widget from the page level
        let feedbackItems = this.state.pageFeedbackWidgets; 
        let feedbackIndex = -1; 
        for(var i=0; i<feedbackItems.length; i++){
          if(feedbackItems[i].props.feedbackKey == action.key) {
            feedbackIndex = i; 
          }
        }

        if(feedbackIndex > -1) {
          this.state.pageFeedbackWidgets.splice(feedbackIndex, 1);
        }
      }

      this.setState(state => ({
        pageFeedbacks: this.state.pageFeedbackWidgets
      })); 
    } else {
      let treeNode = this.widgetTreeNodeMap[shapeId]; 

      // Check whether to remove or add a widget feedback item
      if(actionType == "do") {
        let message = action.getFeedbackMessage(shape);
        let widgetFeedback = <WidgetFeedback key={shapeId + "_" + uniqueId} feedbackKey={action.key} message={message} />; 
        treeNode.subtitle.push(widgetFeedback);       
      } else {
        // Remove the corresponding widget feedback item
        let feedbackItems = treeNode.subtitle; 
        let feedbackIndex = -1; 
        for(var i=0; i<feedbackItems.length; i++){
          if(feedbackItems[i].props.feedbackKey == action.key) {
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

  linkSolutionShapesToConstraintShapes(elements) {
    for(var i=0; i<elements.length; i++) {
      let element = elements[i]; 
      let elementName = element["name"]; 
      element.constraintsCanvasShape = this.constraintsShapesMap[elementName];
    }
    return elements; 
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
    let rowHeight = node.title.props.height; 

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
    })); 
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
          <SortableTree
            treeData={this.state.treeData}
            onChange={treeData => this.setState({ treeData })}
            canDrop={this.canReparentWidgetNode.bind(this)}
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
