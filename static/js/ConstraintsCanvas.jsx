import React from "react";
import FabricHelpers from './FabricHelpers.js';
import Widget from './Widget';
import SortableTree from 'react-sortable-tree';
import 'react-sortable-tree/style.css'; // This only needs to be imported once in your app

export default class ConstraintsCanvas extends React.Component {
  constructor(props) {
  	super(props); 

    // Bound functions
    this.createConstraintsCanvasShapeObject.bind(this);
    this.addShapeOfTypeToCanvas.bind(this);

    // This collection contains the set of shapes on the constraints canvas
    this.constraintsShapesMap = [];

    this.canvasWidth = 375; 
    this.canvasHeight = 667; 

    this.state = { 
      constraintModified: false, 
      treeData: []
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
    let widget = <Widget key={shapeId} shape={shape} id={shapeId} type={type} />;
    this.setState(state => ({
      treeData: this.state.treeData.concat({
        title: widget
      })
    }));
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

    // Also need to push the shape onto the children of the page level object
    this.pageLevelShape.children.push(shape); 

    return shape;
  }

  deleteShape(shape) {
    // TODO 
  }

  deleteShapeFromObjectChildren(shape, objectJSON) {
    let index = objectJSON.children.indexOf(shape); 
    objectJSON.children.splice(index, 1);   
  }

  selectShape(shape) {
    this.selectedShape = shape; 
  }

  distanceWithin(x1,y1,width1,height1,x2,y2,width2,height2,padding){
    // return the distance between the shapes 
    if(!(x1 > (x2 + width2 + padding) || y1 > (y2 + height2 + padding) || x2 > (x1 + width1 + padding) || y2 > (y1 + height1 + padding))) {
      // They are overlapping 
      return true;
    }

    return false;  
  }

  unparentGroup(group){
    for(let i=0; i<group.children.length; i++) {
      let child = group.children[i]; 
      child.parent = undefined; 

      // TODO: hierarchies of groups
      this.pageLevelShape.children.push(child); 
    }

    this.deleteShapeFromObjectChildren(group, this.pageLevelShape);     
  }

  addShapeToGroup(shape, parent) {
    if(shape.parent){
      // Delete it from the page level children
      this.deleteShapeFromObjectChildren(shape, shape.parent);         
    }

    shape.parent = parent; 
    parent.children.push(shape); 
  }

  // Adds two shapes into a new group and adds the new group to the canvas
  addShapeToNewGroup(shape1, shape2, groupType="group") {
    // // Create a new group for the parent container
    // let group = {
    //   "name": _.uniqueId(),
    //   "type": groupType, 
    //   "children": []
    // }

    // shape1.parent = group; 
    // shape2.parent = group; 
    // group.children.push(shape1); 
    // group.children.push(shape2); 

    // // Remove both children from the page level object
    // this.deleteShapeFromObjectChildren(shape1, this.pageLevelShape); 
    // this.deleteShapeFromObjectChildren(shape2, this.pageLevelShape); 
    // this.pageLevelShape.children.push(group); 

    // // Create a new group shape to be the bounding box 
    // let color = groupType == "labels" ? "red" : "blue";
    // let groupBoundingBox = this.getGroupBoundingBox(group); 
    // let groupRect = FabricHelpers.getGroup(groupBoundingBox.x-10, groupBoundingBox.y-10, groupBoundingBox.width+20, groupBoundingBox.height+20, {
    //   selectable: false, 
    //   stroke: color
    // });

    // group.shape = groupRect; 

    // // Add them to the page collection of shape objects
    // this.constraintsCanvas.add(groupRect); 
    // this.constraintsShapes.push(group); 
    // this.constraintsShapesByName[group["name"]] = group; 

    // // Move the group to the back layer
    // this.constraintsCanvas.sendToBack(groupRect);
  }

  // removeShapeFromGroup(shape, parentGroup){
  //   // Remove the child from this group and update the group bounds
  //   shape.parent = undefined; 
  //   let shapeIndex = parentGroup.children.indexOf(shape); 
  //   parentGroup.children.splice(shapeIndex, 1); 

  //   // Append it back to the page level object children for now (Until we support hierarchies of groups)
  //   this.pageLevelShape.children.push(shape); 
  // }

  canReparentWidgetNode({node, nextParent, prevPath, nextPath}) {
    if(nextParent == null || (nextParent && (nextParent.title.props.type == "group" || nextParent.title.props.type == "labelGroup"))) {
        return true;
    }

    return false;
  }

  render () {
    const shapes = this.constraintsShapes; 
    // Process the queue of shapes to add to the canvas
	  return (
      <div className="panel-body" id="constraints-canvas-container" tabIndex="1">
        <div className="widgets-sortable-tree">
          <SortableTree
            treeData={this.state.treeData}
            onChange={treeData => this.setState({ treeData })}
            canDrop={this.canReparentWidgetNode.bind(this)}
          />
        </div>
      </div>
    );
  }
}
