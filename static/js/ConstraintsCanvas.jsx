import React from "react";
import '../css/ConstraintsCanvas.css'; 
import ConstraintsCanvasSVGWidget from './ConstraintsCanvasSVGWidget';
import ConstraintsCanvasContainerSVGWidget from './ConstraintsCanvasContainerSVGWidget';
import WidgetFeedback from './WidgetFeedback';
import ConstraintActions from './ConstraintActions';
import {
  SortableTreeWithoutDndContext as SortableTree,
  removeNodeAtPath, 
  getNodeAtPath, 
  changeNodeAtPath, 
  defaultGetNodeKey, 
  insertNode,
  getFlatDataFromTree, 
  addNodeUnderParent } 
from 'react-sortable-tree';
import ConstraintsCanvasMenu from './ConstraintsCanvasMenu'; 
import Constants from './Constants';
import WidgetTyping from './WidgetTyping'; 
import group from '../assets/illustrator/groupContainer.svg';
import label from '../assets/illustrator/labelContainer.svg';
import repeatGrid from '../assets/illustrator/repeatGrid.svg';
import item from '../assets/illustrator/item.svg';
import rootNode from '../assets/illustrator/canvas.svg';

// import { Ios11Picker } from 'react-color';
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

    // A bunch of constants
    this.canvasWidth = 375; 
    this.canvasHeight = 667; 
    this.defaultControlWidth = 120; 
    this.defaultControlHeight = 40; 
    this.defaultFeedbackHeight = 40; 
    this.defaultTypingAlertHeight = 86;
    this.rowPadding = 10; 
    this.minimumRowHeight = 40; 
    this.minimumGroupSize = 2; 

    this.state = { 
      treeData: [], 
      pageFeedbackWidgets: [], 
      rightClickMenuShown: false, 
      rightClickMenuCallbacks: undefined, 
      rightClickMenuPosition: {
        x: 0, 
        y: 0
      }, 
      rightClickShapeID: undefined, 
      pageOrder: "unimportant"
    }; 
  }

  componentDidMount() {
    let cachedShapesJSON = localStorage.getItem('shapeHierarchy'); 
    if(!cachedShapesJSON) {
      // } else {
      let rootNode = this.initRootNode();
      this.state.treeData = this.state.treeData.concat(rootNode); 

      this.setState(state => ({
        treeData: this.state.treeData
      }), this.updateShapeCache);
    }
  }

  componentDidUpdate = (prevProps) => {
    if(prevProps.svgWidgets.length != this.props.svgWidgets.length) {
      // SVG widgets have been read from cache. Restore hierarchy from cache
      // Retrieve cached shapes from local storage and repopulate them into the tree
      let cachedShapesJSON = localStorage.getItem('shapeHierarchy');
      let cachedShapes = JSON.parse(cachedShapesJSON);
      this.constructTreeFromCache(cachedShapes);
    }
  }

  checkSolutionValidityAndUpdateCache = () => {
    // Update shapes cache in localStorage
    this.updateShapeCache(); 

    // Check validity of constraints
    this.checkSolutionValidity();
  }

  getActionForWidgetFeedback = (lock, shape) => {
    return ConstraintActions.getAction(lock, shape);
  }

  constructTreeFromCache = (canvasRootShape) => {
    // Restore the cosntraints tree from the cached shapes
    this.canvasLevelShape = canvasRootShape; 
    this.constraintsShapesMap[canvasRootShape.name] = canvasRootShape; 

    if(this.canvasLevelShape.children) {
      this.pageLevelShape = this.canvasLevelShape.children[0]; 
      this.constraintsShapesMap[this.pageLevelShape.name] = this.pageLevelShape; 

      // Create page level widget
      let newTreeData = [];
      let pageWidget = this.getWidget(this.pageLevelShape, rootNode);
      let newTreeNode = {
        title: pageWidget, 
        subtitle: []
      }; 

      this.widgetTreeNodeMap[this.pageLevelShape.name] = newTreeNode; 

      // Restore feedback items
      // Check whether to remove or add a widget feedback item
      if(this.canvasLevelShape.locks && this.canvasLevelShape.locks.length) {
        for(let i=0; i<this.canvasLevelShape.locks.length; i++) {
          let lock = this.canvasLevelShape.locks[i];
          let action = this.getActionForWidgetFeedback(lock, this.canvasLevelShape);
          if(action){
            let uniqueId = _.uniqueId();
            let message = action["do"].getFeedbackMessage(this.canvasLevelShape);
            let id = this.pageLevelShape.name + "_" + uniqueId; 
            let widgetFeedback = this.getWidgetFeedback(id, this.canvasLevelShape, action, message);
            newTreeNode.subtitle.push(widgetFeedback); 
          } 
        }     
      } 

      newTreeData = newTreeData.concat(newTreeNode); 

      if(this.pageLevelShape.children) {
        let parentKey = 0; 
        let nodeIndex = parentKey; 
        for(let i=0; i<this.pageLevelShape.children.length; i++) {
          nodeIndex = nodeIndex + 1; 
          let child = this.pageLevelShape.children[i]; 
          let results = this.constructShapeHierarchy(child, parentKey, nodeIndex, newTreeData);
          newTreeData = results.treeData; 
          nodeIndex = results.nodeIndex; 
        }
      }

      this.setState(state => ({
        treeData: newTreeData
      }));
    }
  }

  getSVGSourceByID = (id) => {
    let svgElements = this.props.svgWidgets; 
    let svgElement = svgElements.filter(element => element.id == id); 
    if(svgElement && svgElement.length) {
      svgElement = svgElement[0]; 
      return svgElement.svgData; 
    }

    return ""; 
  }

  constructShapeHierarchy = (node, parentKey, nodeIndex, treeData) => {
    let source =  this.getSVGSourceByID(node.id);
    let widget = this.getWidget(node, source); 

    let newTreeNode = {
        title: widget, 
        subtitle: []
    }; 

    this.widgetTreeNodeMap[node.name] = newTreeNode; 

    let newTreeData = addNodeUnderParent({
      treeData: treeData, 
      newNode: newTreeNode, 
      parentKey: parentKey, 
      getNodeKey: defaultGetNodeKey, 
      ignoreCollapsed: false, 
      expandParent: true
    }); 

    treeData = newTreeData.treeData; 

    let currNodeIndex = nodeIndex;
    if(node.children && node.children.length) {
      for(let i=0; i<node.children.length; i++){
        currNodeIndex = currNodeIndex + 1; 
        let child = node.children[i]; 
        let results = this.constructShapeHierarchy(child, nodeIndex, currNodeIndex, treeData); 
        treeData = results.treeData; 
        currNodeIndex = results.nodeIndex; 
      }
    }

    return { treeData: treeData, nodeIndex: currNodeIndex }; 
  }

  initRootNode = () => {
    // Create an object to represent the  top level canvas shape
    let canvas = {
      "name": "canvas",
      "type": "canvas", 
      "controlType": "canvas",
      "children": [],
      "x": 0, 
      "y": 0, 
      "size": {
        width: this.canvasWidth, 
        height: this.canvasHeight
      }, 
      "background_color": "#E1E2E1"
    }

    this.canvasLevelShape = canvas;
    this.constraintsShapesMap[canvas.name] = canvas; 
 
    // Create an object to represent the page level object (A container for shapes at the root level)
    let page = {
      "name": "page",
      "type": "page",
      "controlType": "page",
      "x": 0, 
      "y": 0, 
      "size": {
        width: Constants.controlWidths('page'),
        height: Constants.controlHeights('page')
      }, 
      "containerOrder": "important",
      "importance": "normal",
      "children": []
    }

    this.constraintsShapesMap[page.name] = page; 
    this.pageLevelShape = page; 
    canvas.children.push(page); 

    let widget = this.getWidget(page, rootNode); 
    let newTreeNode = {
        title: widget, 
        subtitle: []
    }; 

    this.widgetTreeNodeMap[page.name] = newTreeNode; 
    return newTreeNode; 
  }

  updateShapeCache = () => {
    // Update the entry for the constraintShapesMap in the localStorage cache
    // so we can repopulate the constraints tree on refresh 
    let shapeHierarchy = this.getShapeHierarchy();
    let shapeHierarchyJSON = JSON.stringify(shapeHierarchy); 
    localStorage.setItem('shapeHierarchy', shapeHierarchyJSON); 
  }

  getWidget = (shape, src, options={}) => {
    let shapeId = shape.name;
    let highlighted = options.highlighted ? options.highlighted : false; 
    let isContainer = shape.type == "group" || shape.type == "page" || shape.type == "canvas";

    if(isContainer) {
      let item = options.item ? options.item : false; 
      let typed = options.typed ? options.typed : false;
      return (<ConstraintsCanvasContainerSVGWidget 
                key={shapeId} 
                shape={shape} 
                id={shapeId} 
                source={src}
                highlighted={highlighted}
                isContainer={true}
                checkSolutionValidity={this.checkSolutionValidityAndUpdateCache} 
                displayRightClickMenu={this.displayRightClickMenu}
                hideRightClickMenu={this.hideRightClickMenu}
                createLabelsGroup={this.createLabelsGroup.bind(this)}
                getCurrentShapeSiblings={this.getCurrentShapeSiblings}
                getCurrentShapeIndex={this.getCurrentShapeIndex}
                typed={typed}
                item={item} />);
    }
    return (<ConstraintsCanvasSVGWidget 
              key={shapeId} 
              shape={shape} 
              id={shapeId} 
              source={src}
              highlighted={highlighted}
              checkSolutionValidity={this.checkSolutionValidityAndUpdateCache} 
              displayRightClickMenu={this.displayRightClickMenu}
              hideRightClickMenu={this.hideRightClickMenu}
              createLabelsGroup={this.createLabelsGroup.bind(this)}
              getCurrentShapeSiblings={this.getCurrentShapeSiblings}
              getCurrentShapeIndex={this.getCurrentShapeIndex} />);
  }

  addShapeToCanvas = (id, source, type, width, height) => {
    let shape = this.createConstraintsCanvasShapeObject(id, type, width, height); 

    let widget = this.getWidget(shape, source); 

    let newTreeNode = {
        title: widget, 
        subtitle: []
    }; 

    this.widgetTreeNodeMap[shape.name] = newTreeNode; 

    let parentIndex = 0; 
    let newTreeData = addNodeUnderParent({
      treeData: this.state.treeData, 
      newNode: newTreeNode, 
      parentKey: 0, 
      getNodeKey: defaultGetNodeKey, 
      ignoreCollapsed: false, 
      expandParent: true
    }); 

    this.setState(state => ({
      treeData: newTreeData.treeData, 
    }), this.checkSolutionValidityAndUpdateCache);
  }


  clearShapesFromCanvas = () => {
    let newTreeData = []; 
    let rootNode = this.initRootNode(); 
    newTreeData = newTreeData.concat(rootNode); 
    this.setState({
      treeData: newTreeData
    }, this.updateShapeCache); 
  }

  createNewTreeNode = (type, source, options={}) => {
    // Creates a new tree node widget and returns it
    let id = _.uniqueId();

    let width = Constants.controlWidths(type); 
    let height = Constants.controlHeights(type);
    let shape = this.createConstraintsCanvasShapeObject(id, type, width, height, options); 
    let widget = this.getWidget(shape, source, options); 

    let newTreeNode = {
      title: widget, 
      subtitle: []
    }; 

    this.widgetTreeNodeMap[shape.name] = newTreeNode; 

    return newTreeNode; 
  }

  getWidgetFeedback = (shapeId, parentShape, action, message, highlighted) => {
    return (<WidgetFeedback 
              key={shapeId} 
              type="feedback"
              id={shapeId} 
              parentShape={parentShape}
              action={action}
              message={message} 
              highlighted={highlighted}
              updateConstraintsCanvas={this.updateConstraintsCanvas}/>); 
  }

  getConstraintsCanvasShape = (shapeID) => {
    return this.constraintsShapesMap[shapeID]; 
  }

  displayRightClickMenu = (evt, shapeID, menuCallbacks) => {
    this.setState({
      rightClickMenuShown: true, 
      rightClickMenuCallbacks: menuCallbacks, 
      rightClickMenuPosition: {
        x: evt.clientX, 
        y: evt.clientY
      }, 
      rightClickShapeID: shapeID
    });  
  }


  closeRightClickMenu = (evt) => {
    if(this.state.rightClickMenuShown) {
      this.hideRightClickMenu();
    }
  }

  findShapeSiblings = (shapeId, siblings, node) => {
    // Get the two neighboring siblings for a shape in the tree
    for(let i=0; i<node.length; i++) {
      let treeNode = node[i]; 
      let nodeID = treeNode.title.props.id; 
      if(nodeID == shapeId) {
        if(i < node.length - 1) {
          let nextSibling = node[i+1];
          siblings.next = nextSibling; 
        }

        if(i > 0) {
          let prevSibling = node[i-1]; 
          siblings.prev = prevSibling; 
        }
      }
      else if(treeNode.children) {
        this.findShapeSiblings(shapeId, siblings, treeNode.children); 
      }      
    }
  }

  findShapeIndex = (shapeId, node) => {
    for(let i=0; i<node.length; i++) {
      let treeNode = node[i]; 
      let nodeID = treeNode.title.props.id; 
      if(nodeID == shapeId) {
        return i; 
      }

      if(treeNode.children) {
        let inChildrenIndex = this.findShapeIndex(shapeId, treeNode.children); 
        if(inChildrenIndex != -1) {
          return inChildrenIndex; 
        }        
      }
    } 

    return -1; 
  }

  getSiblingLabelItem = (shapeId) => {
    // Go through tree data (recursive) and find the level of the element
    let node = this.state.treeData; 
    let siblings = this.getCurrentShapeSiblings(shapeId);

    let menuItems = []; 
    if(siblings.next) {
      menuItems.push(siblings.next); 
    }

    return menuItems; 
  }
  
  getCurrentShapeSiblings = (shapeId) => {
    // Go through tree data (recursive) and find the level of the element
    let siblings = {}; 
    let node = this.state.treeData; 
    this.findShapeSiblings(shapeId, siblings, node);

    let siblingItems = {}; 
    if(siblings.next) {
      siblingItems.next = {
        id: siblings.next.title.props.id, 
        label: siblings.next.title.props.shape.label
      }; 
    }

    if(siblings.prev) {
      siblingItems.prev = {
        id: siblings.prev.title.props.id, 
        label: siblings.prev.title.props.shape.label
      }; 
    }

    return siblingItems; 
  }

  getCurrentShapeIndex = (shapeId) => {
    let node = this.state.treeData; 
    return this.findShapeIndex(shapeId, node);
  }

  getCurrentContainerOrder = (shapeId) => {
    let node = this.widgetTreeNodeMap[shapeId]; 
    return node.title.props.shape.containerOrder; 
  }

  getCurrentShapeOrder = (shapeId) => {
    let node = this.widgetTreeNodeMap[shapeId]; 
    return node.title.props.shape.order; 
  }

  getCurrentShapeImportance = (shapeId) => {
    let node = this.widgetTreeNodeMap[shapeId]; 
    return node.title.props.shape.importance; 
  }

  getCurrentShapeType = (shapeId) => {
    let node = this.widgetTreeNodeMap[shapeId]; 
    return node.title.props.shape.type; 
  }
 
  hideRightClickMenu = () => {
    // Recheck consistency of the solutions after any of the things are set
    this.setState({
      rightClickMenuShown: false
    }); 
  }

  highlightAddedWidget = (shapeId, highlighted) => {
    let treeNode = this.widgetTreeNodeMap[shapeId];
    let treeNodeData = this.getPathAndChildrenForTreeNode(treeNode);
    if(treeNodeData) {
      let widget = this.getWidget(treeNode.title.props.shape, treeNode.title.props.source, { highlighted: highlighted }); 

      // Create a new node for the widget
      let newNode = {
        title: widget, 
        subtitle: [], 
        expanded: treeNode.expanded || treeNodeData.expanded, 
        children: treeNodeData.children
      }; 

      // Replace the current node with this new node
      this.state.treeData = changeNodeAtPath({
        treeData: this.state.treeData,
        path: treeNodeData.path,
        getNodeKey: defaultGetNodeKey,
        ignoreCollapsed: false,
        newNode: newNode
      }); 

      this.setState(state => ({
        treeData: this.state.treeData
      }), this.checkSolutionValidityAndUpdateCache); 
    }
  }

  highlightWidgetFeedback = (shapeId, lock, highlighted) => {
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
    for(let i=0; i<feedbackItems.length; i++) {
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

  updateWidgetFeedbacks = (shape, action, actionType) => {    
    // The shape was already updated so we just need to re-render the tree to get the new sizes
    // Add WidgetFeedbackItem to correct item in the tree

    // Find the corresponding tree node
    let shapeId = shape.name; 
    let uniqueId = _.uniqueId();
      
    // Update the canvas shape feedbacks on the same shape as the page level shape. 
    if(shapeId == "canvas") {
      shapeId = "page"; 
    }

    let treeNode = this.widgetTreeNodeMap[shapeId]; 

    // First, see whether there is already a feedback item for this action
    // If there is, remove it, before updating with the new action
    let feedbackItems = treeNode.subtitle; 
    let feedbackIndex = -1; 
    for(let i=0; i<feedbackItems.length; i++){
      if(feedbackItems[i].props.action[actionType].key == action[actionType].key) {
        feedbackIndex = i; 
      }
    }

    // Remove the item at that index
    if(feedbackIndex > -1) {
      treeNode.subtitle.splice(feedbackIndex, 1);        
    }

    // Check whether to remove or add a widget feedback item
    if(actionType == "do") {
      let message = action[actionType].getFeedbackMessage(shape);
      let id = shapeId + "_" + uniqueId; 
      let widgetFeedback = this.getWidgetFeedback(id, shape, action, message);
      treeNode.subtitle.push(widgetFeedback);       
    } 

    this.setState(state => ({
      treeData: this.state.treeData
    }), this.checkSolutionValidityAndUpdateCache);      
  }

  getShapeHierarchy = () => {
    let treeNodes = this.state.treeData; 

    // Convert this into a hierarchical structure
    let shapes = [];
    for(let i=0; i<treeNodes.length; i++){
      let treeNode = treeNodes[i]; 
      if(treeNode.children){
        this.getShapeChildren(treeNode); 
      }

      let shape = treeNode.title.props.shape; 
      if(treeNode.title.props.typed) {
        // If the tree node is a typed group
        // Update the correspondingID list to
        // link the child elemeents with their corresponding shapes
        this.getRepeatGroupMatchingChildren(treeNode); 
        shape.typed = true; 
      }

      // Add it to the page level shape
      shapes.push(shape); 
    }

    this.canvasLevelShape.children = shapes;
    return this.canvasLevelShape;
  }

  getShapeChildren = (node) => {
    let shape = node.title.props.shape; 
    shape.children = []; 
    for(let i=0; i<node.children.length; i++){
      let child = node.children[i]; 

      if(child.title.props.typed) {
        this.getRepeatGroupMatchingChildren(child); 
        child.title.props.shape.typed = true; 
      }

      
      // Add the child shape object to the shape children
      let childShape = child.title.props.shape; 
      shape.children.push(childShape); 

      if(child.children){
        this.getShapeChildren(child);
      }
    }
  }

  getPathAndChildrenForTreeNode = (treeNode) => {
    // Innefficient but is the easiset to implement for now
    // Get all the tree data as a flattened list
    let treeNodeID = treeNode.title.props.shape.name; 
    let flatData = getFlatDataFromTree({
      treeData: this.state.treeData, 
      getNodeKey: defaultGetNodeKey, 
      ignoreCollapsed: false
    }); 

    for(let i=0; i<flatData.length; i++){
      let node = flatData[i]; 
      let nodeItem = node.node; 
      if(nodeItem.title.props.shape && nodeItem.title.props.shape.name == treeNodeID) {
        return { path: node.path, children: node.node.children, treeIndex: node.treeIndex, expanded: nodeItem.expanded }; 
      }
    }

    return { path: [-1], children: [], treeIndex: 0 }; 
  }

  inferShapeType = () => {
    return "button";
  }


  createConstraintsCanvasShapeObject = (id, type, width, height, options={}) => {
    // Optional set of initial properties cna be passed in through the intial object
    let order = options.order ? options.order : -1; 

    let containerOrder = undefined; 

    let isContainer = type == "group" || type == "labelGroup"; 

    if(isContainer) {
      containerOrder = options.containerOrder ? options.containerOrder : "unimportant";
    }

    let importance = (options.importance ? options.importance : "normal");

    // Set up the object that will keep the current state of this shape
    // And be passed with a set of information to the server for solving
    let label = Constants.controlLabels(type); 
    let shape = {
      "name": _.uniqueId(),
      "id": id, 
      "label": label, 
      "type": type,
      "importance": importance, 
      "containerOrder": containerOrder, 
      "order": order, 
      "size": {
        "width": width, 
        "height": height
      }, 
      "x": 0, 
      "y": 0
    }

    if (isContainer) {
      shape.children = []; 
    }

    this.constraintsShapesMap[shape["name"]] = shape; 

    return shape;
  }

  calculateRowHeight = ({treeIndex, node, path}) => {
    let padding = 0; 
    let actualRowHeight = node.title.props.shape.size.height + (padding * 2);
    let nodeElement = node.title.props.shape; 
    let rowHeight = (actualRowHeight < this.minimumRowHeight) ? this.minimumRowHeight : actualRowHeight; 
    let infoHeight = 23 
    let infoShowing = (nodeElement.importance != "normal" || nodeElement.order != -1 || nodeElement.containerOrder);
    rowHeight += (infoShowing ? infoHeight : 0);  

    // Row height
    let feedbackItems = node.subtitle.filter(item => item.props.type == "feedback"); 
    let typingAlert = node.subtitle.filter(item => item.props.type == "typing"); 
    let numFeedback = feedbackItems ? feedbackItems.length : 0; 
    let numTyping = typingAlert ? typingAlert.length : 0; 

    return this.rowPadding + rowHeight + (numFeedback * this.defaultFeedbackHeight) + (numTyping * this.defaultTypingAlertHeight); 
  }

  canReparentWidgetNode = ({node, nextParent, prevPath, nextPath}) => {
    if(nextParent && (nextParent.title.props.isContainer)) {
        if(nextParent.title.props.item) {
          return false;
        }
        return true;
    }

    return false;
  }

  typesMatch = (group1, group2) =>  {
    // Check whether the set of types in each group list match 
    if(group1.length != group2.length) {
      return false;
    }

    for(let i=0; i<group1.length; i++) {
      let item1 = group1[i]; 
      let item2 = group2[i]; 
      if(item1 != item2) {
        return false;
      }
    }

    return true;
  }

  canSplitIntoGroupOfSize = (node, size) => {
    // Determine if the children of this node can be split into a group of the given size
    let pattern = []; 

    // Collect all the types and split them into groups based on the given size
    let currSize = 0; 
    let currGroup = []; 
    for(let i=0; i<node.children.length; i++) {
      let currChild = node.children[i]; 
      currGroup.push(currChild.title.props.shape.type);
      currSize++; 

      if(currSize == size){
        if(currGroup.length) {
          pattern.push(currGroup); 
        }

        currSize = 0; 
        currGroup = []; 
      }
    }

    // Now, verify that each of the subgroups has the exact same set of types
    for(let i=0; i<pattern.length; i++){
      if(i < pattern.length - 1) {
        let patternGroup = pattern[i]; 
        let nextPatternGroup = pattern[i+1]; 
        if(!this.typesMatch(patternGroup, nextPatternGroup)) {
          return false;
        }
      }
    }

    return true; 
  }

  getGroupSizes = (total) => {
    // Get the set of group sizes to check by finding the possible divisors
    let totalFloor = Math.floor(total/2); 
    let sizes = []; 
    for(let i=1; i<=totalFloor; i++) {
      if(total % i == 0){
        sizes.push(i); 
      }
    }

    return sizes;
  }

  checkGroupTyping = (node) => {
    // Do the type inference algorithm
    // iterate through each set of possible groupings starting with the greatest common divisor
    let numChildren = node.children.length; 
    let groupSizes = this.getGroupSizes(numChildren);
    // We want to split into the largest size group, so reverse the order
    groupSizes.reverse();
    for(let i=0; i<groupSizes.length; i++) {
      let groupSize = groupSizes[i];
      if(groupSize >= this.minimumGroupSize) {
        if(this.canSplitIntoGroupOfSize(node, groupSize)) {
          return groupSize;
        }
      }
    }

    return false;
  }

  getRepeatGroupMatchingChildren = (group) => {
    // For a given child, return the shape IDs of the child shapes that are in the
    // corresponding positions in the other group(s)
    let items = group.children; 
    if(items) {
      for(let i=0; i<items.length; i++) {
        let currItem = items[i]; 

        let correspondingBefore = []
        if(i > 0) {
          correspondingBefore = _.range(0, i); 
        }

        let correspondingAfter = []; 
        if(i < items.length - 1) {
          correspondingAfter = _.range(i+1, items.length); 
        }

        let correspondingItems = correspondingBefore.concat(correspondingAfter); 

        let itemChildren = currItem.children; 
        if(itemChildren) {
          for(let j=0; j<itemChildren.length; j++) {
            let itemChild = itemChildren[j]; 

            let correspondingIDs = []; 
            for(let k=0; k<correspondingItems.length; k++) {
              let correspondingItem = items[correspondingItems[k]]; 
              let matchingItem = correspondingItem.children[j]; 
              correspondingIDs.push(matchingItem.title.props.id);
            }

            itemChild.title.props.shape.correspondingIDs = correspondingIDs; 
          }
        }
      }
    }
  }

  restructureRepeatGroupChildren = (groupChildren, groupSize) => {
    // Split the children of this group node into uniformly sized groups 
    let curr = 0; 
    let currGroup = []; 
    let groups = []; 
    for(let i=0; i<groupChildren.length; i++) {
      currGroup.push(groupChildren[i]); 
      curr++; 

      if(curr == groupSize) {
        groups.push(currGroup);
        currGroup = [];
        curr = 0;  
      }
    }

    // For each group of children, create a new group node in the tree, and return these groups as 
    // the new children 
    let newChildren = []; 
    for(let i=0; i<groups.length; i++) {
      let currGroup = groups[i]; 
      let newGroupNode = this.createNewTreeNode("group", item, { item: true }); 
      let isExpanded = (i == 0) ? true : false; 
      newGroupNode.expanded = isExpanded; 
      newGroupNode.children = currGroup; 
      newChildren.push(newGroupNode); 
    }

    return newChildren; 
  }

  createRepeatGroup = (groupID, typed, groupSize) => {
    return () => {
      let groupNode = this.widgetTreeNodeMap[groupID];
      let groupNodeData = this.getPathAndChildrenForTreeNode(groupNode);
      if(groupNodeData) {
        let widget = this.getWidget(groupNode.title.props.shape, repeatGrid, { typed: true }); 
        let newGroupChildren = this.restructureRepeatGroupChildren(groupNodeData.children, groupSize); 

        // Create a new node for the widget
        let newNode = {
          title: widget, 
          subtitle: [], 
          expanded: true, 
          children: newGroupChildren
        }; 

        // Replace the current node with this new node
        this.state.treeData = changeNodeAtPath({
          treeData: this.state.treeData,
          path: groupNodeData.path,
          getNodeKey: defaultGetNodeKey,
          ignoreCollapsed: false,
          newNode: newNode
        }); 

        this.setState(state => ({
          treeData: this.state.treeData
        }), this.checkSolutionValidityAndUpdateCache); 
      }
    }
  }

  closeTypingAlert = (groupID) => {
    return () => {
      // Close the group typing alert dialog without doing anything. 
      let treeNode = this.widgetTreeNodeMap[groupID]; 
      // Remove the typing dialog from the group
      if(treeNode && treeNode.subtitle && treeNode.subtitle.length) {
        let subtitleNode = treeNode.subtitle[0]; 
        if(subtitleNode.props.type == "typing") {
          treeNode.subtitle.splice(0,1);       
        }
      }

      this.setState(state => ({
        treeData: this.state.treeData
      }));       
    }
  }

  getWidgetTyping = (key, groupID, groupSize) => {
    return (<WidgetTyping 
      key={key} type="typing" 
      groupID={groupID} 
      groupSize={groupSize}
      createRepeatGroup={this.createRepeatGroup} 
      closeTypingAlert={this.closeTypingAlert} />); 
  }

  createLabelsGroup = (labelID, labeledID) => {
    // Create a new group in the hierarchy to contain the labeled shape and the label shape 
    let labelNode = this.widgetTreeNodeMap[labelID]; 
    let labeledNode = this.widgetTreeNodeMap[labeledID]; 
    let labelNodeData = this.getPathAndChildrenForTreeNode(labelNode); 
    let labeledNodeData = this.getPathAndChildrenForTreeNode(labeledNode);
    if(labelNodeData && labeledNodeData) {
      // Remove labeled node from the tree before re-adding to the labels group
      this.state.treeData = removeNodeAtPath({
        treeData: this.state.treeData, 
        path: labeledNodeData.path, 
        getNodeKey: defaultGetNodeKey,
      }); 
      
      // Create a new labelGroup element. The order should be important so the label always appears first in reading order. 
      // Have to set the children on the object here when creating a new node
      labeledNode.children = labeledNodeData.children; 

      let newLabelGroupNode = this.createNewTreeNode("labelGroup", label, { containerOrder: "important" }); 
      newLabelGroupNode.expanded = true; 
      newLabelGroupNode.children = [labelNode, labeledNode]; 

      // Replace the current node with this new node
      this.state.treeData = changeNodeAtPath({
        treeData: this.state.treeData,
        path: labelNodeData.path,
        getNodeKey: defaultGetNodeKey,
        ignoreCollapsed: false,
        newNode: newLabelGroupNode
      }); 
    }
  }

  removeTypedGroup = (groupNode) => {
   // Ungroup childen from the item containers
    let children = groupNode.children; 
    if(children) {
      for(let i=0; i<children.length; i++){
        let child = children[i]; 
        if(child.title.props.item) {
          let nodePath = this.getPathAndChildrenForTreeNode(child); 

          this.state.treeData = removeNodeAtPath({
            treeData: this.state.treeData, 
            path: nodePath.path, 
            getNodeKey: defaultGetNodeKey,
          }); 

          // Remove the children of the item and place
          // at the parent level
          let itemChildren = child.children; 
          if(itemChildren) {
            let startingIndex = nodePath.treeIndex; 
            for(let i=0; i<itemChildren.length; i++) {
              let itemChild = itemChildren[i]; 
              // Reinsert the children at the item node level
              let result = insertNode({
                treeData: this.state.treeData, 
                depth: nodePath.path.length - 1, 
                minimumTreeIndex: startingIndex, 
                newNode: itemChild, 
                getNodeKey: defaultGetNodeKey, 
                ignoreCollapsed: false, 
                expandParent: true
              });  

              if(result.treeData) {
                this.state.treeData = result.treeData; 
              }                     

              startingIndex += 1; 
            }
          }
        }
      }
    }

    // once children have been restructured, replace
    // the group container with a regular group container
    this.replaceTypedGroup(groupNode); 
  }

  replaceTypedGroup = (groupNode) => {
    let groupNodeData = this.getPathAndChildrenForTreeNode(groupNode);
    if(groupNodeData) {
      let shape = groupNode.title.props.shape; 
      shape.typed = false; 

      let widget = this.getWidget(shape, group); 

      // Create a new node for the widget
      let newNode = {
        title: widget, 
        subtitle: [], 
        expanded: true, 
        children: groupNodeData.children
      }; 

      // Replace the current node with this new node
      this.state.treeData = changeNodeAtPath({
        treeData: this.state.treeData,
        path: groupNodeData.path,
        getNodeKey: defaultGetNodeKey,
        ignoreCollapsed: false,
        newNode: newNode
      }); 
    }
  }

  onMoveNode = ({ treeData, node, nextParentNode, prevPath, prevTreeIndex, nextPath, nextTreeIndex }) => {
    // If the node was moved into group, check whether group typing should be applied. 
    if(nextParentNode) {
      if(nextParentNode.title.props.shape.type == "group") {
        this.removeWidgetTypingAlert(nextParentNode);
        if(nextParentNode.title.props.typed) {
          // The group is already typed. 
          // Remove the group typing 
          // Check first whether the widget typing alert has already been activated for this group
          this.removeTypedGroup(nextParentNode);
        } 

        let groupSize = this.checkGroupTyping(nextParentNode); 
        let parentID = nextParentNode.title.props.shape.name; 

          // Find the group in the tree, remove it, and display the label to apply the typing
        if(groupSize >= this.minimumGroupSize) {
          let typingIndex = 0; 
          let widgetTypingElement = this.getWidgetTyping(typingIndex, parentID, groupSize); 
          nextParentNode.subtitle.unshift(widgetTypingElement);
        }   

        this.setState(state => ({
          treeData: this.state.treeData
        }), this.checkSolutionValidityAndUpdateCache); 
      }
    }

    // Remove the widget from the tree node map
    let prevParentPath = prevPath.slice(0, prevPath.length-1);
    let prevParentNode = getNodeAtPath({
        treeData: this.state.treeData, 
        path: prevParentPath, 
        getNodeKey: defaultGetNodeKey,
    }); 

    // If the previous node was a typed group or item, remove the typing
    // Also remove the alert if it was showin
    prevParentNode = prevParentNode.node; 
    if(prevParentNode && prevParentNode.title.props.shape.type == "group") {
      this.removeWidgetTypingAlert(prevParentNode); 

      if(prevParentNode.title.props.typed) {
        this.removeTypedGroup(prevParentNode); 
      }
      else if(prevParentNode.title.props.item) {
        let typedGroupPath = prevParentPath.slice(0, prevParentPath.length-1); 
        let typedGroupNode = getNodeAtPath({
          treeData: this.state.treeData, 
          path: typedGroupPath, 
          getNodeKey: defaultGetNodeKey
        }); 

        this.removeTypedGroup(typedGroupNode.node);
      }
    }
  }

  removeWidgetTypingAlert = (node) => {
    if(node.subtitle && node.subtitle.length) {
      let firstSubtitle = node.subtitle[0]; 
      if(firstSubtitle.props.type == "typing") {
        // Splice out the typing message that is already there, and replace it with a new one to keep the current group size. 
        node.subtitle.splice(0,1);
      }
    }
  }

  removeWidgetNode = (path) => { 
    return () => {
      const getNodeKey = ({ treeIndex }) => treeIndex;

      // Remove the widget from the tree node map
      let treeNode = getNodeAtPath({
          treeData: this.state.treeData, 
          path: path, 
          getNodeKey: defaultGetNodeKey,
      }); 

      this.state.treeData = removeNodeAtPath({
        treeData: this.state.treeData, 
        path, 
        getNodeKey,
      })

      // Check if the parent node is an item or a typed group 
      // If it is either an item or typed group
      // Remove the typed group and unparent the children 
      // from the item groups. 
      let parentPath = path.slice(0, path.length-1); 
      if(parentPath.length) {
        let parentNode = getNodeAtPath({
          treeData: this.state.treeData, 
          path: parentPath, 
          getNodeKey: defaultGetNodeKey
        }); 

        if(parentNode.node.title.props.typed) {
          if(parentNode.node.children.length == 1) {
            this.removeTypedGroup(parentNode.node); 
          }
        }
        else if(parentNode.node.title.props.item) {
          let typedGroupPath = parentPath.slice(0, parentPath.length-1); 
          let typedGroupNode = getNodeAtPath({
            treeData: this.state.treeData, 
            path: typedGroupPath, 
            getNodeKey: defaultGetNodeKey
          }); 

          this.removeTypedGroup(typedGroupNode.node);
        }
        else if(parentNode.node.title.props.isContainer) {
          // Hide the typing alert that was shown on the container, if there is one
          this.removeWidgetTypingAlert(parentNode.node);
        }
      }

      // Remove from the global map of widgets
      let shapeID = treeNode.node.title.props.id; 
      delete this.widgetTreeNodeMap[shapeID]; 

      // Delete the entry in the constraints canvas shape map 
      delete this.constraintsShapesMap[shapeID];

      this.setState(state => ({
        treeData: this.state.treeData,
      }), this.checkSolutionValidityAndUpdateCache); 
    }
  }

  getNodeProps = ({node, path}) => {
    if(path.length == 1 && path[0] == 0) {
      return {}; 
    }
    else {
      return {
        buttons: [
          <button 
            className="widgets-sortable-tree-remove"  
            onClick={this.removeWidgetNode(path)}>
            <span className="glyphicon glyphicon-minus" aria-hidden="true"></span>
          </button>
        ]
      }; 
    }
  }

  render () {
    console.log("Render ConstraintsCanvas");
    const shapes = this.constraintsShapes; 
    const pageFeedbacks = this.state.pageFeedbackWidgets;
    const rightClickMenuPosition = this.state.rightClickMenuPosition; 
    const rightClickMenu = (this.state.rightClickMenuShown ?
     <ConstraintsCanvasMenu 
      left={rightClickMenuPosition.x} 
      top={rightClickMenuPosition.y} 
      menuCallbacks={this.state.rightClickMenuCallbacks}
      shapeID={this.state.rightClickShapeID}
      getSiblingLabelItem={this.getSiblingLabelItem}
      getCurrentShapeIndex={this.getCurrentShapeIndex}
      getCurrentShapeOrder={this.getCurrentShapeOrder}
      getCurrentContainerOrder={this.getCurrentContainerOrder}
      getCurrentShapeSiblings={this.getCurrentShapeSiblings}
      getCurrentShapeType={this.getCurrentShapeType}
      getCurrentShapeImportance={this.getCurrentShapeImportance}  /> : undefined);
    // const colorPicker = (this.state.colorPickerShown ? <Ios11Picker onChangeComplete={this.updateBackgroundColor} /> : undefined);  
    // const colorPickerPosition = this.state.colorPickerPosition; 
    const pageOrder = this.state.pageOrder; 

    // Process the queue of shapes to add to the canvas
	  return (
       <div className="panel panel-primary constraints-container">
          <div className="panel-heading"> 
            <h3 className="panel-title">Outline</h3>
          </div>
          <div id="constraints-canvas-container" tabIndex="1" className="constraints-canvas-container panel-body"> 
            <div className="constraints-canvas-page-feedback">
              {pageFeedbacks}
            </div>
            <div className={(!rightClickMenu ? "hidden" : "")}> 
              {rightClickMenu}
            </div>
            <div className="widgets-sortable-tree">
              <SortableTree
                treeData={this.state.treeData}
                onChange={treeData => this.setState({ treeData })}
                canDrop={this.canReparentWidgetNode}
                onMoveNode={this.onMoveNode}
                rowHeight={this.calculateRowHeight}
                // isVirtualized={false}
                generateNodeProps={this.getNodeProps}
              />
            </div>
          </div>
      </div>
    );
  }
}
