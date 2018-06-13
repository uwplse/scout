import React from "react";
import SVGWidget from './SVGWidget';
import WidgetFeedback from './WidgetFeedback';
import SortableTree, { removeNodeAtPath, getNodeAtPath, changeNodeAtPath, defaultGetNodeKey, getFlatDataFromTree, addNodeUnderParent } from 'react-sortable-tree';
import RightClickMenu from './RightClickMenu'; 
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

    // Method bindings
    this.displayRightClickMenu = this.displayRightClickMenu.bind(this);
    this.hideRightClickMenu = this.hideRightClickMenu.bind(this); 
    // this.displayColorPicker = this.displayColorPicker.bind(this);
    this.updateBackgroundColor = this.updateBackgroundColor.bind(this);
    this.findShapeSiblings = this.findShapeSiblings.bind(this);
    this.getSiblingLabelItem = this.getSiblingLabelItem.bind(this);
    this.getCurrentShapeIndex = this.getCurrentShapeIndex.bind(this);
    this.getCurrentShapeOrder = this.getCurrentShapeOrder.bind(this);
    this.getCurrentShapeSiblings = this.getCurrentShapeSiblings.bind(this);
    this.getCurrentShapeImportance = this.getCurrentShapeImportance.bind(this);
    this.createLabelsGroup = this.createLabelsGroup.bind(this);
    this.onMoveNode = this.onMoveNode.bind(this);
    this.createRepeatGroup = this.createRepeatGroup.bind(this);
    this.closeTypingAlert = this.closeTypingAlert.bind(this); 
    this.togglePageOrder = this.togglePageOrder.bind(this);

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
      showImportanceLevels: false, 
      pageOrder: "unimportant"
    }; 
  }

  componentDidMount() {
    // Create an object to represent the  top level canvas shape
    let canvas = {
      "name": _.uniqueId(),
      "type": "canvas", 
      "controlType": "canvas",
      "children": [],
      "location": {
        x: 0, 
        y: 0
      }, 
      "size": {
        width: this.canvasWidth, 
        height: this.canvasHeight
      }, 
      "background": "#ffffff" 
    }

    this.canvasLevelShape = canvas;
    this.constraintsShapesMap[canvas.name] = canvas; 
 
    // Create an object to represent the page level object (A container for shapes at the root level)
    let page = {
      "name": _.uniqueId(),
      "type": "page",
      "controlType": "page",
      "location": {
        x: 0, 
        y: 0
      }, 
      "size": {
        width: SVGWidget.initialWidths("page"),
        height: SVGWidget.initialHeights("page")
      }, 
      "containerOrder": "unimportant",
      "children": []
    }

    this.constraintsShapesMap[page.name] = page; 
    this.pageLevelShape = page; 
    canvas.children.push(page); 

    let widget = this.getWidget(this.pageLevelShape, rootNode); 
    let newTreeNode = {
        title: widget, 
        subtitle: []
    }; 

    this.widgetTreeNodeMap[page.name] = newTreeNode; 
    this.state.treeData = this.state.treeData.concat(newTreeNode); 

    this.setState(state => ({
      treeData: this.state.treeData
    }));
  }

  togglePageOrder(newOrder) {
    this.pageLevelShape.containerOrder = newOrder; 

    this.setState({
      pageOrder: newOrder
    });
  }

  getWidget(shape, src, options={}) {
    let shapeId = shape.name;
    let typedGroup = options.typedGroup ?  options.typedGroup : false;  
    let highlighted = options.highlighted ? options.highlighted : false;
    return (<SVGWidget 
              key={shapeId} 
              shape={shape} 
              id={shapeId} 
              source={src}
              highlighted={highlighted}
              typedGroup={typedGroup}
              showImportanceLevels={this.state.showImportanceLevels}
              checkSolutionValidity={this.checkSolutionValidity} 
              displayRightClickMenu={this.displayRightClickMenu}
              hideRightClickMenu={this.hideRightClickMenu}
              createLabelsGroup={this.createLabelsGroup} />);
  }

  addShapeOfTypeToCanvas(type, controlType, source) {
    let shape = this.createConstraintsCanvasShapeObject(type, controlType); 
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
    }), this.checkSolutionValidity);
  }

  createNewTreeNode(type, controlType, source, options={}) {
    // Creates a new tree node widget and returns it
    let shape = this.createConstraintsCanvasShapeObject(type, controlType, options); 
    let widget = this.getWidget(shape, source); 

    let newTreeNode = {
      title: widget, 
      subtitle: []
    }; 

    this.widgetTreeNodeMap[shape.name] = newTreeNode; 

    return newTreeNode; 
  }

  getWidgetFeedback(shapeId, parentShape, action, message, highlighted){
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

  getConstraintsCanvasShape(shapeID) {
    return this.constraintsShapesMap[shapeID]; 
  }

  displayRightClickMenu(evt, shapeID, menuCallbacks) {
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


  closeRightClickMenu(evt) {
    if(this.state.rightClickMenuShown) {
      this.hideRightClickMenu();
    }
  }

  findShapeNextSibling(shapeId, siblings, node) {
    // Get the two neighboring siblings for a shape in the tree
    for(var i=0; i<node.length; i++) {
      let treeNode = node[i]; 
      let nodeID = treeNode.title.props.id; 
      if(nodeID == shapeId) {
        if(i < node.length - 1) {
          let nextSibling = node[i+1];
          siblings.next = nextSibling; 
        }
      }
      else if(treeNode.children) {
        this.findShapeNextSibling(shapeId, siblings, treeNode.children); 
      }      
    }
  }

  findShapeIndex(shapeId, node) {
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

  getSiblingLabelItem(shapeId) {
    // Go through tree data (recursive) and find the level of the element
    let siblings = {}; 
    let node = this.state.treeData; 
    this.findShapeNextSibling(shapeId, siblings, node);

    let menuItems = []; 
    if(siblings.next) {
      menuItems.push({
        id: siblings.next.title.props.id, 
        label: siblings.next.title.props.shape.label
      }); 
    }

    return menuItems; 
  }

  findShapeSiblings(shapeId, node) {
    // Get the two neighboring siblings for a shape in the tree
    for(var i=0; i<node.length; i++) {
      let treeNode = node[i]; 
      let nodeID = treeNode.title.props.id; 
      if(nodeID == shapeId) {
        return node; 
      }
      else if(treeNode.children) {
        let siblings = this.findShapeSiblings(shapeId, treeNode.children); 
        if(siblings) {
          return siblings; 
        }
      }      
    }

    return undefined; 
  }

  getCurrentShapeIndex(shapeId) {
    let node = this.state.treeData; 
    return this.findShapeIndex(shapeId, node);
  }

  getCurrentShapeOrder(shapeId) {
    let node = this.widgetTreeNodeMap[shapeId]; 
    return node.title.props.shape.containerOrder; 
  }

  getCurrentShapeImportance(shapeId) {
    let node = this.widgetTreeNodeMap[shapeId]; 
    return node.title.props.shape.importance; 
  }

  getCurrentShapeSiblings(shapeId) {
    let node = this.state.treeData; 
    return this.findShapeSiblings(shapeId, node); 
  }
 
  updateBackgroundColor(color) {
    let backgroundElement = document.getElementById("constraints-canvas-container");
    backgroundElement.style.backgroundColor = color.hex; 

    // When the canvas level background color changes, update the canvas level object
    this.canvasLevelShape.background = color.hex; 

    this.setState({
      colorPickerShown: false
    });   
  }

  hideRightClickMenu() {
    // Recheck consistency of the solutions after any of the things are set
    this.setState({
      rightClickMenuShown: false
    }); 
  }

  highlightAddedWidget(shapeId, highlighted) {
    let treeNode = this.widgetTreeNodeMap[shapeId];
    let treeNodeData = this.getPathAndChildrenForTreeNode(treeNode);
    if(treeNodeData) {
      let widget = this.getWidget(treeNode.title.props.shape, treeNode.title.props.source, { highlighted: highlighted }); 

      // Create a new node for the widget
      let newNode = {
        title: widget, 
        subtitle: []
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
      }), this.checkSolutionValidity); 
    }
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

        // Remove the item at that index
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

    this.canvasLevelShape.children = shapes;
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

  getPathAndChildrenForTreeNode(treeNode) {
    // Innefficient but is the easiset to implement for now
    // Get all the tree data as a flattened list
    let treeNodeID = treeNode.title.props.shape.name; 
    let flatData = getFlatDataFromTree({
      treeData: this.state.treeData, 
      getNodeKey: defaultGetNodeKey, 
      ignoreCollapsed: false
    }); 

    for(var i=0; i<flatData.length; i++){
      let node = flatData[i]; 
      let nodeItem = node.node; 
      if(nodeItem.title.props.shape && nodeItem.title.props.shape.name == treeNodeID) {
        return { path: node.path, children: node.node.children }; 
      }
    }

    return { path: [-1], children: [] }; 
  }


  createConstraintsCanvasShapeObject(type, controlType, options={}) {
    // Optional set of initial properties cna be passed in through the intial object
    let order = options.order ? options.order : -1; 

    let containerOrder = undefined; 
    if(type == "group" || type == "labelGroup") {
      containerOrder = options.containerOrder ? options.containerOrder : "unimportant";
    }

    let importance = (options.importance ? options.importance : "normal");
    let width = options.width ? options.width : SVGWidget.initialWidths(controlType); 
    let height = options.height ? options.height : SVGWidget.initialHeights(controlType); 

    // Set up the object that will keep the current state of this shape
    // And be passed with a set of information to the server for solving
    let label = SVGWidget.initialLabels(type); 
    let shape = {
      "name": _.uniqueId(),
      "label": label, 
      "type": type,
      "controlType": controlType, 
      "importance": importance, 
      "containerOrder": containerOrder, 
      "order": order, 
      "size": {
        "width": width, 
        "height": height
      }
    }

    if (type == "group" || type == "labelGroup") {
      shape.children = []; 
    }

    this.constraintsShapesMap[shape["name"]] = shape; 

    return shape;
  }

  calculateRowHeight({treeIndex, node, path}) {
    let padding = 0; 
    let actualRowHeight = node.title.props.shape.size.height + (padding * 2);
    let nodeElement = node.title.props.shape; 
    let rowHeight = (actualRowHeight < this.minimumRowHeight) ? this.minimumRowHeight : actualRowHeight; 
    let infoHeight = 23; 
    let infoShowing = (nodeElement.importance != "normal" || nodeElement.order != -1 || nodeElement.containerOrder);
    rowHeight += (infoShowing ? infoHeight : 0);  

    // Row height
    let feedbackItems = node.subtitle.filter(item => item.props.type == "feedback"); 
    let typingAlert = node.subtitle.filter(item => item.props.type == "typing"); 
    let numFeedback = feedbackItems ? feedbackItems.length : 0; 
    let numTyping = typingAlert ? typingAlert.length : 0; 

    return this.rowPadding + rowHeight + (numFeedback * this.defaultFeedbackHeight) + (numTyping * this.defaultTypingAlertHeight); 
  }

  canReparentWidgetNode({node, nextParent, prevPath, nextPath}) {
    if(nextParent == null || (nextParent && (nextParent.title.props.shape.type == "group" || nextParent.title.props.shape.type == "labelGroup"))) {
        return true;
    }

    return false;
  }

  typesMatch(group1, group2) {
    // Check whether the set of types in each group list match 
    if(group1.length != group2.length) {
      return false;
    }

    for(var i=0; i<group1.length; i++) {
      let item1 = group1[i]; 
      let item2 = group2[i]; 
      if(item1 != item2) {
        return false;
      }
    }

    return true;
  }

  canSplitIntoGroupOfSize(node, size) {
    // Determine if the children of this node can be split into a group of the given size
    let pattern = []; 

    // Collect all the types and split them into groups based on the given size
    let currSize = 0; 
    let currGroup = []; 
    for(var i=0; i<node.children.length; i++) {
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
    for(var i=0; i<pattern.length; i++){
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

  getGroupSizes(total) {
    // Get the set of group sizes to check by finding the possible divisors
    let totalFloor = Math.floor(total/2); 
    let sizes = []; 
    for(var i=1; i<=totalFloor; i++) {
      if(total % i == 0){
        sizes.push(i); 
      }
    }

    return sizes;
  }

  checkGroupTyping(node) {
    // Do the type inference algorithm
    // iterate through each set of possible groupings starting with the greatest common divisor
    let numChildren = node.children.length; 
    let groupSizes = this.getGroupSizes(numChildren);
    // We want to split into the largest size group, so reverse the order
    groupSizes.reverse();
    for(var i=0; i<groupSizes.length; i++) {
      let groupSize = groupSizes[i];
      if(groupSize >= this.minimumGroupSize) {
        if(this.canSplitIntoGroupOfSize(node, groupSize)) {
          return groupSize;
        }
      }
    }

    return false;
  }

  getRepeatGroupMatchingChildren(childIndex, groupChildren, groupSize) {
    // For a given child, return the shape IDs of the child shapes that are in the
    // corresponding positions in the other group(s)
    var correspondingIDs = []; 
    var index = childIndex - groupSize; 
    while(index >= 0) {
      var correspondingChild = groupChildren[index]; 
      var correspondingChildID = correspondingChild.title.props.id; 
      correspondingIDs.push(correspondingChildID); 
      index = index - groupSize; 
    }

    index = childIndex + groupSize; 
    while(index < groupChildren.length) {
      var correspondingChild = groupChildren[index]; 
      var correspondingChildID = correspondingChild.title.props.id; 
      correspondingIDs.push(correspondingChildID);
      index = index + groupSize; 
    }

    return correspondingIDs; 
  }

  restructureRepeatGroupChildren(groupChildren, groupSize) {
    // Split the children of this group node into uniformly sized groups 
    let curr = 0; 
    let currGroup = []; 
    let groups = []; 
    for(var i=0; i<groupChildren.length; i++) {
      // TODO: Refactor at some point to just update the React objects instead of keeping around this extra
      // object to maintain the metadata for the solver
      let correspondingChildrenIDs = this.getRepeatGroupMatchingChildren(i, groupChildren, groupSize); 
      groupChildren[i].title.props.shape.correspondingIDs = correspondingChildrenIDs; 
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
    for(var i=0; i<groups.length; i++) {
      let currGroup = groups[i]; 
      let newGroupNode = this.createNewTreeNode("group", "group", item); 
      let isExpanded = (i == 0) ? true : false; 
      newGroupNode.expanded = isExpanded; 
      newGroupNode.children = currGroup; 
      newChildren.push(newGroupNode); 
    }

    return newChildren; 
  }

  createRepeatGroup(groupID, typed, groupSize){
    let groupNode = this.widgetTreeNodeMap[groupID];
    let groupNodeData = this.getPathAndChildrenForTreeNode(groupNode);
    if(groupNodeData) {
      let widget = this.getWidget(groupNode.title.props.shape, repeatGrid, { typedGroup: typed }); 
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
      }), this.checkSolutionValidity); 
    }
  }

  closeTypingAlert(groupID) {
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

  getWidgetTyping(key, groupID, groupSize){
    return (<WidgetTyping 
      key={key} type="typing" 
      groupID={groupID} 
      groupSize={groupSize}
      createRepeatGroup={this.createRepeatGroup} 
      closeTypingAlert={this.closeTypingAlert} />); 
  }

  createLabelsGroup(labelID, labeledID) {
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
      let newLabelGroupNode = this.createNewTreeNode("labelGroup", "labelGroup", label, { containerOrder: "important" }); 
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

  onMoveNode({ treeData, node, nextParentNode, prevPath, prevTreeIndex, nextPath, nextTreeIndex }) {
    // If the node was moved into group, check whether group typing should be applied. 
    if(nextParentNode) {
      if(nextParentNode.title.props.shape.type == "group") {
        // Check first whether the widget typing alert has already been activated for this group
        if(nextParentNode.subtitle && nextParentNode.subtitle.length) {
          let firstSubtitle = nextParentNode.subtitle[0]; 
          if(firstSubtitle.props.type == "typing") {
            // Splice out the typing message that is already there, and replace it with a new one to keep the current group size. 
            nextParentNode.subtitle.splice(0,1);
          }
        }

        let groupSize = this.checkGroupTyping(nextParentNode); 
        let parentID = nextParentNode.title.props.shape.name; 

          // Find the group in the tree, remove it, and display the label to apply the typing
        if(groupSize >= this.minimumGroupSize) {
          let typingIndex = 0; 
          let widgetTypingElement = this.getWidgetTyping(typingIndex, parentID, groupSize); 
          nextParentNode.subtitle.unshift(widgetTypingElement);

          this.setState(state => ({
            treeData: this.state.treeData
          }), this.checkSolutionValidity); 
        }
        else {
          // TODO: Remove the corresponding WidgetTyping item from the subtitle area of the node
        }
      }
    }
  }

  removeWidgetNode(path){
    const getNodeKey = ({ treeIndex }) => treeIndex;

    // Remove the widget from the tree node map
    let treeNode = getNodeAtPath({
        treeData: this.state.treeData, 
        path: path, 
        getNodeKey: defaultGetNodeKey,
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
    const rightClickMenuPosition = this.state.rightClickMenuPosition; 
    const rightClickMenu = (this.state.rightClickMenuShown ?
     <RightClickMenu left={rightClickMenuPosition.x} top={rightClickMenuPosition.y} 
      menuCallbacks={this.state.rightClickMenuCallbacks}
      shapeID={this.state.rightClickShapeID}
      getSiblingLabelItem={this.getSiblingLabelItem}
      getCurrentShapeIndex={this.getCurrentShapeIndex}
      getCurrentShapeOrder={this.getCurrentShapeOrder}
      getCurrentShapeSiblings={this.getCurrentShapeSiblings}
      getCurrentShapeImportance={this.getCurrentShapeImportance}  /> : undefined);
    const colorPicker = (this.state.colorPickerShown ? <Ios11Picker onChangeComplete={this.updateBackgroundColor} /> : undefined);  
    const colorPickerPosition = this.state.colorPickerPosition; 
    const pageOrder = this.state.pageOrder; 
    var self = this;

    // Process the queue of shapes to add to the canvas
	  return (
       <div className="panel panel-default constraints-container">
          <div className="panel-heading"> 
            <h3 className="panel-title">Constraints
              <div className="btn-group btn-group-xs header-button-group">
                <button type="button" className="btn btn-info dropdown-toggle" data-toggle="dropdown" aria-haspopup="true" aria-expanded="false">
                  Order<span className="caret"></span>
                </button>
                <ul className="dropdown-menu">
                  <li onClick={this.togglePageOrder.bind(this, "important")}><a href="#">Order Important</a></li>
                  <li onClick={this.togglePageOrder.bind(this, "unimportant")}><a href="#">Order Unimportant</a></li>
                </ul>
              </div>
              <span className={"label " + (pageOrder == "important" ? "label-success" : "label-info")}>Order {pageOrder}</span>
            </h3>
          </div>
          <div id="constraints-canvas-container" tabIndex="1" className="constraints-canvas-container panel-body"> 
            <div className="constraints-canvas-page-feedback">
              {pageFeedbacks}
            </div>
            <div className={(!rightClickMenu ? "hidden" : "")}> 
              {rightClickMenu}
            </div>
            {/*<div className={(!colorPicker ? "hidden" : "")}> 
              {colorPicker}
            </div>*/}
            <div className="widgets-sortable-tree">
              { /*             rowHeight={this.calculateRowHeight.bind(this)} */}
              <SortableTree
                treeData={this.state.treeData}
                onChange={treeData => this.setState({ treeData })}
                canDrop={this.canReparentWidgetNode.bind(this)}
                onMoveNode={this.onMoveNode.bind(this)}
                rowHeight={this.calculateRowHeight.bind(this)}
                style={{height: "calc(100% - 80px)"}}
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
      </div>
    );
  }
}
