import React from "react";
import SVGWidget from './SVGWidget';
import WidgetFeedback from './WidgetFeedback';
import SortableTree, { removeNodeAtPath, getNodeAtPath, changeNodeAtPath, defaultGetNodeKey, getFlatDataFromTree } from 'react-sortable-tree';
import RightClickMenu from './RightClickMenu'; 
import WidgetTyping from './WidgetTyping'; 
import group from '../assets/illustrator/groupContainer.svg';
import typedGroup from '../assets/illustrator/typedGroupContainer.svg';  
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
    this.displayColorPicker = this.displayColorPicker.bind(this);
    this.updateBackgroundColor = this.updateBackgroundColor.bind(this);
    this.findShapeSiblings = this.findShapeSiblings.bind(this);
    this.getSiblingLabelItems = this.getSiblingLabelItems.bind(this);
    this.onMoveNode = this.onMoveNode.bind(this);
    this.setTypingOnGroup = this.setTypingOnGroup.bind(this);
    this.closeTypingAlert = this.closeTypingAlert.bind(this); 

    // This collection contains the set of shapes on the constraints canvas
    this.constraintsShapesMap = {};
    this.widgetTreeNodeMap = {};

    this.canvasWidth = 375; 
    this.canvasHeight = 667; 

    this.defaultControlWidth = 120; 
    this.defaultControlHeight = 40; 
    this.defaultFeedbackHeight = 40; 
    this.defaultTypingAlertHeight = 86;
    this.rowPadding = 10; 
    this.minimumRowHeight = 40; 

    this.state = { 
      treeData: [], 
      pageFeedbackWidgets: [], 
      rightClickMenuShown: false, 
      rightClickMenuSetFontSize: undefined, 
      rightClickMenuSetImportance: undefined, 
      rightClickMenuSetLabel: undefined, 
      rightClickMenuPosition: {
        x: 0, 
        y: 0
      }, 
      rightClickShapeID: undefined, 
      colorPickerShown: false, 
      colorPickerCallback: undefined, 
      colorPickerPosition: {
        x: 0, 
        y: 0 
      }, 
      showImportanceLevels: false
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
      }, 
      "background": "#ffffff" 
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

  getWidget(shape, src, options={}) {
    let shapeId = shape.name;
    let typedGroup = options.typedGroup ?  options.typedGroup : undefined;  
    return (<SVGWidget 
              key={shapeId} 
              shape={shape} 
              id={shapeId} 
              source={src}
              typedGroup={typedGroup}
              showImportanceLevels={this.state.showImportanceLevels}
              checkSolutionValidity={this.checkSolutionValidity} 
              displayRightClickMenu={this.displayRightClickMenu}
              hideRightClickMenu={this.hideRightClickMenu} />);
  }

  addShapeOfTypeToCanvas(type, controlType, source) {
    let shape = this.createConstraintsCanvasShapeObject(type, controlType); 
    let shapeId = shape.name;
    let widget = this.getWidget(shape, source); 

    let newTreeNode = {
        title: widget, 
        subtitle: []
    }; 

    this.widgetTreeNodeMap[shapeId] = newTreeNode; 
    this.state.treeData = this.state.treeData.concat(newTreeNode); 

    this.setState(state => ({
      treeData: this.state.treeData
    }), this.checkSolutionValidity);
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

  displayRightClickMenu(evt, shapeID, setFontSizeCallback, setImportanceCallback, setLabelCallback) {
    this.setState({
      rightClickMenuShown: true, 
      rightClickMenuSetFontSize: setFontSizeCallback, // The method to call in the SVGWidget instance that called this menu open.
      rightClickMenuSetImportance: setImportanceCallback,  
      rightClickMenuSetLabel: setLabelCallback, 
      rightClickMenuPosition: {
        x: evt.clientX, 
        y: evt.clientY
      }, 
      rightClickShapeID: shapeID
    });  
  }

  displayColorPicker(evt, setColor) {
    this.setState({
      colorPickerShown: true, 
      colorPickerCallback: setColor,
      colorPickerPosition: {
        x: evt.clientX, 
        y: evt.clientY
      }
    });   
  }

  findShapeSiblings(shapeId, siblings, node) {
    // Get the two neighboring siblings for a shape in the tree
    for(var i=0; i<node.length; i++) {
      let treeNode = node[i]; 
      let nodeID = treeNode.title.props.id; 
      if(nodeID == shapeId) {
        if(i > 0) {
          let prevSibling = node[i-1]; 
          siblings.previous = prevSibling; 
        }

        if(i < node.length - 1) {
          let nextSibling = node[i+1];
          siblings.next = nextSibling; 
        }
      }
      else if(treeNode.children) {
        this.findShapeSiblings(shapeId, siblings, treeNode.children); 
      }      
    }
  }

  getSiblingLabelItems(shapeId) {
    // Go through tree data (recursive) and find the level of the element
    let siblings = {}; 
    let node = this.state.treeData; 
    this.findShapeSiblings(shapeId, siblings, node);

    let menuItems = []; 
    if(siblings.previous) {
      menuItems.push({
        id: siblings.previous.title.props.id, 
        label: siblings.previous.title.props.shape.label, 
        direction: 'above'
      }); 
    }

    if(siblings.next) {
      menuItems.push({
        id: siblings.next.title.props.id, 
        label: siblings.next.title.props.shape.label, 
        direction: 'below'
      }); 
    }

    return menuItems; 
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
    this.setState({
      rightClickMenuShown: false
    }); 
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

  getPathForTreeNode(treeNode) {
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
        return node.path; 
      }
    }

    return [-1];
  }


  createConstraintsCanvasShapeObject(type, controlType) {  
    // Set up the object that will keep the current state of this shape
    // And be passed with a set of information to the server for solving
    let label = SVGWidget.initialLabels(controlType); 
    let shape = {
      "name": _.uniqueId(),
      "label": label, 
      "type": type,
      "controlType": controlType, 
      "size": {
        "width": SVGWidget.initialWidths(controlType), 
        "height": SVGWidget.initialHeights(controlType)
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
    let rowHeight = (actualRowHeight < this.minimumRowHeight) ? this.minimumRowHeight : actualRowHeight; 

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
    for(var i=2; i<=totalFloor; i++) {
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
    for(var i=0; i<groupSizes.length; i++) {
      let groupSize = groupSizes[i];
      if(this.canSplitIntoGroupOfSize(node, groupSize)) {
        return groupSize;
      }
    }

    return false;
  }

  setTypingOnGroup(groupID, typed){
    let source = typed ? typedGroup : group; 

    let groupNode = this.widgetTreeNodeMap[groupID];
    let groupNodePath = this.getPathForTreeNode(groupNode);
    let groupNodeInTree = getNodeAtPath({
      treeData: this.state.treeData, 
      path: groupNodePath, 
      getNodeKey: defaultGetNodeKey,
    }); 

    if(groupNode) {
      let widget = this.getWidget(groupNode.title.props.shape, source, { typed: typed }); 

      let newNode = {
        title: widget, 
        subtitle: [], 
        expanded: true, 
        children: groupNodeInTree.node.children
      }; 

      this.state.treeData = changeNodeAtPath({
        treeData: this.state.treeData,
        path: groupNodePath,
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

  getWidgetTyping(key, groupID){
    return (<WidgetTyping key={key} type="typing" groupID={groupID} setTypingOnGroup={this.setTypingOnGroup} closeTypingAlert={this.closeTypingAlert} />); 
  }

  onMoveNode({ treeData, node, nextParentNode, prevPath, prevTreeIndex, nextPath, nextTreeIndex }) {
    // If the node was moved into group, check whether group typing should be applied. 
    if(nextParentNode) {
      if(nextParentNode.title.props.shape.type == "group") {
        let shouldBeTyped = this.checkGroupTyping(nextParentNode); 
        let parentID = nextParentNode.title.props.shape.name; 
          // Find the group in the tree, remove it, and display the label to apply the typing
        if(shouldBeTyped) {
          let typingIndex = nextParentNode.subtitle.length; 
          let widgetTypingElement = this.getWidgetTyping(typingIndex, parentID); 
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
      setFontSize={this.state.rightClickMenuSetFontSize} 
      setImportanceLevel={this.state.rightClickMenuSetImportance} 
      setLabel={this.state.rightClickMenuSetLabel}
      shapeID={this.state.rightClickShapeID}
      getSiblingLabelItems={this.getSiblingLabelItems}  /> : undefined);
    const colorPicker = (this.state.colorPickerShown ? <Ios11Picker onChangeComplete={this.updateBackgroundColor} /> : undefined);  
    const colorPickerPosition = this.state.colorPickerPosition; 
    var self = this;

    // Process the queue of shapes to add to the canvas
	  return (
      <div className="panel-body" id="constraints-canvas-container" tabIndex="1" /*onClick={this.displayColorPicker} */>
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
