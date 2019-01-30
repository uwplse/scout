import React from "react";
import 'rc-tree/assets/index.css';
import '../css/ConstraintsCanvas.css'; 
import '../css/Tree.css';
import ConstraintsCanvasSVGWidget from './ConstraintsCanvasSVGWidget';
import ConstraintsCanvasContainerSVGWidget from './ConstraintsCanvasContainerSVGWidget';
import WidgetFeedback from './WidgetFeedback';
import ConstraintActions from './ConstraintActions';
import { getUniqueID } from './util';
// import {
//   SortableTreeWithoutDndContext as SortableTree,
//   removeNodeAtPath, 
//   getNodeAtPath, 
//   changeNodeAtPath, 
//   defaultGetNodeKey, 
//   insertNode,
//   getFlatDataFromTree, 
//   addNodeUnderParent } 
// from 'react-sortable-tree';
// import ConstraintsCanvasMenu from './ConstraintsCanvasMenu'; 
import GroupingRightClickMenu from './GroupingRightClickMenu'; 
import WidgetTyping from './WidgetTyping'; 
import groupSVG from '../assets/GroupWidget.svg';
import repeatGrid from '../assets/illustrator/repeatGrid.svg';
import item from '../assets/illustrator/item.svg';
import rootNode from '../assets/CanvasWidget.svg';
import Tree, { TreeNode } from 'rc-tree';

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
    this.defaultNodeHeight = 46.5; 
    this.defaultNodeWidth = 173;

    this.state = { 
      treeData: [], 
      expandedTreeNodes: ["canvas"],
      selectedTreeNodes: [], 
      pageFeedbackWidgets: [], 
      rightClickMenuShown: false, 
      rightClickMenuCallbacks: undefined, 
      rightClickMenuPosition: {
        x: 0, 
        y: 0
      }, 
      rightClickShapeID: undefined, 
      svgSourceMap: {}
    }; 
  }

  componentDidMount() {
    let cachedShapesJSON = localStorage.getItem('shapeHierarchy'); 
    if(!cachedShapesJSON) {
      let rootNode = this.initRootNode();
      this.state.treeData = this.state.treeData.concat(rootNode); 

      this.setState(state => ({
        treeData: this.state.treeData
      }), this.updateShapeCache);
    }else {
      let cachedShapesJSON = localStorage.getItem('shapeHierarchy');
      let cachedShapes = JSON.parse(cachedShapesJSON);
      this.constructTreeFromCache(cachedShapes);
    }
  }

  componentDidUpdate = (prevProps) => {
    if(prevProps.svgWidgets.length != this.props.svgWidgets.length) {
      // Update the tree nodes with the SVG source from the cache 
      this.updateSVGSourceMap(); 
    }
  }

  checkSolutionValidityAndUpdateCache = () => {
    // Update shapes cache in localStorage
    this.updateShapeCache(); 

    // Check validity of constraints
    this.checkSolutionValidity();
  }

  constructTreeFromCache = (treeData) => {   
    let canvasNode = {
      key: treeData.name, 
      shape: treeData, 
      src: rootNode, 
      children: []
    }

    // Restore the cosntraints tree from the cached shapes
    this.canvasLevelShape = treeData; 
    this.constraintsShapesMap[canvasNode.name] = treeData; 
    this.widgetTreeNodeMap[canvasNode.name] = canvasNode; 

    if(treeData.children) {
      // Restore feedback items
      // Check whether to remove or add a widget feedback item
      // if(this.canvasLevelShape.locks && this.canvasLevelShape.locks.length) {
      //   for(let i=0; i<this.canvasLevelShape.locks.length; i++) {
      //     let lock = this.canvasLevelShape.locks[i];
      //     let action = ConstraintActions.getAction("keep", this.canvasLevelShape);
      //     if(action){
      //       let uniqueId = _.uniqueId();
      //       let message = action["do"].getFeedbackMessage(lock, this.canvasLevelShape);
      //       let id = this.canvasLevelShape.name + "_" + uniqueId; 
      //       let widgetFeedback = this.getWidgetFeedback(id, this.canvasLevelShape, action, lock, message);
      //       newTreeNode.subtitle.push(widgetFeedback); 
      //     } 
      //   }     
      // } 

      for(let i=0; i<treeData.children.length; i++) {
        let child = treeData.children[i]; 
        this.constructShapeHierarchy(child, canvasNode);
      }

      this.state.treeData = this.state.treeData.concat(canvasNode); 
    }

    this.setState(state => ({
      treeData: this.state.treeData
    }));
  }

  updateSVGSourceMap = () => {
    for(let i=0; i < this.props.svgWidgets.length; i++) {
      let svgWidget = this.props.svgWidgets[i]; 
      this.state.svgSourceMap[svgWidget.id] = svgWidget; 
    }

    this.setState({
      svgSourceMap: this.state.svgSourceMap
    });
  }

  // getSVGSource = (node) => {
  //   if(node.item) {
  //     return item; 
  //   }

  //   let svgElements = this.props.svgWidgets; 
  //   let svgElement = svgElements.filter(element => element.id == node.id); 
  //   if(svgElement && svgElement.length) {
  //     svgElement = svgElement[0]; 
  //     return svgElement.svgData; 
  //   }

  //   return ""; 
  // }

  constructShapeHierarchy = (node, treeData) => {
    let source =  this.state.svgSourceMap[node.id];
    this.constraintsShapesMap[node.name] = node; 

    let newTreeNode = {
        key: node.name, 
        shape: node,
        src: source
    }; 

    this.widgetTreeNodeMap[node.name] = newTreeNode; 
    treeData.children.push(newTreeNode); 

    // Restore feedback items for locks 
    // if(node.locks && node.locks.length) {
    //   for(let i=0; i<node.locks.length; i++) {
    //     let lock = node.locks[i];
    //     let action = ConstraintActions.getAction("keep", node);
    //     if(action){
    //       let uniqueId = _.uniqueId();
    //       let message = action["do"].getFeedbackMessage(lock, node);
    //       let id = node.name + "_" + uniqueId; 
    //       let widgetFeedback = this.getWidgetFeedback(id, node, action, lock, message);
    //       newTreeNode.subtitle.push(widgetFeedback); 
    //     } 
    //   }     
    // } 
    if(node.children && node.children.length) {
      newTreeNode.children = []; 
      for(let i=0; i<node.children.length; i++){
        let child = node.children[i]; 
        this.constructShapeHierarchy(child, newTreeNode); 
      }
    }
  }

  initRootNode = () => {
    // Create an object to represent the  top level canvas shape
    let canvas = {
      "name": "canvas",
      "type": "canvas", 
      "controlType": "canvas",
      "containerOrder": "important",
      "children": [],
      "x": 0, 
      "y": 0,
      "width": this.defaultNodeWidth, 
      "height": this.defaultNodeHeight, 
      "orig_width": this.defaultNodeWidth, 
      "orig_height": this.defaultNodeHeight
    }

    this.canvasLevelShape = canvas;
    this.constraintsShapesMap[canvas.name] = this.canvasLevelShape; 


    let rootTreeNode = {
        key: this.canvasLevelShape.name, 
        shape: this.canvasLevelShape,
        src: rootNode, 
        children: []
        // item: false, 
        // typed: false, 
        // highlighted: false
    }; 

    return rootTreeNode; 
  }

  updateShapeCache = () => {
    // Update the entry for the constraintShapesMap in the localStorage cache
    // so we can repopulate the constraints tree on refresh 
    let shapeHierarchy = this.getShapeHierarchy();
    let shapeHierarchyJSON = JSON.stringify(shapeHierarchy); 
    localStorage.setItem('shapeHierarchy', shapeHierarchyJSON); 
  }

  getWidget = (key, shape, src, options={}) => {
    let shapeId = shape.name;
    let highlighted = options.highlighted ? options.highlighted : false; 
    let isContainer = shape.type == "group" || shape.type == "canvas";
    let item = options.item ? options.item : false;
    let typed = options.typed ? options.typed : false;

    if(isContainer) {
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
                getCurrentShapeSiblings={this.getCurrentShapeSiblings}
                getCurrentShapeIndex={this.getCurrentShapeIndex}
                removeWidgetNode={this.removeWidgetNode}
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
              getCurrentShapeSiblings={this.getCurrentShapeSiblings}
              getCurrentShapeIndex={this.getCurrentShapeIndex}
              removeWidgetNode={this.removeWidgetNode} />);
  }

  addShapeToCanvas = (id, source, type, width, height) => {
    let shape = this.createConstraintsCanvasShapeObject(id, type, width, height); 
    let newTreeNode = {
        key: shape.name, 
        shape: shape, 
        src:  source
    }; 

    this.widgetTreeNodeMap[shape.name] = newTreeNode; 

    if(this.state.treeData.length) {
      this.state.treeData[0].children.push(newTreeNode); 
    }

    this.setState(state => ({
      treeData: this.state.treeData, 
    }), this.checkSolutionValidityAndUpdateCache);
  }

  clearShapesFromCanvas = () => {
    let newTreeData = []; 
    let rootNode = this.initRootNode(); 
    this.state.treeData = this.state.treeData.concat(rootNode); 
    this.setState({
      treeData: this.state.treeData
    }, this.updateShapeCache); 
  }

  createNewTreeNode = (type, source, options={}) => {
    // Creates a new tree node widget and returns it
    let id = getUniqueID();

    let width = options.width ? options.width : 0;
    let height = options.height ? options.height : 0; 
    let shape = this.createConstraintsCanvasShapeObject(id, type, width, height, options); 

    let newTreeNode = {
      key: shape.name, 
      shape: shape, 
      src: source
    }; 

    this.widgetTreeNodeMap[shape.name] = newTreeNode; 

    return newTreeNode; 
  }

  getWidgetFeedback = (shapeId, parentShape, action, property, message, highlighted) => {
    return (<WidgetFeedback 
              key={shapeId} 
              type="feedback"
              id={shapeId} 
              parentShape={parentShape}
              action={action}
              property={property}
              message={message} 
              highlighted={highlighted}
              updateConstraintsCanvas={this.updateConstraintsCanvas}/>); 
  }

  getConstraintsCanvasShape = (shapeID) => {
    return this.constraintsShapesMap[shapeID]; 
  }

  displayRightClickMenu = (evt, shapeID) => {
    let shape = this.constraintsShapesMap[shapeID]; 
    if(shape) {
      if(shape.type == "group") {
        this.setState({
          rightClickMenuShown: true, 
          rightClickMenuPosition: {
            x: evt.clientX, 
            y: evt.clientY
          }, 
          rightClickShapeID: shapeID, 
          rightClickGroup: false
        });         
      } else if(this.state.selectedTreeNodes.indexOf(shapeID) > -1 && this.state.selectedTreeNodes.length > 1) {
        this.setState({
          rightClickMenuShown: true, 
          rightClickMenuPosition: {
            x: evt.clientX, 
            y: evt.clientY
          }, 
          rightClickShapeID: shapeID, 
          rightClickGroup: true
        });   
      }
    }
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
      let nodeID = treeNode.key; 
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
      let nodeID = treeNode.key; 
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
        id: siblings.next.key 
      }; 
    }

    if(siblings.prev) {
      siblingItems.prev = {
        id: siblings.prev.key 
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
    return node.shape.containerOrder; 
  }

  getCurrentShapeOrder = (shapeId) => {
    let node = this.widgetTreeNodeMap[shapeId]; 
    return node.shape.order; 
  }

  getCurrentShapeImportance = (shapeId) => {
    let node = this.widgetTreeNodeMap[shapeId]; 
    return node.shape.importance; 
  }

  getCurrentShapeType = (shapeId) => {
    let node = this.widgetTreeNodeMap[shapeId]; 
    return node.shape.type; 
  }
 
  hideRightClickMenu = () => {
    // Recheck consistency of the solutions after any of the things are set
    this.setState({
      rightClickMenuShown: false
    }); 
  }

  // highlightAddedWidget = (shapeId, highlighted) => {
  //   let treeNode = this.widgetTreeNodeMap[shapeId];
  //   let treeNodeData = this.getPathAndChildrenForTreeNode(treeNode);
  //   if(treeNodeData) {
  //     let widget = this.getWidget(treeNode.title.props.shape, treeNode.title.props.source, { highlighted: highlighted }); 

  //     // Create a new node for the widget
  //     let newNode = {
  //       title: widget, 
  //       subtitle: [], 
  //       expanded: treeNode.expanded || treeNodeData.expanded, 
  //       children: treeNodeData.children
  //     }; 

  //     // Replace the current node with this new node
  //     this.state.treeData = changeNodeAtPath({
  //       treeData: this.state.treeData,
  //       path: treeNodeData.path,
  //       getNodeKey: defaultGetNodeKey,
  //       ignoreCollapsed: false,
  //       newNode: newNode
  //     }); 

  //     this.setState(state => ({
  //       treeData: this.state.treeData
  //     })); 
  //   }
  // }

  // highlightWidgetFeedback = (shapeId, lock, highlighted) => {
  //   // Find the widget with this shape ID in the constraints tree
  //   let treeNode = this.widgetTreeNodeMap[shapeId]; 
  //   let feedbackItems = undefined; 
  //   if(treeNode != undefined) {
  //     feedbackItems = treeNode.subtitle; 
  //   }else {
  //     feedbackItems = this.state.pageFeedbackWidgets; 
  //   }

  //   // Find the corresponding feedback item
  //   let feedbackIndex = -1; 
  //   for(let i=0; i<feedbackItems.length; i++) {
  //     if(feedbackItems[i].props.action["do"].key == lock) {
  //       feedbackIndex = i; 
  //     }
  //   }

  //   if(feedbackIndex > -1) {
  //     let feedbackItem = feedbackItems[feedbackIndex]; 

  //     // Highlight parameter can be true or false which determines whether the new feedback item is highlighted or unhighlighted
  //     let newFeedbackItem = this.getWidgetFeedback(shapeId, feedbackItem.props.parentShape, feedbackItem.props.action, feedbackItem.props.message, highlighted); 
      
  //     // Splice out the old item 
  //     feedbackItems.splice(feedbackIndex, 1); 
  //     feedbackItems.splice(feedbackIndex, 0, newFeedbackItem); 
  //   }

  //   this.setState(state => ({
  //     treeData: this.state.treeData
  //   }));      
  // }

  // updateWidgetFeedbacks = (shape, action, actionType, property) => {    
  //   // The shape was already updated so we just need to re-render the tree to get the new sizes
  //   // Add WidgetFeedbackItem to correct item in the tree

  //   // Find the corresponding tree node
  //   let shapeId = shape.name; 
  //   let uniqueId = _.uniqueId();
  //   let treeNode = this.widgetTreeNodeMap[shapeId]; 

  //   // First, see whether there is already a feedback item for this action
  //   // If there is, remove it, before updating with the new action
  //   let feedbackItems = treeNode.subtitle; 
  //   let feedbackIndex = -1; 
  //   for(let i=0; i<feedbackItems.length; i++){
  //     ///???
  //     if(feedbackItems[i].props.property == property) {
  //       feedbackIndex = i; 
  //     }
  //   }

  //   // Remove the item at that index
  //   if(feedbackIndex > -1) {
  //     treeNode.subtitle.splice(feedbackIndex, 1);        
  //   }

  //   // Check whether to remove or add a widget feedback item
  //   if(actionType == "do") {
  //     let message = action[actionType].getFeedbackMessage(property, shape);
  //     let id = shapeId + "_" + uniqueId; 
  //     let widgetFeedback = this.getWidgetFeedback(id, shape, action, property, message);
  //     treeNode.subtitle.push(widgetFeedback);       
  //   } 

  //   this.setState(state => ({
  //     treeData: this.state.treeData
  //   }), this.checkSolutionValidityAndUpdateCache);      
  // }

  getShapeHierarchy = () => {
    let treeNodes = this.state.treeData; 

    // Convert this into a hierarchical structure
    if(treeNodes.length) {
      let rootNode = treeNodes[0]; 
      if(rootNode.children){
        this.getShapeChildren(rootNode); 
      }

      let rootNodeShape = rootNode.shape; 
      if(rootNode.typed) {
        // If the tree node is a typed group
        // Update the correspondingID list to
        // link the child elemeents with their corresponding shapes
        this.getRepeatGroupMatchingChildren(rootNode); 
        shape.typed = true; 
      }

      return rootNodeShape; 
    }

    return undefined; 
  }


  getShapeChildren = (node) => {
    let shape = node.shape; 
    shape.children = []; 
    for(let i=0; i<node.children.length; i++){
      let child = node.children[i]; 

      if(child.typed) {
        this.getRepeatGroupMatchingChildren(child); 
        child.shape.typed = true; 
      }

      
      // Add the child shape object to the shape children
      let childShape = child.shape; 
      shape.children.push(childShape); 

      if(child.children){
        this.getShapeChildren(child);
      }
    }
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
    let item = (options.item ? options.item : false); 
    let typed = (options.typed ? options.typed : false);

    // Set up the object that will keep the current state of this shape
    // And be passed with a set of information to the server for solving
    let shape = {
      "name": getUniqueID(),
      "id": id, 
      "type": type,
      "importance": importance, 
      "containerOrder": containerOrder, 
      "order": order, 
      "width": width, 
      "height": height,
      "orig_width": width, 
      "orig_height": height,
      "x": 0, 
      "y": 0,
      "item": item, 
      "typed": typed
    }

    if (isContainer) {
      shape.children = []; 
    }

    this.constraintsShapesMap[shape["name"]] = shape; 

    return shape;
  }

  // typesMatch = (group1, group2) =>  {
  //   // Check whether the set of types in each group list match 
  //   if(group1.length != group2.length) {
  //     return false;
  //   }

  //   for(let i=0; i<group1.length; i++) {
  //     let item1 = group1[i]; 
  //     let item2 = group2[i]; 
  //     if(item1 != item2) {
  //       return false;
  //     }
  //   }

  //   return true;
  // }

  // canSplitIntoGroupOfSize = (node, size) => {
  //   // Determine if the children of this node can be split into a group of the given size
  //   let pattern = []; 

  //   // Collect all the types and split them into groups based on the given size
  //   let currSize = 0; 
  //   let currGroup = []; 
  //   for(let i=0; i<node.children.length; i++) {
  //     let currChild = node.children[i]; 
  //     currGroup.push(currChild.title.props.shape.type);
  //     currSize++; 

  //     if(currSize == size){
  //       if(currGroup.length) {
  //         pattern.push(currGroup); 
  //       }

  //       currSize = 0; 
  //       currGroup = []; 
  //     }
  //   }

  //   // Now, verify that each of the subgroups has the exact same set of types
  //   for(let i=0; i<pattern.length; i++){
  //     if(i < pattern.length - 1) {
  //       let patternGroup = pattern[i]; 
  //       let nextPatternGroup = pattern[i+1]; 
  //       if(!this.typesMatch(patternGroup, nextPatternGroup)) {
  //         return false;
  //       }
  //     }
  //   }

  //   return true; 
  // }

  // getGroupSizes = (total) => {
  //   // Get the set of group sizes to check by finding the possible divisors
  //   let totalFloor = Math.floor(total/2); 
  //   let sizes = []; 
  //   for(let i=1; i<=totalFloor; i++) {
  //     if(total % i == 0){
  //       sizes.push(i); 
  //     }
  //   }

  //   return sizes;
  // }

  // checkGroupTyping = (node) => {
  //   // Do the type inference algorithm
  //   // iterate through each set of possible groupings starting with the greatest common divisor
  //   let numChildren = node.children.length; 
  //   let groupSizes = this.getGroupSizes(numChildren);
  //   // We want to split into the largest size group, so reverse the order
  //   groupSizes.reverse();
  //   for(let i=0; i<groupSizes.length; i++) {
  //     let groupSize = groupSizes[i];
  //     if(groupSize >= this.minimumGroupSize) {
  //       if(this.canSplitIntoGroupOfSize(node, groupSize)) {
  //         return groupSize;
  //       }
  //     }
  //   }

  //   return false;
  // }

  // getRepeatGroupMatchingChildren = (group) => {
  //   // For a given child, return the shape IDs of the child shapes that are in the
  //   // corresponding positions in the other group(s)
  //   let items = group.children; 
  //   if(items) {
  //     for(let i=0; i<items.length; i++) {
  //       let currItem = items[i]; 

  //       let correspondingBefore = []
  //       if(i > 0) {
  //         correspondingBefore = _.range(0, i); 
  //       }

  //       let correspondingAfter = []; 
  //       if(i < items.length - 1) {
  //         correspondingAfter = _.range(i+1, items.length); 
  //       }

  //       let correspondingItems = correspondingBefore.concat(correspondingAfter); 

  //       let itemChildren = currItem.children; 
  //       if(itemChildren) {
  //         for(let j=0; j<itemChildren.length; j++) {
  //           let itemChild = itemChildren[j]; 

  //           let correspondingIDs = []; 
  //           for(let k=0; k<correspondingItems.length; k++) {
  //             let correspondingItem = items[correspondingItems[k]]; 
  //             let matchingItem = correspondingItem.children[j]; 
  //             correspondingIDs.push(matchingItem.key);
  //           }

  //           itemChild.shape.correspondingIDs = correspondingIDs; 
  //         }
  //       }
  //     }
  //   }
  // }

  // restructureRepeatGroupChildren = (groupChildren, groupSize) => {
  //   // Split the children of this group node into uniformly sized groups 
  //   let curr = 0; 
  //   let currGroup = []; 
  //   let groups = []; 
  //   for(let i=0; i<groupChildren.length; i++) {
  //     currGroup.push(groupChildren[i]); 
  //     curr++; 

  //     if(curr == groupSize) {
  //       groups.push(currGroup);
  //       currGroup = [];
  //       curr = 0;  
  //     }
  //   }

  //   // For each group of children, create a new group node in the tree, and return these groups as 
  //   // the new children 
  //   let newChildren = []; 
  //   for(let i=0; i<groups.length; i++) {
  //     let currGroup = groups[i]; 
  //     let newGroupNode = this.createNewTreeNode("group", item, { item: true }); 
  //     let isExpanded = (i == 0) ? true : false; 
  //     newGroupNode.expanded = isExpanded; 
  //     newGroupNode.children = currGroup; 
  //     newChildren.push(newGroupNode); 
  //   }

  //   return newChildren; 
  // }

  // createRepeatGroup = (groupID, typed, groupSize) => {
  //   return () => {
  //     let groupNode = this.widgetTreeNodeMap[groupID];
  //     // let groupNodeData = this.getPathAndChildrenForTreeNode(groupNode);
  //     if(groupNode) {
  //       let widget = this.getWidget(groupNode.title.props.shape, repeatGrid, { typed: true }); 
  //       let newGroupChildren = this.restructureRepeatGroupChildren(groupNodeData.children, groupSize); 

  //       // Create a new node for the widget
  //       let newNode = {
  //         title: widget, 
  //         subtitle: [], 
  //         expanded: true, 
  //         children: newGroupChildren
  //       }; 

  //       // Replace the current node with this new node
  //       this.state.treeData = changeNodeAtPath({
  //         treeData: this.state.treeData,
  //         path: groupNodeData.path,
  //         getNodeKey: defaultGetNodeKey,
  //         ignoreCollapsed: false,
  //         newNode: newNode
  //       }); 

  //       this.setState(state => ({
  //         treeData: this.state.treeData
  //       }), this.checkSolutionValidityAndUpdateCache); 
  //     }
  //   }
  // }

  // closeTypingAlert = (groupID) => {
  //   return () => {
  //     // Close the group typing alert dialog without doing anything. 
  //     let treeNode = this.widgetTreeNodeMap[groupID]; 
  //     // Remove the typing dialog from the group
  //     if(treeNode && treeNode.subtitle && treeNode.subtitle.length) {
  //       let subtitleNode = treeNode.subtitle[0]; 
  //       if(subtitleNode.props.type == "typing") {
  //         treeNode.subtitle.splice(0,1);       
  //       }
  //     }

  //     this.setState(state => ({
  //       treeData: this.state.treeData
  //     }));       
  //   }
  // }

  // getWidgetTyping = (key, groupID, groupSize) => {
  //   return (<WidgetTyping 
  //     key={key} type="typing" 
  //     groupID={groupID} 
  //     groupSize={groupSize}
  //     createRepeatGroup={this.createRepeatGroup} 
  //     closeTypingAlert={this.closeTypingAlert} />); 
  // }

  // createLabelsGroup = (labelID, labeledID) => {
  //   // Create a new group in the hierarchy to contain the labeled shape and the label shape 
  //   let labelNode = this.widgetTreeNodeMap[labelID]; 
  //   let labeledNode = this.widgetTreeNodeMap[labeledID]; 
  //   let labelNodeData = this.getPathAndChildrenForTreeNode(labelNode); 
  //   let labeledNodeData = this.getPathAndChildrenForTreeNode(labeledNode);
  //   if(labelNodeData && labeledNodeData) {
  //     // Remove labeled node from the tree before re-adding to the labels group
  //     this.state.treeData = removeNodeAtPath({
  //       treeData: this.state.treeData, 
  //       path: labeledNodeData.path, 
  //       getNodeKey: defaultGetNodeKey,
  //     }); 
      
  //     // Create a new labelGroup element. The order should be important so the label always appears first in reading order. 
  //     // Have to set the children on the object here when creating a new node
  //     labeledNode.children = labeledNodeData.children; 

  //     let newLabelGroupNode = this.createNewTreeNode("labelGroup", label, { containerOrder: "important" }); 
  //     newLabelGroupNode.expanded = true; 
  //     newLabelGroupNode.children = [labelNode, labeledNode]; 

  //     // Replace the current node with this new node
  //     this.state.treeData = changeNodeAtPath({
  //       treeData: this.state.treeData,
  //       path: labelNodeData.path,
  //       getNodeKey: defaultGetNodeKey,
  //       ignoreCollapsed: false,
  //       newNode: newLabelGroupNode
  //     }); 
  //   }
  // }

  // removeTypedGroup = (groupNode) => {
  //  // Ungroup childen from the item containers
  //   let children = groupNode.children; 
  //   if(children) {
  //     for(let i=0; i<children.length; i++){
  //       let child = children[i]; 
  //       if(child.title.props.item) {
  //         let nodePath = this.getPathAndChildrenForTreeNode(child); 

  //         this.state.treeData = removeNodeAtPath({
  //           treeData: this.state.treeData, 
  //           path: nodePath.path, 
  //           getNodeKey: defaultGetNodeKey,
  //         }); 

  //         // Remove the children of the item and place
  //         // at the parent level
  //         let itemChildren = child.children; 
  //         if(itemChildren) {
  //           let startingIndex = nodePath.treeIndex; 
  //           for(let i=0; i<itemChildren.length; i++) {
  //             let itemChild = itemChildren[i]; 
  //             // Reinsert the children at the item node level
  //             let result = insertNode({
  //               treeData: this.state.treeData, 
  //               depth: nodePath.path.length - 1, 
  //               minimumTreeIndex: startingIndex, 
  //               newNode: itemChild, 
  //               getNodeKey: defaultGetNodeKey, 
  //               ignoreCollapsed: false, 
  //               expandParent: true
  //             });  

  //             if(result.treeData) {
  //               this.state.treeData = result.treeData; 
  //             }                     

  //             startingIndex += 1; 
  //           }
  //         }
  //       }
  //     }
  //   }

  //   // once children have been restructured, replace
  //   // the group container with a regular group container
  //   this.replaceTypedGroup(groupNode); 
  // }

  // replaceTypedGroup = (groupNode) => {
  //   let groupNodeData = this.getPathAndChildrenForTreeNode(groupNode);
  //   if(groupNodeData) {
  //     let shape = groupNode.title.props.shape; 
  //     shape.typed = false; 

  //     let widget = this.getWidget(shape, group); 

  //     // Create a new node for the widget
  //     let newNode = {
  //       title: widget, 
  //       subtitle: [], 
  //       expanded: true, 
  //       children: groupNodeData.children
  //     }; 

  //     // Replace the current node with this new node
  //     this.state.treeData = changeNodeAtPath({
  //       treeData: this.state.treeData,
  //       path: groupNodeData.path,
  //       getNodeKey: defaultGetNodeKey,
  //       ignoreCollapsed: false,
  //       newNode: newNode
  //     }); 
  //   }
  // }

  // onMoveNode = ({ treeData, node, nextParentNode, prevPath, prevTreeIndex, nextPath, nextTreeIndex }) => {
  //   // If the node was moved into group, check whether group typing should be applied. 
  //   if(nextParentNode) {
  //     if(nextParentNode.title.props.shape.type == "group") {
  //       this.removeWidgetTypingAlert(nextParentNode);
  //       if(nextParentNode.title.props.typed) {
  //         // The group is already typed. 
  //         // Remove the group typing 
  //         // Check first whether the widget typing alert has already been activated for this group
  //         this.removeTypedGroup(nextParentNode);
  //       } 

  //       let groupSize = this.checkGroupTyping(nextParentNode); 
  //       let parentID = nextParentNode.title.props.shape.name; 

  //         // Find the group in the tree, remove it, and display the label to apply the typing
  //       if(groupSize >= this.minimumGroupSize) {
  //         let typingIndex = 0; 
  //         let widgetTypingElement = this.getWidgetTyping(typingIndex, parentID, groupSize); 
  //         nextParentNode.subtitle.unshift(widgetTypingElement);
  //       }   
  //     }
  //   }

  //   // Remove the widget from the tree node map
  //   let prevParentPath = prevPath.slice(0, prevPath.length-1);
  //   let prevParentNode = getNodeAtPath({
  //       treeData: this.state.treeData, 
  //       path: prevParentPath, 
  //       getNodeKey: defaultGetNodeKey,
  //   }); 

  //   // If the previous node was a typed group or item, remove the typing
  //   // Also remove the alert if it was showin
  //   prevParentNode = prevParentNode.node; 
  //   if(prevParentNode && prevParentNode.title.props.shape.type == "group") {
  //     this.removeWidgetTypingAlert(prevParentNode); 

  //     if(prevParentNode.title.props.typed) {
  //       this.removeTypedGroup(prevParentNode); 
  //     }
  //     else if(prevParentNode.title.props.item) {
  //       let typedGroupPath = prevParentPath.slice(0, prevParentPath.length-1); 
  //       let typedGroupNode = getNodeAtPath({
  //         treeData: this.state.treeData, 
  //         path: typedGroupPath, 
  //         getNodeKey: defaultGetNodeKey
  //       }); 

  //       this.removeTypedGroup(typedGroupNode.node);
  //     }
  //   }

  //   this.setState(state => ({
  //     treeData: this.state.treeData
  //   }), this.checkSolutionValidityAndUpdateCache); 
  // }

  // removeWidgetTypingAlert = (node) => {
  //   if(node.subtitle && node.subtitle.length) {
  //     let firstSubtitle = node.subtitle[0]; 
  //     if(firstSubtitle.props.type == "typing") {
  //       // Splice out the typing message that is already there, and replace it with a new one to keep the current group size. 
  //       node.subtitle.splice(0,1);
  //     }
  //   }
  // }

  removeWidgetNode = (key) => { 
    let parentNode = this.getParentNodeForKey(key, this.state.treeData[0]); 
    let index = -1; 
    for(let i=0; i<parentNode.children.length; i++) {
      let childNode = parentNode.children[i]; 
      if(childNode.key == key) {
        index = i; 
        break;
      }
    }

    if(index != -1) {
      parentNode.children.splice(index, 1); 
    }

    // Remove from the global map of widgets
    delete this.widgetTreeNodeMap[key]; 

    // Delete the entry in the constraints canvas shape map 
    delete this.constraintsShapesMap[key];

    this.setState(state => ({
      treeData: this.state.treeData,
    }), this.checkSolutionValidityAndUpdateCache); 

    // // Check if the parent node is an item or a typed group 
    // // If it is either an item or typed group
    // // Remove the typed group and unparent the children 
    // // from the item groups. 
    // let parentPath = path.slice(0, path.length-1); 
    // if(parentPath.length) {
    //   let parentNode = getNodeAtPath({
    //     treeData: this.state.treeData, 
    //     path: parentPath, 
    //     getNodeKey: defaultGetNodeKey
    //   }); 

    //   if(parentNode.node.title.props.typed) {
    //     if(parentNode.node.children.length == 1) {
    //       this.removeTypedGroup(parentNode.node); 
    //     }
    //   }
    //   else if(parentNode.node.title.props.item) {
    //     let typedGroupPath = parentPath.slice(0, parentPath.length-1); 
    //     let typedGroupNode = getNodeAtPath({
    //       treeData: this.state.treeData, 
    //       path: typedGroupPath, 
    //       getNodeKey: defaultGetNodeKey
    //     }); 

    //     this.removeTypedGroup(typedGroupNode.node);
    //   }
    //   else if(parentNode.node.title.props.isContainer) {
    //     // Hide the typing alert that was shown on the container, if there is one
    //     this.removeWidgetTypingAlert(parentNode.node);
    //   }
    // }

  }

  groupContainsKey = (treeNode, key) => {
    for(let j=0; j<treeNode.children.length; j++) {
      if(treeNode.children[j].key == key) {
        return true;
      }
    }

    return false;
  }

  groupTreeNodes = (treeNode, keys) => {
    let nodes = []; 
    let index = 0;
    let firstIndex = -1; 
    while(treeNode.children.length && index <= treeNode.children.length-1) {
      let childNode = treeNode.children[index]; 
      if(keys.indexOf(childNode.key) > -1) {
        if(firstIndex == -1) {
          firstIndex = index; 
        }

        let removedChild = treeNode.children.splice(index,1);
        nodes.push(removedChild[0]); 
      }else {
        index += 1; 
      }
    }

    // Make a new group to contain the nodes
    let group = this.createNewTreeNode("group", groupSVG, {width: this.defaultNodeWidth, height: this.defaultNodeHeight});
    group.children = nodes; 

    if(firstIndex != -1) {
      treeNode.children.splice(firstIndex, 0, group);
    }
  }

  groupSelectedNodes = () => {
    let firstKey = this.state.selectedTreeNodes[0];
    let parentNode = this.getParentNodeForKey(firstKey, this.state.treeData[0]);
    if(parentNode) {
      this.groupTreeNodes(parentNode, this.state.selectedTreeNodes);
    }

    this.setState({
      treeData: this.state.treeData 
    })
  }

  ungroupGroup = (nodeKey) => {
    let parentNode = this.getParentNodeForKey(nodeKey, this.state.treeData[0]); 
    let index = -1; 
    let groupChildren = [];
    for(let i=0; i<parentNode.children.length; i++) {
      let childNode = parentNode.children[i]; 
      if(childNode.key == nodeKey) {
        index = i; 
        groupChildren = childNode.children; 
        childNode.children = undefined; 
      }
    }

    // remove the group element first
    parentNode.children.splice(index, 1); 

    // Now insert them into the parent at that index
    if(index != -1) {
      parentNode.children.splice(index, 0, ...groupChildren);
    }
  }

  onExpand = (expandedKeys) => {
    console.log('onExpand', arguments);
    this.setState({
      expandedTreeNodes: expandedKeys
    });
  }

  getParentNodeForKey = (treeNodeKey, treeNode) =>  {
    if(treeNodeKey == "canvas") {
      return treeNode; 
    }

    if(treeNode.children && treeNode.children.length) {
      for(let i=0; i<treeNode.children.length; i++) {
        let nodeChild = treeNode.children[i]; 
        if(nodeChild.key == treeNodeKey) {
          return treeNode; 
        }

        let subNode = this.getParentNodeForKey(treeNodeKey, nodeChild); 
        if(subNode) {
          return subNode; 
        }
      }
    }

    return undefined; 
  }

  hasSameParentNode = (treeNodeKey1, treeNodeKey2) => {
    let parent1 = this.getParentNodeForKey(treeNodeKey1); 
    let parent2 = this.getParentNodeForKey(treeNodeKey2); 
    if(parent1 && parent2 && parent1.key == parent2.key) {
      return true; 
    }

    return false;
  }

  onSelected = (selectedKeys, evt) => {
    let selected = selectedKeys[selectedKeys.length-1];
    if(!evt.nativeEvent || !evt.nativeEvent.shiftKey) {
      // allow multiple node seelction when shift key is pressed
      // Only have the most recent node selected 
      this.setState({
        selectedTreeNodes: [selected]
      }); 
    } else {
      // Get the last selected node and verify that it has the same parent node as the other 
      // selected nodes
      let selectedNodes = selectedKeys; 
      if(this.state.selectedTreeNodes.length > 1) {
        let prev = this.state.selectedTreeNodes[this.state.selectedTreeNodes.length-2]; 
        if(!this.hasSameParentNode(selected, prev)) {
          selectedNodes = [selected]; 
        }
      }

      this.setState({
        selectedTreeNodes: selectedNodes
      }); 
    }
  }

  onDrop = (info) => {
    console.log('drop', info);
    const dropKey = info.node.props.eventKey;
    const dragKey = info.dragNode.props.eventKey;
    const dropPos = info.node.props.pos.split('-');
    const dropPosition = info.dropPosition - Number(dropPos[dropPos.length - 1]);

    const loop = (data, key, callback) => {
      data.forEach((item, index, arr) => {
        if (item.key === key) {
          callback(item, index, arr);
          return;
        }
        if (item.children) {
          loop(item.children, key, callback);
        }
      });
    };
    const data = [...this.state.treeData];

    let dropObj; 
    loop(data, dropKey, (item) => {
      dropObj = item; 
    });

    let droppedOnGroup = false; 
    if(dropObj.shape.type == "group") {
      droppedOnGroup = true;
    }

    // Find dragObject
    let dragObj;
    loop(data, dragKey, (item, index, arr) => {
      arr.splice(index, 1);
      dragObj = item;
    });

    if (droppedOnGroup) {
      // Drop on the content
      // Only allow the drop if the element dropped on is a gorup
      loop(data, dropKey, (item) => {
        item.children = item.children || [];
        item.children.unshift(dragObj);
      });
    } else if (
      (info.node.props.children || []).length > 0 &&  // Has children
      info.node.props.expanded &&                     // Is expanded
      dropPosition === 1                              // On the bottom gap
    ) {
      loop(data, dropKey, (item) => {
        item.children = item.children || [];
        item.children.unshift(dragObj);
      });
    } else {
      // Drop on the gap
      let ar;
      let i;
      loop(data, dropKey, (item, index, arr) => {
        ar = arr;
        i = index;
      });
      if (dropPosition === -1) {
        ar.splice(i, 0, dragObj);
      } else {
        ar.splice(i + 1, 0, dragObj);
      }
    }

    this.setState({
      treeData: data,
    });
  }

  render () {
    // Gather the set of tree nodes
    const gatherTreeNodes = data => {
      return data.map((item) => {
        let widgetOptions = {
          highlighted: item.highlighted, 
          typed: item.typed, 
          item: item.item
        }

       let widgetSource = item.src; 
       if(!widgetSource) {
          let widgetSourceNode = this.state.svgSourceMap[item.shape.id]; 
          if(widgetSourceNode) {
            widgetSource = widgetSourceNode.svgData; 
          }
       }

        let widget = this.getWidget(item.key, item.shape, widgetSource, widgetOptions); 
        if (item.children && item.children.length) {
          return <TreeNode key={item.key} icon={widget} title={""}>{gatherTreeNodes(item.children)}</TreeNode>;
        }
        return <TreeNode key={item.key} icon={widget} title={""} />;
      });
    };

    const treeNodes = gatherTreeNodes(this.state.treeData); 

    console.log("Render ConstraintsCanvas");
    const shapes = this.constraintsShapes; 
    const pageFeedbacks = this.state.pageFeedbackWidgets;
    const rightClickMenuPosition = this.state.rightClickMenuPosition; 
    const rightClickMenu = (this.state.rightClickMenuShown ? 
      <GroupingRightClickMenu 
        groupElements={this.state.rightClickGroup} 
        groupSelected={this.groupSelectedNodes}
        ungroupSelected={this.ungroupGroup}
        menuLeft={rightClickMenuPosition.x}
        menuTop={rightClickMenuPosition.y}
        shapeID={this.state.rightClickShapeID} /> : undefined); 

    // Process the queue of shapes to add to the canvas
	  return (
       <div className="panel panel-primary constraints-container">
          <div className="panel-heading"> 
            <h3 className="panel-title">Outline
            </h3>
            <div className="btn-group header-button-group">
              <button 
                type="button" 
                className="btn btn-default design-canvas-button" 
                onClick={this.props.checkSolutionValidity.bind(this, {getDesigns: true})}>Generate Designs</button>
            </div>
          </div>
          <div id="constraints-canvas-container" tabIndex="1" className="constraints-canvas-container panel-body"> 
            <div className="constraints-canvas-page-feedback">
              {pageFeedbacks}
            </div>
            <div className={(!rightClickMenu ? "hidden" : "")}> 
              {rightClickMenu}
            </div>
            <div className="widgets-sortable-tree draggable-container">
              {treeNodes.length ? 
                (<Tree
                  draggable={true}
                  selectable={true}
                  showLine={false}
                  multiple={true}
                  autoExpandParent={true}
                  expandedKeys={this.state.expandedTreeNodes}
                  selectedKeys={this.state.selectedTreeNodes}
                  defaultExpandedKeys={["canvas"]}
                  onSelect={this.onSelected}
                  onDragStart={this.onDragStart}
                  onDragEnter={this.onDragEnter}
                  onDrop={this.onDrop}
                  onExpand={this.onExpand}
                >
                  {treeNodes}
                </Tree>) : undefined}
              {/*<SortableTree
                treeData={this.state.treeData}
                onChange={treeData => this.setState({ treeData })}
                canDrop={this.canReparentWidgetNode}
                onMoveNode={this.onMoveNode}
                rowHeight={this.calculateRowHeight}
                // isVirtualized={false}
                generateNodeProps={this.getNodeProps}
              />*/}
            </div>
          </div>
      </div>
    );
  }
}
