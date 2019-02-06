import React from "react";
import 'rc-tree/assets/index.css';
import '../css/ConstraintsCanvas.css'; 
import '../css/Tree.css';
import ConstraintsCanvasSVGWidget from './ConstraintsCanvasSVGWidget';
import ConstraintsCanvasContainerSVGWidget from './ConstraintsCanvasContainerSVGWidget';
import WidgetFeedback from './WidgetFeedback';
import WidgetFeedbackPanel from './WidgetFeedbackPanel';
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
import repeatGridSVG from '../assets/RepeatGroupWidget.svg';
import itemSVG from '../assets/ItemWidget.svg';
import rootNode from '../assets/CanvasWidget.svg';
import alternateSVG from '../assets/AlternateWidget.svg';
import Tree, { TreeNode } from 'rc-tree';

export default class ConstraintsCanvas extends React.Component {
  constructor(props) {
  	super(props); 

    // Callback to update a shape on the constraints canvas through the PageContainer so that it can validate the current state
    this.updateConstraintsCanvas = props.updateConstraintsCanvas; 
    this.checkSolutionValidity =  props.checkSolutionValidity; 

    // This collection contains the set of shapes on the constraints canvas
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
      selectedElement: undefined, 
      selectedElementY: 0, 
      rightClickMenuShown: false, 
      rightClickMenuCallbacks: undefined, 
      rightClickMenuPosition: {
        x: 0, 
        y: 0
      }, 
      rightClickMenuTypeGroupSize: -1, 
      rightClickMenuIsTyped: false,
      rightClickMenuIsAlternate: false,
      rightClickMenuContainsGroup: false,
      rightClickShapeID: undefined, 
      rightClickIsGroup: false,
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
    } else {
      let cachedShapes = JSON.parse(cachedShapesJSON);
      this.constructTreeFromCache(cachedShapes);
    }
  }

  static getDerivedStateFromProps(nextProps, prevState) {
    return {
      left: nextProps.left, 
      top: nextProps.top, 
      menuTrigger: nextProps.menuTrigger
    };     
  }

  componentDidUpdate = (prevProps) => {
    if(prevProps.svgWidgets.length != this.props.svgWidgets.length) {
      // Update the tree nodes with the SVG source from the cache 
      this.updateSVGSourceMap(); 
    }

    if(this.props.activeDesignWidget != undefined 
      && prevProps.activeDesignWidget != this.props.activeDesignWidget){
      let widgetTreeNode = this.widgetTreeNodeMap[this.props.activeDesignWidget.name]; 

      // Set the activeDesignWidget so that this node will activate its feedback with 
      // an instance of the widget selected from the design (A specific instance of this widget)
      // and will set the properties in the feedback panel based on that 
      widgetTreeNode.activeDesignWidget = this.props.activeDesignWidget; 

      this.setState({
        treeData: this.state.treeData
      }); 
    }
    else {
      if(prevProps.activeDesignWidget != undefined) {
        let widgetTreeNode = this.widgetTreeNodeMap[prevProps.activeDesignWidget.name]; 

        // Unset the activeDesignWidget property for this node so it goes back to its default state 
        delete widgetTreeNode.activeDesignWidget; 

        this.setState({
          treeData: this.state.treeData
        }); 
      }
    }
  }

  checkSolutionValidityAndUpdateCache = () => {
    // Update shapes cache in localStorage
    this.updateShapeCache(); 

    // Check validity of constraints
    this.checkSolutionValidity();
  }

  constructTreeFromCache = (treeData) => {  
    if(treeData.length) {
      let canvasNode = treeData[0]; 

      // Restore the cosntraints tree from the cached shapes
      this.widgetTreeNodeMap[canvasNode.shape.name] = canvasNode; 

      if(canvasNode.children) {
        for(let i=0; i<canvasNode.children.length; i++) {
          let child = canvasNode.children[i]; 
          this.constructShapeHierarchy(child);
        }
      }

      this.setState(state => ({
        treeData: treeData
      }));
    } 
  }

  updateSVGSourceMap = () => {
    for(let i=0; i < this.props.svgWidgets.length; i++) {
      let svgWidget = this.props.svgWidgets[i]; 
      this.state.svgSourceMap[svgWidget.id] = svgWidget; 
    }

    let svgItem = {
      id: "group", 
      svgData: groupSVG, 
      visible: true
    }

    this.state.svgSourceMap["group"] = svgItem; 

    this.setState({
      svgSourceMap: this.state.svgSourceMap
    });
  }

  constructShapeHierarchy = (treeNode) => {
    this.widgetTreeNodeMap[treeNode.shape.name] = treeNode; 

    if(treeNode.children && treeNode.children.length) {
      for(let i=0; i<treeNode.children.length; i++){
        let child = treeNode.children[i]; 
        this.constructShapeHierarchy(child); 
      }
    }
  }

  renderTree = () => {
    this.setState({
      treeData: this.state.treeData
    }, this.checkSolutionValidityAndUpdateCache); 
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

    let rootTreeNode = {
        key: canvas.name, 
        shape: canvas,
        src: rootNode, 
        disabled: true, 
        children: []
    }; 

    return rootTreeNode; 
  }

  updateShapeCache = () => {
    // Update the entry for the constraintShapesMap in the localStorage cache
    // so we can repopulate the constraints tree on refresh 
    let treeHierarchy = this.state.treeData; 
    let treeHierarchyJSON = JSON.stringify(treeHierarchy); 
    localStorage.setItem('shapeHierarchy', treeHierarchyJSON); 
  }

  getWidget = (shape, src, options={}) => {
    let shapeId = shape.name;
    let highlighted = options.highlighted ? options.highlighted : false; 
    let isContainer = shape.type == "group" || shape.type == "canvas";
    let item = options.item ? options.item : false;
    let typed = options.typed ? options.typed : false;
    let feedback = options.feedback ? options.feedback : [];
    let activeDesignWidget = options.activeDesignWidget ? options.activeDesignWidget : undefined; 

    let typingAlerts = [];
    if(options.typeGroupSize > 1) {
      typingAlerts = this.getWidgetTyping(shapeId, options.typeGroupSize); 
    }

    if(isContainer) {
      return (<ConstraintsCanvasContainerSVGWidget 
                key={shapeId} 
                shape={shape} 
                id={shapeId} 
                source={src}
                highlighted={highlighted}
                isContainer={true}
                feedbackItems={feedback}
                typingAlerts={typingAlerts}
                displayRightClickMenu={this.displayRightClickMenu}
                displayWidgetFeedback={this.displayWidgetFeedback}
                getCurrentShapeSiblings={this.getCurrentShapeSiblings}
                getCurrentShapeIndex={this.getCurrentShapeIndex}
                activeDesignWidget={activeDesignWidget}
                removeWidgetNode={this.removeWidgetNode}
                typed={typed}
                item={item} />);
    }
    return (<ConstraintsCanvasSVGWidget 
              key={shapeId} 
              shape={shape} 
              id={shapeId} 
              source={src}
              feedbackItems={feedback}
              typingAlerts={typingAlerts}
              highlighted={highlighted}
              displayRightClickMenu={this.displayRightClickMenu}
              displayWidgetFeedback={this.displayWidgetFeedback}
              getCurrentShapeSiblings={this.getCurrentShapeSiblings}
              getCurrentShapeIndex={this.getCurrentShapeIndex}
              activeDesignWidget={activeDesignWidget}
              removeWidgetNode={this.removeWidgetNode} />);
  }

  getWidgetFeedbacks = (shape) => {
    // Restore feedback items for locks 
    let feedbackItems = []; 
    if(shape.locks && shape.locks.length) {
      for(let i=0; i<shape.locks.length; i++) {
        let lock = shape.locks[i];
        let action = ConstraintActions.getAction("keep", shape);
        if(action){
          let uniqueId = getUniqueID();
          let message = action["do"].getFeedbackMessage(lock, shape);
          let id = shape.name + "_" + uniqueId; 
          let widgetFeedback = this.getWidgetFeedback(id, shape, action, lock, message);
          feedbackItems.push(widgetFeedback); 
        } 
      }     
    } 

    if(shape.prevents && shape.prevents.length) {
      for(let i=0; i<shape.prevents.length; i++) {
        let prevent = shape.prevents[i];
        let action = ConstraintActions.getAction("prevent", shape);
        if(action){
          let uniqueId = getUniqueID();
          let message = action["do"].getFeedbackMessage(prevent, shape);
          let id = shape.name + "_" + uniqueId; 
          let widgetFeedback = this.getWidgetFeedback(id, shape, action, prevent, message);
          feedbackItems.push(widgetFeedback); 
        } 
      }     
    } 

    return feedbackItems; 
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

  createNewTreeNode = (id, type, source, options={}) => {
    // Creates a new tree node widget and returns it
    let width = options.width ? options.width : 0;
    let height = options.height ? options.height : 0; 
    let shape = this.createConstraintsCanvasShapeObject(id, type, width, height, options); 

    let newTreeNode = {
      key: shape.name, 
      shape: shape, 
      src: source, 
    }; 

    this.widgetTreeNodeMap[shape.name] = newTreeNode; 

    return newTreeNode; 
  }

  getWidgetFeedback = (shapeID, parentShape, action, property, message, highlighted) => {
    return (<WidgetFeedback 
              key={shapeID} 
              type="feedback"
              id={shapeID} 
              parentShape={parentShape}
              action={action}
              property={property}
              message={message} 
              highlighted={highlighted}
              updateConstraintsCanvas={this.updateConstraintsCanvas}/>); 
  }

  getConstraintsCanvasShape = (shapeID) => {
    return this.widgetTreeNodeMap[shapeID].shape; 
  }

  displayWidgetFeedback = (shape, callbacks) => {
    // Call the PageContainer method to open the feedback panel 
    this.props.displayWidgetFeedback(shape, callbacks); 
  }

  displayRightClickMenu = (evt, shapeID) => {
    let node = this.widgetTreeNodeMap[shapeID]; 
    if(node) {
      let selectedAndMultipleSelected = this.state.selectedTreeNodes.indexOf(shapeID) > -1 && this.state.selectedTreeNodes.length > 1
      let isGroup = node.shape.type == "group"; 
      if(!selectedAndMultipleSelected && isGroup) {
        // Check whether the repeat group menu item should be shown 
        let groupSize = this.checkGroupTyping(node);
        node.typedGroupSize = groupSize; 

        let containsGroup = this.containsGroup(node); 
        this.setState({
          rightClickMenuShown: true, 
          rightClickMenuPosition: {
            x: evt.clientX, 
            y: evt.clientY
          }, 
          rightClickShapeID: shapeID, 
          rightClickIsGroup: true, 
          rightClickMenuTypeGroupSize: groupSize, 
          rightClickMenuIsTyped: node.typed, 
          rightClickMenuIsAlternate: node.alternate,
          rightClickMenuContainsGroup: containsGroup
        });         
      } else if(selectedAndMultipleSelected) {
        let containsGroup = this.selectedItemsContainGroup();
        this.setState({
          rightClickMenuShown: true, 
          rightClickMenuPosition: {
            x: evt.clientX, 
            y: evt.clientY
          }, 
          rightClickShapeID: shapeID, 
          rightClickIsGroup: false, 
          rightClickMenuIsTyped: false, 
          rightClickMenuIsAlternate: false,
          rightClickMenuTypeGroupSize: -1, 
          rightClickMenuContainsGroup: containsGroup
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
 
  hideRightClickMenu = () => {
    // Recheck consistency of the solutions after any of the things are set
    this.setState({
      rightClickMenuShown: false
    }); 
  }

  highlightAddedWidget = (shapeId, highlighted) => {
    let treeNode = this.widgetTreeNodeMap[shapeId];
    if(treeNode) {
      treeNode.highlighted = highlighted;

      this.setState(state => ({
        treeData: this.state.treeData
      })); 
    }
  }

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

  getShapeHierarchy = () => {
    let treeNodes = this.state.treeData; 

    // Convert this into a hierarchical structure
    if(treeNodes.length) {
      let rootNode = treeNodes[0]; 
      if(rootNode.children){
        this.getShapeChildren(rootNode); 
      }

      return rootNode.shape; 
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
        // For alternate groups, we do not include the child nodes in the hierarchy. 
        if(child.alternate) {
          // Collapse the alternate group with the set of children as the represntations
          let representations = []; 
          for(let i=0; i<child.children.length; i++) {
            let subchild = child.children[i]; 
            let svg = this.state.svgSourceMap[subchild.shape.id]; 
            representations.push(svg.id); 
          }

          // Store these on the object so that we can iterate through them in the solver
          child.shape.representations = representations; 

          // Get the height/width of the first child to use as the height
          if(child.children.length) {
            let firstChild = child.children[0]; 
            child.shape.alternate_width = firstChild.shape.orig_width; 
            child.shape.alternate_height = firstChild.shape.orig_height;
          }
        }
        else {
          this.getShapeChildren(child);
        }
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
    if(type == "group") {
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

    if (type == "group") {
      shape.children = []; 
    }

    return shape;
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
              correspondingIDs.push(matchingItem.key);
            }

            itemChild.shape.correspondingIDs = correspondingIDs; 
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

      let newGroupNode = this.createNewTreeNode("item", "group", itemSVG, 
        {width: this.defaultNodeWidth, height: this.defaultNodeHeight});

      for(let j=0; j<currGroup.length; j++) {
        currGroup[j].disabled = true;
      }

      newGroupNode.item = true;
      newGroupNode.disabled = true; 
      newGroupNode.shape.item = true;
      newGroupNode.children = currGroup; 
      newChildren.push(newGroupNode); 
    }

    return newChildren; 
  }

  createAlternateGroup = (shapeID) => {
    let node = this.widgetTreeNodeMap[shapeID];
    if(node.shape.type == "group") {
      node.src = alternateSVG; 
      node.shape.alternate = true; 
      node.alternate = true; 
    }
    else {
      // Group the selected elements into an alternate group 
      this.groupSelectedNodes({alternate: true}); 
    }

    this.setState({
      treeData: this.state.treeData
    }, this.checkSolutionValidityAndUpdateCache); 
  }

  removeAlternateGroup = (groupID) => {
    let node = this.widgetTreeNodeMap[groupID]; 
    if(node.shape.type == "group") {
      node.src = groupSVG; 
      node.shape.alternate = false;
      node.shape.representations = []; 
      node.alternate = false;
    }

    this.setState({
      treeData: this.state.treeData
    }, this.checkSolutionValidityAndUpdateCache); 
  }

  createRepeatGroup = (groupID) => {
    let groupNode = this.widgetTreeNodeMap[groupID];
    if(groupNode) {
      groupNode.typed = true; 
      groupNode.src = repeatGridSVG; 
      groupNode.shape.typed = true; 

      let newGroupChildren = this.restructureRepeatGroupChildren(groupNode.children, groupNode.typedGroupSize); 
      groupNode.children = newGroupChildren; 

      this.setState(state => ({
        treeData: this.state.treeData
      }), this.checkSolutionValidityAndUpdateCache); 
    }
  }

  removeRepeatGroup = (groupID) => {
    let groupNode = this.widgetTreeNodeMap[groupID];
   // Ungroup childen from the item containers
    let groupChildren = groupNode.children; 
    if(groupChildren) {
      let toRemove = []
      let index = 0; 
      while(index < groupChildren.length) {
        let childNode = groupChildren[index]; 
        if(childNode.item) {
          for(let i=0; i<childNode.children.length; i++) {
            childNode.children[i].disabled = false;
          }

          groupChildren.splice(index,1); 
          groupChildren.splice(index,0,...childNode.children); 
        }
        index += 1; 
      }
    }

    groupNode.typed = false; 
    groupNode.src = groupSVG; 
    groupNode.shape.typed = false; 

    this.setState({
      treeData: this.state.treeData
    });
  }

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

    // Check whether the parent group should be removed if all its children are gone
    if(!parentNode.children.length && parentNode.shape.type != "canvas") {
      this.removeWidgetNode(parentNode.key);
    }

    // Check if the parent was a repeat group or an item 
    if(parentNode.typed) {
      this.removeRepeatGroup(parentNode.key); 
    }

    if(parentNode.item) {
      let itemParent = this.getParentNodeForKey(parentNode.key, this.state.treeData[0]); 
      if(itemParent.typed) {
        this.removeRepeatGroup(itemParent.key); 
      }
    }

    if(key == this.state.selectedElement) {
      this.setState({
        selectedElement: undefined
      });
    }

    this.setState(state => ({
      treeData: this.state.treeData,
    }), this.checkSolutionValidityAndUpdateCache); 
  }

  closeTypingAlert = (groupID) => {
    return () => {
      // Set the typeGroupSize value to -1 so the alert will no longer be shown.
      let treeNode = this.widgetTreeNodeMap[groupID]; 
      treeNode.typeGroupSize = -1; 

      this.setState(state => ({
        treeData: this.state.treeData
      }));       
    }
  }

  getWidgetTyping = (groupID, groupSize) => {
    let key = getUniqueID();
    return (<WidgetTyping
      key={key} 
      type="typing" 
      groupID={groupID} 
      groupSize={groupSize}
      createRepeatGroup={this.createRepeatGroup} 
      closeTypingAlert={this.closeTypingAlert} />); 
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
      currGroup.push(currChild.shape.type);
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
    for(let i=2; i<=totalFloor; i++) {
      if(total % i == 0){
        sizes.push(i); 
      }
    }

    return sizes;
  }

  containsGroup = (node) => {
    let numChildren = node.children.length; 
    for(let i=0; i<numChildren; i++){
      let child = node.children[i]; 
      if(child.shape.type == "group") {
        return true; 
      }
    }

    return false;
  }

  selectedItemsContainGroup = () => {
    for(let i=0; i<this.state.selectedTreeNodes.length; i++) {
      let selectedNodeKey = this.state.selectedTreeNodes[i]; 
      let treeNode = this.widgetTreeNodeMap[selectedNodeKey]; 
      if(treeNode.shape.type == "group") {
        return true;
      }
    }

    return false;
  }

  checkGroupTyping = (node) => {
    if(node.typed) {
      return -1; 
    }

    // Do the type inference algorithm
    // iterate through each set of possible groupings starting with the greatest common divisor
    let numChildren = node.children.length; 
    let groupSizes = this.getGroupSizes(numChildren);

    for(let i=0; i<groupSizes.length; i++) {
      let groupSize = groupSizes[i];
      if(groupSize >= this.minimumGroupSize) {
        if(this.canSplitIntoGroupOfSize(node, groupSize)) {
          return groupSize;
        }
      }
    }

    return -1;
  }

  groupContainsKey = (treeNode, key) => {
    for(let j=0; j<treeNode.children.length; j++) {
      if(treeNode.children[j].key == key) {
        return true;
      }
    }

    return false;
  }

  groupTreeNodes = (treeNode, keys, alternate=false) => {
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
    let groupType = alternate ? "alternate" : "group"; 
    let groupSrc = alternate ? alternateSVG : groupSVG; 
    let group = this.createNewTreeNode(groupType, "group", groupSrc, 
      {width: this.defaultNodeWidth, height: this.defaultNodeHeight});
    group.children = nodes; 
    group.shape.alternate = alternate; 
    group.alternate = alternate; 

    if(firstIndex != -1) {
      treeNode.children.splice(firstIndex, 0, group);
    }
  }

  groupSelectedNodes = (options={}) => {
    let alternate = options.alternate ? true : false; 

    let firstKey = this.state.selectedTreeNodes[0];
    let parentNode = this.getParentNodeForKey(firstKey, this.state.treeData[0]);
    if(parentNode) {
      this.groupTreeNodes(parentNode, this.state.selectedTreeNodes, alternate);
    }

    // Remove the selected tree nodes after grouping
    this.setState({
      treeData: this.state.treeData, 
      selectedTreeNodes: []
    }, this.checkSolutionValidityAndUpdateCache); 
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
    let parent1 = this.getParentNodeForKey(treeNodeKey1, this.state.treeData[0]); 
    let parent2 = this.getParentNodeForKey(treeNodeKey2, this.state.treeData[0]); 
    if(parent1 && parent2 && parent1.key == parent2.key) {
      return true; 
    }

    return false;
  }

  unselectedSelectedElement = (evt) => {
    let stopped = evt.isPropagationStopped();
    this.setState({
      selectedTreeNodes: [], 
      selectedElement: undefined
    }); 
  }

  onSelected = (selectedKeys, evt) => {
    let selected = selectedKeys[selectedKeys.length-1];
    let selectedNodes = selectedKeys; 
    let selectedElement = selected; 
    if(selected == "canvas") {
      // Ensure that the canvas cannot be selected
      selectedKeys.splice(selectedKeys.length-1, 1); 
      selectedNodes = selectedKeys; 
    }
    else if (evt.nativeEvent && evt.nativeEvent.shiftKey) {
      // Get the last selected node and verify that it has the same parent node as the other 
      // selected nodes
      if(selectedKeys.length > 1) {
        let prev = selectedKeys[selectedKeys.length-2]; 
        if(!this.hasSameParentNode(selected, prev)) {
          selectedNodes = [selected];
        }
        else {
          let parentNode = this.getParentNodeForKey(selected, this.state.treeData[0]);  
          let newSelectedNodes = []; 
          let collect = false;

          // Find the range of elements in bewtween the last two selected nodes
          for(let i=0; i<parentNode.children.length; i++) {
            let child = parentNode.children[i]; 
            if((child.key == prev || child.key == selected) && collect) {
              newSelectedNodes.push(child.key); 
              // Stop collecting
              break;
            }

            if((child.key == prev || child.key == selected) && !collect) {
              collect = true; 
            }

            if(collect) {
              newSelectedNodes.push(child.key); 
            }
          }

          selectedNodes = newSelectedNodes; 
        }

        selectedElement = selected; 
      }
    }   
    else if (evt.nativeEvent && evt.nativeEvent.ctrlKey) {
      // Get the last selected node and verify that it has the same parent node as the other 
      // selected nodes
      let selectedNodes = selectedKeys; 
      if(selectedNodes.length > 1) {
        let prev = selectedNodes[selectedNodes.length-2]; 
        if(!this.hasSameParentNode(selected, prev)) {
          selectedNodes = [selected]; 
        }
      }
      selectedElement = selectedNodes[selectedNodes.length-1]; 
    }
    else {
      // Only have the most recent node selected as shift or ctrl was not pressed
      selectedNodes = [selected]; 
      selectedElement = selected;  
    }

    this.setState({
      selectedTreeNodes: selectedNodes, 
      selectedElement: selectedElement
    }); 
  }

  onDrop = (info) => {
    const dropKey = info.node.props.eventKey;
    const dragKey = info.dragNode.props.eventKey;
    const dropPos = info.node.props.pos.split('-');
    const dropPosition = info.dropPosition - Number(dropPos[dropPos.length - 1]);    
    if(dragKey == "canvas") {
      return;
    }

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

    let droppedOnRepeatGroup = false; 
    if(dropObj.typed) {
      droppedOnRepeatGroup = true; 
    }

    let droppedOnItemGroup = false; 
    if(dropObj.item) {
      droppedOnItemGroup = true; 
    }

    let droppedInItemGroup = false; 
    let parentDropNode = this.getParentNodeForKey(dropObj.key, this.state.treeData[0]); 
    if(parentDropNode && parentDropNode.item) {
      droppedInItemGroup = true; 
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

    // If the node was dropped in a repeat group, we need to remove it as it will no longer match the pattern 
    if(droppedOnRepeatGroup) {
      this.removeRepeatGroup(dropObj); 
    }

    if(droppedOnItemGroup) {
      // Get the parent repeat group node 
      let parentRepeatGroup = this.getParentNodeForKey(dropObj.key, this.state.treeData[0]); 
      this.removeRepeatGroup(parentRepeatGroup);
    }

    if(droppedInItemGroup) {
      let parentRepeatGroup = this.getParentNodeForKey(parentDropNode.key, this.state.treeData[0]); 
      this.removeRepeatGroup(parentRepeatGroup); 
    }

    this.setState({
      treeData: data,
    }, this.checkSolutionValidityAndUpdateCache);
  }

  render () {
    // Gather the set of tree nodes
    const gatherTreeNodes = data => {
      return data.map((item) => {
        let widgetOptions = {
          highlighted: item.highlighted, 
          typed: item.typed, 
          item: item.item, 
          activeDesignWidget: item.activeDesignWidget
        }

        let widgetSource = item.src; 
        if(!widgetSource) {
          if(item.shape.typed) {
            widgetSource = repeatGridSVG; 
          }
          else if(item.shape.alternate) {
            widgetSource = alternateSVG; 
          }
          else if(item.shape.item) {
            widgetSource = itemSVG; 
          } else {
            let widgetSourceNode = this.state.svgSourceMap[item.shape.id]; 
            if(widgetSourceNode) {
              widgetSource = widgetSourceNode.svgData; 
            }
          }
        }

        let widgetFeedbacks = this.getWidgetFeedbacks(item.shape); 
        widgetOptions.feedback = widgetFeedbacks; 
        let widget = this.getWidget(item.shape, widgetSource, widgetOptions); 
        if (item.children && item.children.length) {
          return <TreeNode key={item.key} icon={widget} title={""} disabled={item.disabled}>{gatherTreeNodes(item.children)}</TreeNode>;
        }
        return <TreeNode key={item.key} icon={widget} title={""} disabled={item.disabled} />;
      });
    };

    const treeNodes = gatherTreeNodes(this.state.treeData); 
    const shapes = this.constraintsShapes; 
    const pageFeedbacks = this.state.pageFeedbackWidgets;
    const rightClickMenuPosition = this.state.rightClickMenuPosition; 
    const rightClickMenu = (this.state.rightClickMenuShown ? 
      <GroupingRightClickMenu 
        isGroup={this.state.rightClickIsGroup} 
        groupSelected={this.groupSelectedNodes}
        ungroupSelected={this.ungroupGroup}
        containsGroup={this.state.rightClickMenuContainsGroup}
        typeGroupSize={this.state.rightClickMenuTypeGroupSize}
        createRepeatGroup={this.createRepeatGroup}
        removeRepeatGroup={this.removeRepeatGroup}
        createAlternateGroup={this.createAlternateGroup}
        removeAlternateGroup={this.removeAlternateGroup}
        isTyped={this.state.rightClickMenuIsTyped}
        isAlternate={this.state.rightClickMenuIsAlternate}
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
          <div className="constraints-canvas-container panel-body">
            <div className="constraints-canvas-tree-container"> 
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
                    showIcon={true}
                    autoExpandParent={true}
                    defaultExpandParent={true}
                    defaultExpandAll={true}
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
              </div>
            </div>
            {/*<div className="constraints-canvas-feedback-container">
               <WidgetFeedbackPanel
                selectedElement={this.state.selectedElement}
                selectedElementY={this.state.selectedElementY} />
            </div> */}
          </div>
      </div>
    );
  }
}
