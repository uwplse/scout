import React from "react";
import ConstraintsCanvasMenu from "./ConstraintsCanvasMenu"; 
import FabricHelpers from './FabricHelpers.js';

export default class ConstraintsCanvas extends React.Component {
  constructor(props) {
  	super(props); 

    // Bound functions
    this.createConstraintsCanvasShapeObject.bind(this);

    // This collection contains the set of shapes on the constraints canvas
    this.constraintsShapes = []; 
    this.constraintsShapesByName = {}; // Dictionary collection of shapes for key-value access
    this.pageLevelShape = undefined;

    this.constraintsTop = 10;  
    this.unparentedShapes = [];

    this.canvasHeight = 667; 
    this.canvasWidth = 375; 

    this.state = { 
      constraintModified: false, 
      activeCanvasMenus: [], 
      menuShown:{},
    }; 

    // mapping of shape types to handler functions
    this.shapeAddHandlers = {
      'text': this.addTextToCanvas.bind(this), 
      'button': this.addButtonToCanvas.bind(this), 
      'field': this.addFieldToCanvas.bind(this)
    }; 
  }

  componentDidMount() {
    this.constraintsCanvas = new fabric.Canvas('constraints-canvas'); 
    let canvasElement = document.getElementById("constraints-canvas-container"); 
    canvasElement.addEventListener("keydown", this.deleteSelectedShape.bind(this)); 

    // Create an object to represent the page level object
    let page = {
      "name": _.uniqueId(),
      "type": "page", 
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


    this.constraintsShapes.push(page); 
    this.constraintsShapesByName[page["name"]] = page; 
    this.pageLevelShape = page; 
  }

  getShapeObjects() {
    return this.constraintsShapes; 
  }

  addShapeOfTypeToCanvas(type) {
    this.shapeAddHandlers[type]();
  }

  linkSolutionShapesToConstraintShapes(elements) {
    for(var i=0; i<elements.length; i++) {
      let element = elements[i]; 
      let elementName = element["name"]; 
      element.constraintsCanvasShape = this.constraintsShapesByName[elementName];
    }
    return elements; 
  }

  addFieldToCanvas() {
    let shape = this.createConstraintsCanvasShapeObject("field"); 

    // Add a new field to the constraints canvas
    let location = this.getConstraintsCanvasShapeLocation()
    let field = FabricHelpers.getInteractiveField(location.left, location.top, 120, 40, {'selectable': true});

    this.addShapeToConstraintsCanvas(shape, field.field); 

    shape.lineShape = field.line; 
    shape["label"] = field.field.text; 
    this.constraintsCanvas.add(field.line); 
    this.constraintsCanvas.bringToFront(field.line); 

    field.line.on("selected", this.selectShape.bind(this, shape)); 

    field.field.on("moving", function(evt){
      // Update the position of the line to follow the position of the label 
      field.line.set({left: field.field.left, top: field.field.top + 25}); 
    });

    field.line.on("moving", function(evt){
      // Update the position of the line to follow the position of the label 
      field.field.set({left: field.line.left, top: field.line.top - 25}); 
    });

    field.field.on("modified", function() {
      shape["label"] = field.field.text; 
    }); 
  }

  addTextToCanvas() {
    // Add a new text to the constraints canvas
    let shape = this.createConstraintsCanvasShapeObject("text");

    let location = this.getConstraintsCanvasShapeLocation(); 
    let fontSize = 40; 
    let text = FabricHelpers.getInteractiveText(location.left, location.top, fontSize, {'selectable': true});
   
    this.addShapeToConstraintsCanvas(shape, text);

    text.on("modified", function() {
      shape["label"] = text.text;
    }); 
  }

  addButtonToCanvas() {
    let shape = this.createConstraintsCanvasShapeObject("button"); 

    // Add a new field to the constraints canvas
    let location = this.getConstraintsCanvasShapeLocation(); 
    let button = FabricHelpers.getInteractiveButton(location.left, location.top, 120, 40, {'selectable': true});
    
    this.addShapeToConstraintsCanvas(shape, button.button);

    // Add the text of the label as a property on the button JSON 
    shape.labelShape = button.label; 
    shape["label"] = button.label.text; 
    this.constraintsCanvas.add(button.label); 
    this.constraintsCanvas.bringToFront(button.label); 

    button.button.on("moving", function() {
      let left = button.button.left + (button.button.width * button.button.scaleX - button.label.width * button.label.scaleX)/2; 
      let top = button.button.top + (button.button.height * button.button.scaleY - button.label.height * button.label.scaleY)/2; 
      button.label.set({ left: left, top: top}); 
    }); 

    button.label.on("modified", function() {
      shape["label"] = button.label.text;
    }); 
  }

  getConstraintsCanvasShapeLocation() {
    this.constraintsTop += 50; 
    let top = this.constraintsTop; 
    let left = 20;  
    return { top: top, left: left }; 
  }

  createConstraintsCanvasShapeObject(type) {  
    // Set up the object that will keep the current state of this shape
    // And be passed with a set of information to the server for solving
    let shape = {
      "name": _.uniqueId(),
      "label": type, 
      "type": type
    }

    this.constraintsShapes.push(shape); 
    this.constraintsShapesByName[shape["name"]] = shape; 
    this.state.menuShown[shape.name] = false;

    // Also need to push the shape onto the children of the page level object
    this.pageLevelShape.children.push(shape); 

    return shape;
  }

  addShapeToConstraintsCanvas(shape, fabricShape) {
    shape.shape = fabricShape; 
    this.constraintsCanvas.add(fabricShape); 

    // Keep track of the currently selected shape 
    fabricShape.on("selected", this.selectShape.bind(this, shape)); 
    fabricShape.on("moving", this.moveShape.bind(this, shape)); 
  }

  deleteShape(shape) {
    // Remove the shape from the canvas
    this.constraintsCanvas.remove(shape.shape); 
    let index = this.constraintsShapes.indexOf(shape); 
    this.constraintsShapes.splice(index, 1); 

    if (shape.type == "field") {
      this.constraintsCanvas.remove(shape.lineShape);
    }

    if(shape.type == "button"){
      this.constraintsCanvas.remove(shape.labelShape);
    }
  }

  deleteSelectedShape(evt) {
    if (evt.keyCode == 8 || evt.keyCode == 46) {
      this.deleteShape(this.selectedShape);      
    }

    // Also close the menu
    this.deleteConstraintsMenu(this.selectedShape);
  }

  deleteShapeFromObjectChildren(shape, objectJSON) {
    let index = objectJSON.children.indexOf(shape); 
    objectJSON.children.splice(index, 1);   
  }

  selectShape(shape) {
    this.selectedShape = shape; 
  }

  updateConstraintsCanvasShape(shape) {    
    // Update the state of the menu associated with the shape
    let newMenuState = this.state.menuShown; 
    newMenuState[shape.name] = true;

    this.setState({
      menuShown: newMenuState
    }); 
  }

  deleteConstraintsMenu(shape){
    let delete_i = -1; 
    for(var i=0; i<this.state.activeCanvasMenus.length; i++){
      if(shape == this.state.activeCanvasMenus[i].props.menuTrigger) {
        delete_i = i; 
      }
    }

    if (delete_i != -1) {
      this.state.activeCanvasMenus.splice(delete_i,1); 
    }

    // Remove the state of its menu from the map of menu states
    delete this.state.menuShown[shape.name];
 
    this.setState({
      activeCanvasMenus: this.state.activeCanvasMenus,
      menuShown: this.state.menuShown
    });
  }

  distanceWithinGroupingThreshold(x1,y1,width1,height1,x2,y2,width2,height2) {
    // return the distance between the shapes 
    let padding = 10; 
    if(!(x1 > (x2 + width2 + padding) || y1 > (y2 + height2 + padding) || x2 > (x1 + width1 + padding) || y2 > (y1 + height1 + padding))) {
      // They are overlapping 
      return true;
    }

    return false;
  }

  distanceWithinLabelsThreshold(x1,y1,width1,height1,x2,y2,width2,height2) {
    // return the distance between the shapes 
    let padding = 20; 
    if(!(x1 > (x2 + width2 + padding) || y1 > (y2 + height2 + padding) || x2 > (x1 + width1 + padding) || y2 > (y1 + height1 + padding))) {
      // They are overlapping 
      return true;
    }

    return false; 
  }

  // toLeft(x1,y1,width1,height1,x2,y2,width2,height2) {
  //   let padding = 20;
  //   let right1 = x1 + width1; 
  //   let bottom2 = y2 + height2; 
  //   let bottom1 = y1 + height1; 
  //   if(right1 > (x2 - padding) && right1 <= x2) {
  //     // The shape is to the left hand side within the range for creating the labels constraint
  //     if((y1 >= y2 && y1 <= bottom2) || (bottom1 >= y2 && bottom1 <= bottom2) 
  //       || ((y1 <= y2) && (bottom1 >= bottom2 ))) {
  //       // The bottom or top is overlapping with the shape as well
  //       return true;
  //     }
  //   }

  //   return false;
  // }

  moveShape(shape) {
    // Check proximity of the shape to other elements 
    let shape_x = shape.shape.left; 
    let shape_y = shape.shape.top; 
    let shape_width = shape.shape.width; 
    let shape_height = shape.shape.height;

    let grouping = false;
    let labels = false;
    for(let i=0; i<this.constraintsShapes.length; i++) {
      if(this.constraintsShapes[i].name != shape.name && this.constraintsShapes[i].type != "page") {
        let cShape_x = this.constraintsShapes[i].shape.left; 
        let cShape_y = this.constraintsShapes[i].shape.top; 
        let cShape_width = this.constraintsShapes[i].shape.width; 
        let cShape_height = this.constraintsShapes[i].shape.height; 

        if(this.constraintsShapes[i].type == "field") {
          cShape_width = this.constraintsShapes[i].lineShape.width; 
          cShape_height = this.constraintsShapes[i].lineShape.top - cShape_y; 
        }

        if (this.constraintsShapes[i].type != "group" 
          && this.distanceWithinGroupingThreshold(shape_x,shape_y,shape_width,shape_height,cShape_x,cShape_y,cShape_width,cShape_height)) {
          grouping = true;
          if(!shape.parent){
            if (this.constraintsShapes[i].parent) {
              let parentGroup = this.constraintsShapes[i].parent; 
              // Move this shape into the group and update the group bounding box
              this.addShapeToGroup(shape, parentGroup);              
            }
            else {
              this.addShapeToNewGroup(this.constraintsShapes[i], shape); 

              // Don't look at any more shapes 
            }
          }
          break;
        }
        else if (shape.type == "text" && this.distanceWithinLabelsThreshold(shape_x,shape_y,shape_width,shape_height, cShape_x, cShape_y, cShape_width, cShape_height)) {
          labels = true;
          // A labels relationship can only be created with a text element
          // Here is where we should create the labels relationship
          if(!shape.labels) {
            this.addShapeToLabelsGroup(shape, this.constraintsShapes[i]);            
          }

          break;
        }
      }
    }

    if(!labels && shape.type == "text" && shape.labels) {
      // Delete the group shape from the canvas
      this.constraintsCanvas.remove(shape.labelsGroup); 
      delete shape.labels; 
      delete shape.labelsGroup; 
    }

    if(!grouping) {
      // If the shape was in a group and that group had only two children, remove the group 
      if(shape.parent) {
        let parentGroup = shape.parent; 
        if(parentGroup.children.length <= 2) {
          for(let i=0; i<parentGroup.children.length; i++) {
            let child = parentGroup.children[i]; 
            child.parent = undefined; 

            // TODO: hierarchies of groups
            this.pageLevelShape.children.push(child); 
          }

          this.deleteShape(parentGroup); 
        } else {
          // Remove the child from this group and update the group bounds
          shape.parent = undefined; 
          let shapeIndex = parentGroup.children.indexOf(shape); 
          parentGroup.children.splice(shapeIndex, 1); 

          // Append it back to the page level object children for now (Until we support hierarchies of groups)
          this.pageLevelShape.children.push(shape); 

          // Update the parent group bounding box
          let groupBoundingBox = this.getGroupBoundingBox(parentGroup); 
          parentGroup.shape.set({left: groupBoundingBox.x-5, top: groupBoundingBox.y-5, width: groupBoundingBox.width+10, height: groupBoundingBox.height+10}); 
        }
      }
    }
  }

  // Returns the bounding box for a group from the location and sizes of its children
  getGroupBoundingBox(group) {
    let x = -1; 
    let y = -1; 
    let bottom = -1; 
    let right = -1; 
    for(let i=0; i<group.children.length; i++) {
      let child = group.children[i];  
      if (x==-1 || child.shape.left < x) {
        x = child.shape.left; 
      }

      if (y==-1 || child.shape.top < y) {
        y = child.shape.top; 
      }

      let childBottom = child.shape.top + child.shape.height * child.shape.scaleY; 
      if(child.type == "field") {
        childBottom = child.lineShape.top; 
      }

      if (bottom==-1 || childBottom > bottom) {
        bottom = childBottom; 
      }

      let childRight = child.shape.left + child.shape.width * child.shape.scaleX; 
      if(child.type == "field") {
        childRight = child.lineShape.left + child.lineShape.width * child.lineShape.scaleX;
      }

      if (right==-1 || childRight > right) {
        right = childRight; 
      }
    }

    return { x: x, y: y, width: right-x, height: bottom-y }; 
  }

  // Adds a new shape into an existing group
  addShapeToGroup(shape, parentGroup) {
    shape.parent = parentGroup; 
    parentGroup.children.push(shape); 

    // Delete it from the page level children
    this.deleteShapeFromObjectChildren(shape, this.pageLevelShape); 
    
    // Adjust the group bounding box
    let groupShape = parentGroup.shape; 
    let groupBoundingBox = this.getGroupBoundingBox(parentGroup); 
    groupShape.set({
      left: groupBoundingBox.x-10, 
      top: groupBoundingBox.y-10, 
      width: groupBoundingBox.width+20, 
      height: groupBoundingBox.height+20
    }); 
  }

  addShapeToLabelsGroup(shape, labeledShape) {
    let shapeToLabel = labeledShape; 
    if(shape.parent) {
      shapeToLabel = shape.parent; 
    }

    shape.labels = shapeToLabel; 

    // Make a new group shape
    // It wont' be added to the page, but just used to calculate the bounding box
    let group = {
      "children": []
    }

    group.children.push(shape); 
    group.children.push(shapeToLabel);

    // Create a new group shape to be the bounding box 
    let groupBoundingBox = this.getGroupBoundingBox(group); 
    let groupRect = FabricHelpers.getGroup(groupBoundingBox.x-10, groupBoundingBox.y-10, groupBoundingBox.width+20, groupBoundingBox.height+20, {
      selectable: false, 
      stroke: 'red'
    }); 

    // Add them to the page collection of shape objects
    shape.labelsGroup = groupRect; 
    this.constraintsCanvas.add(groupRect); 

    // Move the group to the back layer
    this.constraintsCanvas.sendToBack(groupRect);
  }

  // Adds two shapes into a new group and adds the new group to the canvas
  addShapeToNewGroup(shape1, shape2) {
    // Create a new group for the parent container
    let group = {
      "name": _.uniqueId(),
      "type": "group", 
      "children": []
    }

    shape1.parent = group; 
    shape2.parent = group; 
    group.children.push(shape1); 
    group.children.push(shape2); 

    // Remove both children from the page level object
    this.deleteShapeFromObjectChildren(shape1, this.pageLevelShape); 
    this.deleteShapeFromObjectChildren(shape2, this.pageLevelShape); 
    this.pageLevelShape.children.push(group); 

    // Create a new group shape to be the bounding box 
    let groupBoundingBox = this.getGroupBoundingBox(group); 
    let groupRect = FabricHelpers.getGroup(groupBoundingBox.x-10, groupBoundingBox.y-10, groupBoundingBox.width+20, groupBoundingBox.height+20, {
      selectable: false, 
      stroke: 'blue'
    });

    group.shape = groupRect; 

    // Add them to the page collection of shape objects
    this.constraintsCanvas.add(groupRect); 
    this.constraintsShapes.push(group); 
    this.constraintsShapesByName[group["name"]] = group; 

    // Move the group to the back layer
    this.constraintsCanvas.sendToBack(groupRect);
  }

  createConstraintsCanvasShapeMenu(shape){
    // Show the context menu. 
    let constraintsCanvasBoundingBox = document.getElementById("constraints-canvas").getBoundingClientRect();

    let left = 0; 
    let top = 0; 
    if(shape.location) {
      left = constraintsCanvasBoundingBox.x + shape.location.x; 
      top = constraintsCanvasBoundingBox.y + shape.location.y;
    }

    let fabricShape = shape.shape; 
    if(fabricShape){
      left = constraintsCanvasBoundingBox.x + fabricShape.left + fabricShape.width + 5; 
      top = constraintsCanvasBoundingBox.y + fabricShape.top;       
    }

    if(shape.type == "field"){
      left = constraintsCanvasBoundingBox.x + shape.lineShape.left + shape.lineShape.width + 5;
    }

    return <ConstraintsCanvasMenu key={shape.name} menuID={shape.name} left={left} top={top} 
                                      menuShown={this.state.menuShown[shape.name]} menuTrigger={shape} />; 
  }

  closeActiveMenus(){
    let menuClosed = false;
    for (var key in this.state.menuShown) {
      // check if the property/key is defined in the object itself, not in parent
      if (this.state.menuShown.hasOwnProperty(key)) {           
          if(this.state.menuShown[key]) {
            this.state.menuShown[key] = false;
            menuClosed = true;
          }
      }
    }

    if(menuClosed){
      let menuState = this.state.menuShown; 
      this.setState({
        menuShown: menuState
      });    
    }
  }

  render () {
    const shapes = this.constraintsShapes; 
    // Process the queue of shapes to add to the canvas
	  return (
      <div className="panel-body" id="constraints-canvas-container" tabIndex="1">
        <div className="constraints-canvas-menus">
        {shapes.map(function(shape, index){
             return this.createConstraintsCanvasShapeMenu(shape);
          }.bind(this))
        }
        </div>
        <canvas id="constraints-canvas" width={this.canvasWidth + "px"} height={this.canvasHeight + "px"}>
        </canvas>
      </div>
    );
  }
}
