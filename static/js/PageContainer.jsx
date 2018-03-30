// App.jsx
import React from "react";
import '../css/Canvas.css'; 
import 'whatwg-fetch'; 
import Canvas from "./Canvas"; 
import FabricHelpers from './FabricHelpers.js';
import ConstraintsCanvasMenu from './ConstraintsCanvasMenu'; 

export default class PageContainer extends React.Component {
  constructor(props) {
  	super(props); 
    this.drawWidgetCanvas = this.drawWidgetCanvas.bind(this); 
    this.fieldClicked = this.fieldClicked.bind(this); 
    this.textClicked = this.textClicked.bind(this); 
    this.buttonClicked = this.buttonClicked.bind(this); 
    this.getMoreDesigns = this.getMoreDesigns.bind(this); 
    this.getDesignsWithNewConstraints = this.getDesignsWithNewConstraints.bind(this); 
    this.parseSolutions = this.parseSolutions.bind(this);
    this.deleteShape = this.deleteShape.bind(this); 
    this.updateConstraintsCanvasShape = this.updateConstraintsCanvasShape.bind(this); 

    this.canvas = undefined; 
    this.constraintsTop = 10; 

    // This collection contains the set of shapes on the constraints canvas
    this.constraintsShapes = []; 
    this.constraintsShapesByName = {}; // Dictionary collection of shapes for key-value access
    this.pageLevelShape = undefined; 

    // This is the set of design canvases in the design window
    this.state = { designCanvases: [], constraintModified: false, menuShown: false, activeCanvasMenu: undefined, menuPosition: { x: 0, y: 0 } }; 
  
    this.unparentedShapes = [];
  }

  componentDidMount() {
    // Draw the canvas for adding new widgets to the constraints canvas
    this.drawWidgetCanvas(); 

    // Create an object to represent the page level object
    // these will be where we keep the page level constraints
    let pageJSON = {
      "name": _.uniqueId(),
      "type": "page", 
      "children": []
    }

    this.constraintsShapes.push(pageJSON); 
    this.constraintsShapesByName[pageJSON["name"]] = pageJSON; 
    this.pageLevelShape = pageJSON; 
  }

  displayConstraintsMenu(jsonShape) {
    // check whether the current menu needs to be closed
    if(this.state.menuShown) {
      this.setState({
        activeCanvasMenu: undefined, 
        menuShown: false
      }); 
    }

    // Show the context menu. 
    let componentBoundingBox = this.refs["constraints-canvas"].getBoundingClientRect();

    let shape = jsonShape.shape; 
    this.setState({
        activeCanvasMenu: <ConstraintsCanvasMenu menuTrigger={jsonShape} />,
        menuShown: true, 
        menuPosition: {
          x: componentBoundingBox.x + shape.left + shape.width + 5, 
          y: componentBoundingBox.y + shape.top
        }
    });
  }

  hideConstraintsMenu() {
    if(this.state.menuShown) {
      this.setState({
        activeCanvasMenu: undefined, 
        menuShown: false
      }); 
    }
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
    let json = {
      "name": _.uniqueId(),
      "label": type, 
      "type": type
    }

    this.constraintsShapes.push(json); 
    this.constraintsShapesByName[json["name"]] = json; 

    // Also need to push the shape onto the children of the page level object
    this.pageLevelShape.children.push(json); 

    return json;
  }

  addShapeToConstraintsCanvas(shapeJSON, fabricShape) {
    shapeJSON.shape = fabricShape; 
    this.constraintsCanvas.add(fabricShape); 

    // Keep track of the currently selected shape 
    fabricShape.on("selected", this.selectShape.bind(this, shapeJSON)); 
    fabricShape.on("moving", this.createGroupOnMove.bind(this, shapeJSON)); 

    // Register a mouseover handler to display a dialog with the current constraints
    fabricShape.on("mousedown", this.displayConstraintsMenu.bind(this, shapeJSON)); 
  }

  fieldClicked() {
    let shapeJSON = this.createConstraintsCanvasShapeObject("field"); 

    // Add a new field to the constraints canvas
    let location = this.getConstraintsCanvasShapeLocation()
    let field = FabricHelpers.getInteractiveField(location.left, location.top, 120, 40, {'selectable': true});


    this.addShapeToConstraintsCanvas(shapeJSON, field.field); 

    shapeJSON.lineShape = field.line; 
    shapeJSON["label"] = field.field.text; 
    this.constraintsCanvas.add(field.line); 
    this.constraintsCanvas.bringToFront(field.line); 

    field.field.on("moving", function(evt){
      // Update the position of the line to follow the position of the label 
      field.line.set({left: field.field.left, top: field.field.top + 25}); 
    });

    field.line.on("moving", function(evt){
      // Update the position of the line to follow the position of the label 
      field.field.set({left: field.line.left, top: field.line.top - 25}); 
    });

    field.field.on("modified", function() {
      shapeJSON["label"] = field.field.text; 
    }); 
  }

  textClicked() {
    // Add a new text to the constraints canvas
    let shapeJSON = this.createConstraintsCanvasShapeObject("text");

    let location = this.getConstraintsCanvasShapeLocation(); 
    let fontSize = 40; 
    let text = FabricHelpers.getInteractiveText(location.left, location.top, fontSize, {'selectable': true});
   
    this.addShapeToConstraintsCanvas(shapeJSON, text);

    text.on("modified", function() {
      shapeJSON["label"] = text.text;
    }); 
  }

  buttonClicked() {
    let shapeJSON = this.createConstraintsCanvasShapeObject("button"); 

    // Add a new field to the constraints canvas
    let location = this.getConstraintsCanvasShapeLocation(); 
    let button = FabricHelpers.getInteractiveButton(location.left, location.top, 120, 40, {'selectable': true});
    
    this.addShapeToConstraintsCanvas(shapeJSON, button.button);

    // Add the text of the label as a property on the button JSON 
    shapeJSON.labelShape = button.label; 
    shapeJSON["label"] = button.label.text; 
    this.constraintsCanvas.add(button.label); 
    this.constraintsCanvas.bringToFront(button.label); 

    button.button.on("moving", function() {
      let left = button.button.left + (button.button.width - button.label.width)/2; 
      let top = button.button.top + (button.button.height - button.label.height)/2; 
      button.label.set({ left: left, top: top}); 
    }); 

    button.label.on("moving", function() {
      let left = button.label.left - (button.button.width - button.label.width)/2; 
      let top = button.label.top - (button.button.height - button.label.height)/2; 
      button.button.set({ left: left, top: top}); 
    }); 

    var self = this;
    button.button.on("selected", function() {
      self.constraintsCanvas.sendToBack(button.button); 
    });  

    button.label.on("modified", function() {
      shapeJSON["label"] = button.label.text;
    }); 
  }

  deleteShape(shapeJSON) {
    // Remove the shape from the canvas
    this.constraintsCanvas.remove(shapeJSON.shape); 
    let index = this.constraintsShapes.indexOf(shapeJSON); 
    this.constraintsShapes.splice(index, 1); 
  }

  deleteSelectedShape(evt) {
    if (evt.keyCode == 8 || evt.keyCode == 46) {
      this.deleteShape(this.selectedShape);      
    }

    // Also close the menu
    this.hideConstraintsMenu();
  }

  deleteShapeFromObjectChildren(shapeJSON, objectJSON) {
    let index = objectJSON.children.indexOf(shapeJSON); 
    objectJSON.children.splice(index, 1);   
  }

  selectShape(shapeJSON) {
    this.selectedShape = shapeJSON; 
  }

  overlapping(x1,y1,width1,height1,x2,y2,width2,height2) {
    // return the distance between the shapes 
    if(!(x1 > (x2 + width2) || y1 > (y2 + height2) || x2 > (x1 + width1) || y2 > (y1 + height1))) {
      // They are overlapping 
      return true;
    }

    return false;
  }

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

      let childBottom = child.shape.top + child.shape.height; 
      if (bottom==-1 || childBottom > bottom) {
        bottom = childBottom; 
      }

      let childRight = child.shape.left + child.shape.width; 
      if (right==-1 || childRight > right) {
        right = childRight; 
      }
    }

    return { x: x, y: y, width: right-x, height: bottom-y }; 
  }

  createGroupOnMove(shapeJSON) {
    // check whether the current menu needs to be closed
    if(this.state.menuShown) {
      this.setState({
        activeCanvasMenu: undefined, 
        menuShown: false
      }); 
    }

    // Check proximity of the shape to other elements 
    let shape_x = shapeJSON.shape.left; 
    let shape_y = shapeJSON.shape.top; 
    let shape_width = shapeJSON.shape.width; 
    let shape_height = shapeJSON.shape.height;

    let overlapping = false;
    for(let i=0; i<this.constraintsShapes.length; i++) {
      if(this.constraintsShapes[i].name != shapeJSON.name && this.constraintsShapes[i].type != "group" 
        && this.constraintsShapes[i].type != "page") {
        let cShape_x = this.constraintsShapes[i].shape.left; 
        let cShape_y = this.constraintsShapes[i].shape.top; 
        let cShape_width = this.constraintsShapes[i].shape.width; 
        let cShape_height = this.constraintsShapes[i].shape.height; 
        if (this.overlapping(shape_x,shape_y,shape_width,shape_height,cShape_x,cShape_y,cShape_width,cShape_height)) {
          overlapping = true;
          if(!shapeJSON.parent){
            if (this.constraintsShapes[i].parent) {
              let parentGroup = this.constraintsShapes[i].parent; 
              shapeJSON.parent = parentGroup; 
              parentGroup.children.push(shapeJSON); 

              // Delete it from the page level children
              this.deleteShapeFromObjectChildren(shapeJSON, this.pageLevelShape); 
              
              // Adjust the group bounding box
              let groupShape = parentGroup.shape; 
              let groupBoundingBox = this.getGroupBoundingBox(parentGroup); 
              groupShape.set({left: groupBoundingBox.x-10, top: groupBoundingBox.y-10, width: groupBoundingBox.width+20, height: groupBoundingBox.height+20}); 
            }
            else {
              // Create a new group for the parent container
              let groupJSON = {
                "name": _.uniqueId(),
                "type": "group", 
                "children": []
              }

              this.constraintsShapes[i].parent = groupJSON; 
              shapeJSON.parent = groupJSON; 
              groupJSON.children.push(this.constraintsShapes[i]); 
              groupJSON.children.push(shapeJSON); 

              // Remove both children from the page level object
              this.deleteShapeFromObjectChildren(shapeJSON, this.pageLevelShape); 
              this.deleteShapeFromObjectChildren(this.constraintsShapes[i], this.pageLevelShape); 
              this.pageLevelShape.children.push(groupJSON); 

              // Reconfigure the bounding box
              let groupBoundingBox = this.getGroupBoundingBox(groupJSON); 
              let groupRect = FabricHelpers.getGroup(groupBoundingBox.x-10, groupBoundingBox.y-10, groupBoundingBox.width+20, groupBoundingBox.height+20, {selectable: false, stroke: 'blue'});
              groupJSON.shape = groupRect; 
              groupRect.on("mousedown", this.displayConstraintsMenu.bind(this, groupJSON)); 

              // Add them to the page collection of shape objects
              this.constraintsCanvas.add(groupRect); 
              this.constraintsShapes.push(groupJSON); 
              this.constraintsShapesByName[groupJSON["name"]] = groupJSON; 

              // Move the group to the back layer
              this.constraintsCanvas.sendToBack(groupRect);
            }

            // Don't look at any more shapes 
            break;
          }
        }
      }
    }

    if(!overlapping) {
      // If the shape was in a group and that group had only two children, remove the group 
      if(shapeJSON.parent) {
        let parentGroup = shapeJSON.parent; 
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
          shapeJSON.parent = undefined; 
          let shapeIndex = parentGroup.children.indexOf(shapeJSON); 
          parentGroup.children.splice(shapeIndex, 1); 

          // Append it back to the page level object children for now (Until we support hierarchies of groups)
          this.pageLevelShape.children.push(shapeJSON); 

          // Update the parent group bounding box
          let groupBoundingBox = this.getGroupBoundingBox(parentGroup); 
          parentGroup.shape.set({left: groupBoundingBox.x-5, top: groupBoundingBox.y-5, width: groupBoundingBox.width+10, height: groupBoundingBox.height+10}); 
        }
      }
    }
   }

  drawWidgetCanvas() {
    this.widgetsCanvas = new fabric.Canvas('widgets-canvas');
    let field = FabricHelpers.getField(20,50,120,40,{'cursor': 'hand', 'selectable': false}); 
    let text = FabricHelpers.getText(20,150,40,{'cursor': 'hand', 'selectable': false}); 
    let button = FabricHelpers.getButton(20,250,120,40,{'cursor': 'hand', 'selectable': false}); 
    field.on('mousedown', this.fieldClicked); 
    text.on('mousedown', this.textClicked); 
    button.on('mousedown', this.buttonClicked); 
    this.widgetsCanvas.add(field); 
    this.widgetsCanvas.add(text); 
    this.widgetsCanvas.add(button); 


    this.constraintsCanvas = new fabric.Canvas('constraints-canvas'); 
    let canvasElement = document.getElementById("constraints-canvas-container"); 
    canvasElement.addEventListener("keydown", this.deleteSelectedShape.bind(this)); 
  }

  getShapesJSON() {
    // Get all of the shapes on the canvas into a collection 
    let shapeJSON = []; 
    for(var i=0; i<this.constraintsShapes.length; i++) {
      let shape = this.constraintsShapes[i]; 
      let jsonShape = Object.assign({}, shape); 
      jsonShape.shape = undefined; 

      let fabricShape = shape.shape; 
      if(fabricShape) {
        if(!jsonShape["location"]) {
          jsonShape["location"] = {
            "x": fabricShape.left, 
            "y": fabricShape.top
          }
        }

        let roundedWidth = Math.round(fabricShape.width * fabricShape.scaleX); 
        let roundedHeight = Math.round(fabricShape.height * fabricShape.scaleY); 
        jsonShape["size"] = {
          "width": roundedWidth, 
          "height": roundedHeight

        }        
      }

      // Replace the child references with their IDs before sending them to the server
      if (shape.children) {
        jsonShape.children = []; 
        for(let i=0; i<shape.children.length; i++) {
          jsonShape.children.push(shape.children[i].name); 
        }
      }

      jsonShape.parent = undefined; 
      shapeJSON.push(jsonShape); 
    }  

    return JSON.stringify(shapeJSON); 
  }

  linkSolutionShapesToConstraints(elements) {
    for(var i=0; i<elements.length; i++) {
      let element = elements[i]; 
      let elementName = element["name"]; 
      element.constraintsCanvasShape = this.constraintsShapesByName[elementName];
    }
    return elements; 
  }

  updateConstraintsCanvasShape(constraintsCanvasShape, designCanvasShape, action, undoAction) {
    // First check with the solver that the constraint can be applied
    // If it can be applied, update the corresponding property in the constraints canvas

    // This will make the changes first, then check if the constriant could be applied
    // Consider refactoring so we don't have to do and undo the action
    action.updateConstraintsCanvasShape(constraintsCanvasShape, designCanvasShape);

    let jsonShapes = this.getShapesJSON(); 
    var self = this;
    $.post("/check", {"elements": jsonShapes}, function(requestData) {
      if(requestData == "True") {
        // At least one constraint has been changed 
        // The button to get more designs with the current set of constraints should be disabled. 
        self.setState({
          constraintModified: true, 
          errorMessageShown: false
        });  
      } else {
        // Display an error message somewhere (?)
        undoAction.updateConstraintsCanvasShape(constraintsCanvasShape, designCanvasShape);  

        self.setState({
          errorMessageShown: true
        });
      }
    }, 'text');
  }

  parseSolutions(requestData) {
    let resultsParsed = JSON.parse(requestData); 
    let solutions = resultsParsed.elements;
    let designCanvasList = this.state.designCanvases; 
    for(let i=0; i<solutions.length; i++) {
      let solution = solutions[i]; 
      let elements = solution.elements; 
      
      // Attach the JSON shapes for this canvas instance to the corresponding constraints canvas shapes
      this.linkSolutionShapesToConstraints(elements); 
      designCanvasList.push(<Canvas key={solution.id} id={solution.id} elements={elements} updateConstraintsCanvas={this.updateConstraintsCanvasShape}/>); 
    }

    this.setState({
      designCanvases: designCanvasList, 
      errorMessageShown: false
    });
  }

  getMoreDesigns() {
    // get more designs
    // without changing any new constraints
    let jsonShapes = this.getShapesJSON(); 
   
   // Send an ajax request to the server 
   // Solve for the new designs
    $.post("/solve", {"elements": jsonShapes}, this.parseSolutions, 'text');
  }

  getDesignsWithNewConstraints() {
    // Clear out the current set of designs 
    // TODO: Need some way of ensuring the same set of designs do not get brought back again
    // this has to be handled in the server
    this.state.designCanvases = []; // Don't need to setState here since we will call it when rendering the new designs?
 
    // Get designs with new constraints
    let jsonShapes = this.getShapesJSON(); 

    // Send an ajax request to the server 
    // Solve for the new designs
    $.post("/solve", {"elements": jsonShapes}, this.parseSolutions, 'text');
 }

  render () {
    const designs = this.state.designCanvases;
    const constraintModified = this.state.constraintModified; 
    const menuPosition = this.state.menuPosition; 
    const menuShown = this.state.menuShown; 
    const activeCanvasMenu = this.state.activeCanvasMenu; 
    const errorMessageShown = this.state.errorMessageShown; 
    return (
      <div className="page-container">
        <nav className="navbar navbar-default">
         <div className="container-fluid">
          <div className="navbar-header">
            <button type="button" className="btn btn-default navbar-btn" disabled={constraintModified} onClick={this.getMoreDesigns}>Get More Designs</button>
            <button type="button" className="btn btn-default navbar-btn" disabled={!constraintModified} onClick={this.getDesignsWithNewConstraints}>Update Designs from Constraints</button>
            { errorMessageShown ? <div className="alert alert-danger constraint-error-message">Constraint couldn't be applied. (HORRIBLE USER EXPERIENCE)</div> : null }
          </div>
         </div>
        </nav>
        <div className="bottom">
          <div className="panel panel-primary widgets-container">
            <div className="panel-heading"> 
              <h3 className="panel-title">Widgets</h3>
            </div>  
            <div className="panel-body">         
              <canvas id="widgets-canvas" width="200px" height="667px">
              </canvas>
            </div>
          </div>
          <div className="panel panel-primary constraints-container">
            <div className="panel-heading"> 
              <h3 className="panel-title">Constraints</h3>
            </div>
            <div className="panel-body" id="constraints-canvas-container" tabIndex="1">
              <div style={{left: menuPosition.x, top: menuPosition.y}} className={"canvas-menu-container " + (menuShown ? "" : "hidden")}>
                {activeCanvasMenu}
              </div>
              <canvas ref="constraints-canvas" id="constraints-canvas" width="375px" height="667px">
              </canvas>
            </div>
          </div>
          <div className="panel panel-primary designs-container">
            <div className="panel-heading"> 
              <h3 className="panel-title">Designs</h3>
            </div>
            <div className="panel-body design-body">
              {designs}
            </div>
          </div>
        </div>
      </div>
    ); 
  }
}