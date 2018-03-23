// App.jsx
import React from "react";
import '../css/Canvas.css'; 
import 'whatwg-fetch'; 
import Canvas from "./Canvas"; 
import FabricHelpers from './FabricHelpers.js';
import 'context-menu';

export default class PageContainer extends React.Component {
  constructor(props) {
  	super(props); 
    this.drawCanvas = this.drawCanvas.bind(this); 
    this.fieldClicked = this.fieldClicked.bind(this); 
    this.textClicked = this.textClicked.bind(this); 
    this.buttonClicked = this.buttonClicked.bind(this); 
    this.getDesigns = this.getDesigns.bind(this); 
    this.parseSolutions = this.parseSolutions.bind(this);
    this.deleteShape = this.deleteShape.bind(this); 

    this.canvas = undefined; 
    this.constraintsTop = 10; 

    // This collection contains the set of shapes on the constraints canvas
    this.constraintsShapes = []; 

    // This is the set of design canvases in the design window
    this.state = { designCanvases: [] }; 
  }

  componentDidMount() {
    // Construct the intial canvas
    this.drawCanvas(); 
  }

  fieldClicked() {
    this.constraintsTop += 50; 
    let top = this.constraintsTop; 
    let left = 20; 

    // Add a new field to the constraints canvas
    let field = FabricHelpers.getField(left, top, 120, 40, {'selectable': true});
    this.constraintsCanvas.add(field); 

    // Set up the JSON object
    let json = {
      "name": _.uniqueId(),
      "label": "field", 
      "type": "field", 
      "shape": field
    }

    this.constraintsShapes.push(json); 

    // Keep track of the currently selected shape 
    field.on("selected", this.selectShape.bind(this, json)); 
    field.on("moving", this.createGroupOnMove.bind(this, json)); 
  }

  textClicked() {
    this.constraintsTop += 50; 
    let top = this.constraintsTop; 
    let left = 20; 

    // Add a new text to the constraints canvas
    let fontSize = 40; 
    let text = FabricHelpers.getInteractiveText(left, top, 40, {'selectable': true});
    this.constraintsCanvas.add(text); 

    // Set up the JSON object
    let json = {
      "name": _.uniqueId(),
      "label": "text", 
      "type": "text", 
      "shape": text
    }

    this.constraintsShapes.push(json); 

    // Keep track of the currently selected shape 
    text.on("selected", this.selectShape.bind(this, json)); 
    text.on("moving", this.createGroupOnMove.bind(this, json)); 
  }

  buttonClicked() {
    this.constraintsTop += 50; 
    let top = this.constraintsTop; 
    let left = 20; 

    // Add a new field to the constraints canvas
    let button = FabricHelpers.getButton(left, top, 120, 40, {'selectable': true});
    this.constraintsCanvas.add(button); 

    // Set up the JSON object
    let json = {
      "name": _.uniqueId(),
      "label": "button", 
      "type": "button", 
      "shape": button, 
    }

    this.constraintsShapes.push(json);  

    // Set up the event handlers
    // button.on('mousedown', this.deleteShape.bind(this, json)); 

    // Keep track of the currently selected shape 
    button.on("selected", this.selectShape.bind(this, json)); 
    button.on("moving", this.createGroupOnMove.bind(this, json)); 
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
    // Check proximity of the shape to other elements 
    let shape_x = shapeJSON.shape.left; 
    let shape_y = shapeJSON.shape.top; 
    let shape_width = shapeJSON.shape.width; 
    let shape_height = shapeJSON.shape.height;

    let overlapping = false;
    for(let i=0; i<this.constraintsShapes.length; i++) {
      if(this.constraintsShapes[i].name != shapeJSON.name && this.constraintsShapes[i].type != "group") {
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
              
              // Adjust the group bounding box
              let groupShape = parentGroup.shape; 
              let groupBoundingBox = this.getGroupBoundingBox(parentGroup); 
              groupShape.set({left: groupBoundingBox.x-5, top: groupBoundingBox.y-5, width: groupBoundingBox.width+10, height: groupBoundingBox.height+10}); 
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

              let groupBoundingBox = this.getGroupBoundingBox(groupJSON); 
              let groupRect = FabricHelpers.getGroup(groupBoundingBox.x-5, groupBoundingBox.y-5, groupBoundingBox.width+10, groupBoundingBox.height+10, {selectable: false});
              groupJSON.shape = groupRect; 

              this.constraintsCanvas.add(groupRect); 
              this.constraintsShapes.push(groupJSON); 
              this.constraintsCanvas.sendToBack(groupRect);
            }

            // Don't look at any more shapes 
            break;
          }
        }
      }
    }

    console.log("overlapping: " + overlapping); 

    if(!overlapping) {
      // If the shape was in a group and that group had only two children, remove the group 
      if(shapeJSON.parent) {
        let parentGroup = shapeJSON.parent; 
        if(parentGroup.children.length <= 2) {
          for(let i=0; i<parentGroup.children.length; i++) {
            let child = parentGroup.children[i]; 
            child.parent = undefined; 
          }

          this.deleteShape(parentGroup); 
        }else {
          // Remove the child from this group and update the group bounds
          shapeJSON.parent = undefined; 
          let shapeIndex = parentGroup.children.indexOf(shapeJSON); 
          parentGroup.children.splice(shapeIndex, 1); 

          // Update the parent group bounding box
          let groupBoundingBox = this.getGroupBoundingBox(parentGroup); 
          parentGroup.shape.set({left: groupBoundingBox.x-5, top: groupBoundingBox.y-5, width: groupBoundingBox.width+10, height: groupBoundingBox.height+10}); 
        }
      }
    }
   }

  drawCanvas() {
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
      let jsonShape = {}; 
      let fabricShape = shape.shape; 

      jsonShape["name"] = shape.name; 
      jsonShape["label"] = shape.label;
      jsonShape["type"] = shape.type;

      jsonShape["location"] = {
        "x": fabricShape.left, 
        "y": fabricShape.top
      }

      let roundedWidth = Math.round(fabricShape.width); 
      let roundedHeight = Math.round(fabricShape.height); 
      jsonShape["size"] = {
        "width": roundedWidth, 
        "height": roundedHeight

      }

      if (shape.children) {
        jsonShape.children = []; 
        for(let i=0; i<shape.children.length; i++) {
          jsonShape.children.push(shape.children[i].name); 
        }
      }

      shapeJSON.push(jsonShape); 
    }  

    return JSON.stringify(shapeJSON)
  }

  parseSolutions(requestData) {
    let resultsParsed = JSON.parse(requestData); 
    let solutions = resultsParsed.elements;
    let designCanvasList = this.state.designCanvases; 
    for(let i=0; i<solutions.length; i++) {
      let solution = solutions[i]; 
      let elements = solution.elements; 
      designCanvasList.push(<Canvas key={solution.id} id={solution.id} elements={elements} />); 
    }

    this.setState({
      designCanvases: designCanvasList
    });
  }

  getDesigns() {
    let jsonShapes = this.getShapesJSON(); 
   
   // Send an ajax request to the server 
   // Solve for the new designs
    $.post("/solve", {"elements": jsonShapes}, this.parseSolutions, 'text');
  }

  render () {
    const designs = this.state.designCanvases;
    return (
      <div className="page-container">
        <nav className="navbar navbar-default">
         <div className="container-fluid">
          <div className="navbar-header">
            <button type="button" className="btn btn-default navbar-btn" onClick={this.getDesigns}>Get Designs</button>
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
              <canvas id="constraints-canvas" width="375px" height="667px">
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