// App.jsx
import React from "react";
import '../css/Canvas.css'; 
import ConstraintsCanvas from "./ConstraintsCanvas"; 
import FabricHelpers from './FabricHelpers.js';
import ConstraintsCanvasMenu from './ConstraintsCanvasMenu'; 
import DesignCanvas from './DesignCanvas';

export default class PageContainer extends React.Component {
  constructor(props) {
  	super(props); 
    this.drawWidgetCanvas = this.drawWidgetCanvas.bind(this); 
    this.getMoreDesigns = this.getMoreDesigns.bind(this); 
    this.parseSolutions = this.parseSolutions.bind(this);
    this.updateConstraintsCanvasShape = this.updateConstraintsCanvasShape.bind(this); 

    this.canvas = undefined; 

    // This is the set of design canvases in the design window
    this.state = { designCanvases: [], constraintChanged: false };   
  }

  componentDidMount() {
    // Draw the canvas for adding new widgets to the constraints canvas
    this.drawWidgetCanvas(); 
  }

  // Update the addedShapes property on the constraints canvas to notify it to create new shapes
  // for a shape of this type
  addShapeToConstraintsCanvas(type) {
    this.refs.constraintsCanvas.addShapeOfTypeToCanvas(type);
  }

  drawWidgetCanvas() {
    this.widgetsCanvas = new fabric.Canvas('widgets-canvas');
    let field = FabricHelpers.getField(20,50,120,40,{'cursor': 'hand', 'selectable': false}); 
    let text = FabricHelpers.getText(20,150,40,{'cursor': 'hand', 'selectable': false}); 
    let button = FabricHelpers.getButton(20,250,120,40,{'cursor': 'hand', 'selectable': false}); 
    field.on('mousedown', this.addShapeToConstraintsCanvas.bind(this, 'field')); 
    text.on('mousedown', this.addShapeToConstraintsCanvas.bind(this, 'text')); 
    button.on('mousedown', this.addShapeToConstraintsCanvas.bind(this, 'button')); 
    this.widgetsCanvas.add(field); 
    this.widgetsCanvas.add(text); 
    this.widgetsCanvas.add(button); 
  }

  getShapesJSON() {
    // Get all of the shapes on the canvas into a collection 
    let shapeJSON = []; 
    let shapeObjects = this.refs.constraintsCanvas.getShapeObjects();
    for(var i=0; i<shapeObjects.length; i++) {
      let shape = shapeObjects[i]; 
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
        if(shape.type == "field"){
          roundedWidth = Math.round(shape.lineShape.width * shape.lineShape.scaleX);
          roundedHeight = shape.lineShape.top - fabricShape.top; 
        }

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

      if(shape.labels) {
        jsonShape.labels = shape.labels.name;
        delete jsonShape.labelsGroup; 
      }

      jsonShape.parent = undefined; 
      shapeJSON.push(jsonShape); 
    }  

    return JSON.stringify(shapeJSON); 
  }

  updateConstraintsCanvasShape(constraintsCanvasShape, designCanvasShape, action, undoAction) {
    // First check with the solver that the constraint can be applied
    // If it can be applied, update the corresponding property in the constraints canvas

    // This will make the changes first, then check if the constriant could be applied
    // Consider refactoring so we don't have to do and undo the action
    action.updateConstraintsCanvasShape(constraintsCanvasShape, designCanvasShape);

    // Notify the constraintss canvas
    this.refs.constraintsCanvas.updateConstraintsCanvasShape(constraintsCanvasShape)

    this.setState({
      constraintChanged: true
    });

    let jsonShapes = this.getShapesJSON(); 
    var self = this;
    $.post("/check", {"elements": jsonShapes}, function(requestData) {
      if(requestData == "True") {
        // At least one constraint has been changed 
        // The button to get more designs with the current set of constraints should be disabled. 
        self.setState({
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
      this.refs.constraintsCanvas.linkSolutionShapesToConstraintShapes(elements); 
      designCanvasList.push(<DesignCanvas key={solution.id} id={solution.id} elements={elements} updateConstraintsCanvas={this.updateConstraintsCanvasShape}/>); 
    }

    this.setState({
      designCanvases: designCanvasList, 
      errorMessageShown: false
    });
  }

  getMoreDesigns() {
    this.state.designCanvases = [];

    // get more designs
    // without changing any new constraints
    let jsonShapes = this.getShapesJSON(); 
   
   // Send an ajax request to the server 
   // Solve for the new designs
    $.post("/solve", {"elements": jsonShapes}, this.parseSolutions, 'text');

    // Reset the state of the designs canvas
    this.setState({
      constraintChanged: false
    });
  }

  render () {
    const designs = this.state.designCanvases;
    const errorMessageShown = this.state.errorMessageShown; 
    const constraintChanged = this.state.constraintChanged;
    return (
      <div className="page-container">
        <nav className="navbar navbar-default">
         <div className="container-fluid">
          <div className="navbar-header">
            <button type="button" className="btn btn-default navbar-btn" onClick={this.getMoreDesigns}>Get Designs</button>
            { errorMessageShown ? <div className="alert alert-danger constraint-error-message">Constraint couldn't be applied. (HORRIBLE USER EXPERIENCE)</div> : null }
          </div>
         </div>
        </nav>
        <div className="bottom">
          <div className="panel panel-default widgets-container">
            <div className="panel-heading"> 
              <h3 className="panel-title">Widgets</h3>
            </div>  
            <div className="panel-body">         
              <canvas id="widgets-canvas" width="200px" height="667px">
              </canvas>
            </div>
          </div>
          <div className="panel panel-default constraints-container">
            <div className="panel-heading"> 
              <h3 className="panel-title">Constraints</h3>
            </div>
            <ConstraintsCanvas ref="constraintsCanvas" />
          </div>
          <div className={"panel designs-container " + (constraintChanged ? "panel-danger" : "panel-default")}>
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