// App.jsx
import React from "react";
import '../css/Canvas.css'; 
import ConstraintsCanvas from "./ConstraintsCanvas"; 
import FabricHelpers from './FabricHelpers.js';
import DesignCanvas from './DesignCanvas';
import Sidebar from 'react-sidebar';
import $ from 'jquery';

export default class PageContainer extends React.Component {
  constructor(props) {
  	super(props); 
    this.drawWidgetCanvas = this.drawWidgetCanvas.bind(this); 
    this.drawContainersCanvas = this.drawContainersCanvas.bind(this);
    this.getMoreDesigns = this.getMoreDesigns.bind(this); 
    this.parseSolutions = this.parseSolutions.bind(this);
    this.updateConstraintsCanvasFromDesignCanvas = this.updateConstraintsCanvasFromDesignCanvas.bind(this); 
    this.updateConstraintsCanvas = this.updateConstraintsCanvas.bind(this);
    this.getConstraintsCanvasShape = this.getConstraintsCanvasShape.bind(this);

    this.canvas = undefined; 

    // This is the set of design canvases in the design window
    this.state = { 
      solutions: [],
      constraintChanged: false , 
      designsFound: -1, 
      treeData: [], 
      sidebarOpen: true,
    };   

    // Dictionaries for being able to retrieve a design canvas by ID more efficiently
    this.solutionsMap ={};

    this.constraintsCanvasRef = React.createRef();
  }

  componentDidMount() {
    // Draw the canvas for adding new widgets to the constraints canvas
    this.drawWidgetCanvas(); 
    this.drawContainersCanvas(); 
  }

  // Update the addedShapes property on the constraints canvas to notify it to create new shapes
  // for a shape of this type
  addShapeToConstraintsCanvas(type) {
    this.constraintsCanvasRef.current.addShapeOfTypeToCanvas(type);
  }

  getDesignCanvas(id, elements, savedState, validity, invalidated) {
    return (<DesignCanvas 
              key={id} id={id} 
              elements={elements}
              savedState={savedState}
              valid={validity}
              invalidated={invalidated}
              getConstraintsCanvasShape={this.getConstraintsCanvasShape}
              updateConstraintsCanvas={this.updateConstraintsCanvasFromDesignCanvas}
              saveDesignCanvas={this.saveDesignCanvas.bind(this)} 
              trashDesignCanvas={this.trashDesignCanvas.bind(this)}
              getRelativeDesigns={this.getRelativeDesigns.bind(this)}/>); 
  }

  getConstraintsCanvasShape(shapeId) {
    return this.constraintsCanvasRef.current.getConstraintsCanvasShape(shapeId); 
  }

  drawWidgetCanvas() {
    this.widgetsCanvas = new fabric.Canvas('widgets-canvas');
    let field = FabricHelpers.getField(15,50,120,40,{'cursor': 'hand', 'selectable': false}); 
    let text = FabricHelpers.getText(15,100,20,{'cursor': 'hand', 'selectable': false}); 
    let button = FabricHelpers.getButton(15,150,120,40,{'cursor': 'hand', 'selectable': false}); 
    field.on('mousedown', this.addShapeToConstraintsCanvas.bind(this, 'field')); 
    text.on('mousedown', this.addShapeToConstraintsCanvas.bind(this, 'text')); 
    button.on('mousedown', this.addShapeToConstraintsCanvas.bind(this, 'button')); 
    this.widgetsCanvas.add(field); 
    this.widgetsCanvas.add(text); 
    this.widgetsCanvas.add(button); 
  }

  drawContainersCanvas() {
    this.containersCanvas = new fabric.Canvas('containers-canvas');
    let group = FabricHelpers.getGroup(15, 10, 120, 40, {
      stroke: '#39a1f4',
      selectable: false, 
      groupType: 'Group', 
      strokeDashArray: [5,5]
    });

    group.on('mousedown', this.addShapeToConstraintsCanvas.bind(this, 'group'));

    let label = FabricHelpers.getGroup(15, 70, 120, 40, {
      selectable: false, 
      stroke: 'red', 
      groupType: 'Label', 
      strokeDashArray: [5,5]
    });

    label.on('mousedown', this.addShapeToConstraintsCanvas.bind(this, 'labelGroup')); 

    this.containersCanvas.add(group); 
    this.containersCanvas.add(label);
  }

  checkSolutionValidity() {
    let jsonShapes = this.getShapesJSON(); 

    // Get all of the solutions so far to check their validity 
    let prevSolutions = JSON.stringify(this.state.solutions);

    var self = this;
    $.post("/check", {"elements": jsonShapes, "solutions": prevSolutions}, function(requestData) {
      let requestParsed = JSON.parse(requestData); 
      let valid = requestParsed.result; 
      if(!valid) {
        self.setState({
          errorMessageShown: true
        }); 
      }else {
        // TODO: Figure out what we are doing with this
        self.setState({
          constraintChanged: true
        });
      }

      self.updateSolutionValidity(requestParsed.solutions);
    }); 
  }

  updateConstraintsCanvasFromDesignCanvas(designCanvasShape, action, actionType) {
    // Retrieve the shape object in the constraints tree and apply teh updates
    let constraintsCanvasShape = this.getConstraintsCanvasShape(designCanvasShape.name);
    action[actionType].updateConstraintsCanvasShape(constraintsCanvasShape, designCanvasShape);

    // Notify the constraintss canvas to remove the widget feedback from the tree
    this.constraintsCanvasRef.current.updateWidgetFeedbacks(constraintsCanvasShape, action, actionType);

    // Check the validity of the current constraints and update valid state of solutions
    this.checkSolutionValidity();
  }

  updateSolutionValidity(solutions) {
    // Update the state of each solution to display the updated valid/invalid state
    for(var i=0; i<solutions.length; i++) {
      let solution = solutions[i]; 
      let designSolution = this.solutionsMap[solution.id]; 
      designSolution.valid = solution.valid; 
    }

    // Update the state
    this.setState({
      solutions: this.state.solutions
    }); 
  }

  updateConstraintsCanvas(constraintsCanvasShape, action) {
    action["undo"].updateConstraintsCanvasShape(constraintsCanvasShape, undefined);

    // Notify the constraintss canvas
    this.constraintsCanvasRef.current.updateWidgetFeedbacks(constraintsCanvasShape, action, "undo");

    // Check for the validity of current state of constriants, and update valid state of solutions
    this.checkSolutionValidity(); 
  }

  saveDesignCanvas(designCanvasID){
    // Retrieve the solution corresponding to the design canvas ID
    let solution = this.solutionsMap[designCanvasID]; 
    solution.saved = 1;  

    // Update the state
    this.setState({
      solutions: this.state.solutions
    }); 
  }

  trashDesignCanvas(designCanvasID) {
    // Retrieve a design canvas by its ID
    let solution = this.solutionsMap[designCanvasID];
    solution.saved = -1; 

    // Update the state
    this.setState({
      solutions: this.state.solutions
    }); 
  }

  getShapesJSON() {
    // Get all of the shapes on the canvas into a collection 
    let shapeObjects = this.constraintsCanvasRef.current.getShapeHierarchy();
    return JSON.stringify(shapeObjects); 
  }

  parseSolutions(requestData) {
    let resultsParsed = JSON.parse(requestData); 
    let solutions = resultsParsed.solutions;
    let designCanvasList = this.state.mainDesignCanvases; 
    for(let i=0; i<solutions.length; i++) {
      let solution = solutions[i];  
      this.solutionsMap[solution.id] = solution; 
    }

    let designsFound = solutions.length;

    // Go through previous solutions and see which ones need to be invalidated
    for(let i=0; i<this.state.solutions.length; i++) {
      let designSolution = this.state.solutions[i]; 
      if(!designSolution.valid) {
        // Invalidate the solution which means it should be moved into the right side panel 
        designSolution.invalidated = true; 
      }
    }

    this.setState({
      designsFound: designsFound,
      solutions: solutions.concat(this.state.solutions), 
      errorMessageShown: false 
    });
  }

  getMoreDesigns() {
    // get more designs
    // without changing any new constraints
    let jsonShapes = this.getShapesJSON(); 

    // Get JSON for already retrieved designs/saved/trashed
    let prevSolutions = JSON.stringify(this.state.solutions);
   
   // Send an ajax request to the server 
   // Solve for the new designs
    $.post("/solve", {"elements": jsonShapes, "solutions": prevSolutions}, this.parseSolutions, 'text');

    // Reset the state of the designs canvas
    this.setState({
      constraintChanged: false
    });
  }

  getRelativeDesigns(elements, action) {
    // get more designs relative to a specific design
    let jsonShapes = this.getShapesJSON(); 

    // Get JSON for already retrieved designs/saved/trashed
    let prevSolutions = JSON.stringify(this.state.solutions);
   
   // Send an ajax request to the server 
   // Solve for the new designs
    $.post("/solve", {
      "elements": jsonShapes, 
      "solutions": prevSolutions, 
      "relative_designs": {
        "relative_design": elements, 
        "relative_action": action
      }
    }, this.parseSolutions, 'text');

    // Reset the state of the designs canvas
    this.setState({
      constraintChanged: false
    });
  }

  render () {
    var self = this;
    const designsFound = this.state.designsFound; 
    const errorMessageShown = this.state.errorMessageShown; 
    const constraintChanged = this.state.constraintChanged;
    const designsAlertMessage = designsFound > 0 ? "Here " + (designsFound > 1 ? "are" : "is") + " " + designsFound + " very different " + (designsFound > 1 ? "designs" : "design") + ". " : "No more designs found. "; 
    const savedCanvases = this.state.solutions.filter(function(solution) { return (solution.saved == 1); })
              .map(function(solution) {
                  return self.getDesignCanvas(solution.id, solution.elements, solution.saved, solution.valid, solution.invalidated); 
                }); 

    const designCanvases = this.state.solutions.filter(function(solution) { return (solution.saved == 0 && (!solution.invalidated)); }) 
              .map(function(solution) {
                  return self.getDesignCanvas(solution.id, solution.elements, solution.saved, solution.valid, solution.invalidated); 
                }); 

    const trashedCanvases = this.state.solutions.filter(function(solution) { return solution.saved == -1; })
              .map(function(solution) {
                    if(solution.saved == -1) {
                      return self.getDesignCanvas(solution.id, solution.elements, solution.saved, solution.valid, solution.invalidated); 
                    }
                });

    const invalidatedCanvases = this.state.solutions.filter(function(solution) { return solution.invalidated == true; })
        .map(function(solution) {
              if(solution.invalidated == true) {
                return self.getDesignCanvas(solution.id, solution.elements, solution.saved, solution.valid, solution.invalidated); 
              }
          });      
    return (
      <div className="page-container">
        <nav className="navbar navbar-default">
         <div className="container-fluid">
          <div className="navbar-header">
            <h2>C.N.P.</h2>
          </div>
         </div>
        </nav>
        <div className="bottom">
          <div className="components-container">
            <div className="panel panel-default widgets-container">
              <div className="panel-heading"> 
                <h3 className="panel-title">Widgets</h3>
              </div>  
              <div className="panel-body">         
                <canvas id="widgets-canvas" width="150px" height="333px">
                </canvas>
              </div>
            </div>
            <div className="panel panel-default containers-container">
              <div className="panel-heading"> 
                <h3 className="panel-title">Containers</h3>
              </div>  
              <div className="panel-body">         
                <canvas id="containers-canvas" width="150px" height="260px">
                </canvas>
              </div>
            </div>
          </div>
         <div className="panel panel-default constraints-container">
            <div className="panel-heading"> 
              <h3 className="panel-title">Constraints
                <button type="button" className="btn btn-default design-canvas-button" disabled={(designsFound > 0 || designsFound == -1) ? null : "disabled"} onClick={this.getMoreDesigns}>{(designsFound == 0 ? "Get Designs" : "Show More")}</button>
              </h3>
            </div>
            <div className="constraints-canvas-container"> 
              <ConstraintsCanvas ref={this.constraintsCanvasRef} updateConstraintsCanvas={this.updateConstraintsCanvas}/>
            </div>
           {/*<ConstraintsCanvas ref="constraintsCanvas" />*/}
          </div>
          <div className="panel-group design-canvas-container">
            <div className="left-container">
              { savedCanvases.length ? (<div className="panel designs-container panel-default">
                <span className="save-icon glyphicon glyphicon-star" aria-hidden="true"></span>
                <div className="panel-body saved-body">
                  {savedCanvases}
                </div>
              </div>) : null }
              <div className="panel designs-container panel-default">
                <div className="design-body">
                  {designCanvases}
                </div>
              </div>
              { trashedCanvases.length ? (<div className="panel designs-container panel-default">
                <span className="save-icon glyphicon glyphicon-trash" aria-hidden="true"></span>
                <div className="panel-body trashed-body">
                  {trashedCanvases}
                </div>
              </div>) : null }
            </div>
            {invalidatedCanvases.length ? (<div className="right-container"> 
              <div className="panel invalid-container panel-default"> 
                <span className="save-icon glyphicon glyphicon-asterisk" aria-hidden="true"></span>
                <div className="panel-body invalidated-body">
                  {invalidatedCanvases}
                </div>
              </div>
            </div>) : null}
          </div>
        </div>
      </div>
    ); 
  }
}