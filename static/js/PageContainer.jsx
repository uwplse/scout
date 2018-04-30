// App.jsx
import React from "react";
import '../css/Canvas.css'; 
import ConstraintsCanvas from "./ConstraintsCanvas"; 
import FabricHelpers from './FabricHelpers.js';
import ConstraintsCanvasMenu from './ConstraintsCanvasMenu'; 
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
    this.updateConstraintsCanvasShape = this.updateConstraintsCanvasShape.bind(this); 

    this.canvas = undefined; 

    // This is the set of design canvases in the design window
    this.state = { 
      designCanvases: [], 
      savedDesignCanvases: [], 
      trashedDesignCanvases: [], 
      constraintChanged: false , 
      designsFound: -1, 
      treeData: [], 
      sidebarOpen: true
    };   

    // Dictionaries for being able to retrieve a design canvas by ID more efficiently
    this.designCanvasMap = {}; 
    this.savedDesignCanvasesMap = {}; 
    this.trashedDesignCanvasesMap = {};

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

  drawWidgetCanvas() {
    this.widgetsCanvas = new fabric.Canvas('widgets-canvas');
    let field = FabricHelpers.getField(20,50,120,40,{'cursor': 'hand', 'selectable': false}); 
    let text = FabricHelpers.getText(20,100,20,{'cursor': 'hand', 'selectable': false}); 
    let button = FabricHelpers.getButton(20,150,120,40,{'cursor': 'hand', 'selectable': false}); 
    field.on('mousedown', this.addShapeToConstraintsCanvas.bind(this, 'field')); 
    text.on('mousedown', this.addShapeToConstraintsCanvas.bind(this, 'text')); 
    button.on('mousedown', this.addShapeToConstraintsCanvas.bind(this, 'button')); 
    this.widgetsCanvas.add(field); 
    this.widgetsCanvas.add(text); 
    this.widgetsCanvas.add(button); 
  }

  drawContainersCanvas() {
    this.containersCanvas = new fabric.Canvas('containers-canvas');
    let group = FabricHelpers.getGroup(10, 10, 120, 40, {
      stroke: '#39a1f4',
      selectable: false, 
      groupType: 'Group'
    });

    group.on('mousedown', this.addShapeToConstraintsCanvas.bind(this, 'group'));

    let label = FabricHelpers.getGroup(10, 70, 120, 40, {
      selectable: false, 
      stroke: 'red', 
      groupType: 'Label'
    });

    label.on('mousedown', this.addShapeToConstraintsCanvas.bind(this, 'labelGroup')); 

    this.containersCanvas.add(group); 
    this.containersCanvas.add(label);
  }

  updateConstraintsCanvasShape(constraintsCanvasShape, designCanvasShape, action, actionType) {
    // First check with the solver that the constraint can be applied
    // If it can be applied, update the corresponding property in the constraints canvas

    // This will make the changes first, then check if the constriant could be applied
    // Consider refactoring so we don't have to do and undo the action
    action.updateConstraintsCanvasShape(constraintsCanvasShape, designCanvasShape);

    // Notify the constraintss canvas
    this.constraintsCanvasRef.current.updateWidgetFeedbacks(constraintsCanvasShape, action, actionType);

    this.setState({
      constraintChanged: true
    });

    // let jsonShapes = this.getShapesJSON(); 
    // var self = this;
    // $.post("/check", {"elements": jsonShapes}, function(requestData) {
    //   if(requestData == "True") {
    //     // At least one constraint has been changed 
    //     // The button to get more designs with the current set of constraints should be disabled. 
    //     self.setState({
    //       errorMessageShown: false
    //     });  
    //   } else {
    //     // Display an error message somewhere (?)
    //     undoAction.updateConstraintsCanvasShape(constraintsCanvasShape, designCanvasShape);  

    //     self.setState({
    //       errorMessageShown: true
    //     });
    //   }
    // }, 'text');
  }

  getDesignCanvasScalingFactor(designCanvasID) {
    if(this.savedDesignCanvasesMap[designCanvasID]) {
      return 0.10; 
    } 
    else if(this.trashedDesignCanvasesMap[designCanvasID]) {
      return 0.10; 
    }

    return 0.5;
  }

  saveDesignCanvas(designCanvasID){
    // Retrieve a design canvas by its ID
    let designCanvas = this.designCanvasMap[designCanvasID]; 

    // Remove it from the list of design canvas components and from the map 
    let designCanvasIndex = this.state.designCanvases.indexOf(designCanvas); 
    this.state.designCanvases.splice(designCanvasIndex, 1); 
    delete this.designCanvasMap[designCanvasID]; 

    // Move the design into the collection of saved design canvas components
    this.state.savedDesignCanvases.push(designCanvas);  
    this.savedDesignCanvasesMap[designCanvasID] = designCanvas; 

    // Update the state
    this.setState({
      designCanvases: this.state.designCanvases, 
      savedDesignCanvases: this.state.savedDesignCanvases
    }); 
  }

  trashDesignCanvas(designCanvasID) {
    // Retrieve a design canvas by its ID
    let designCanvas = this.designCanvasMap[designCanvasID]; 

    // Remove it from the list of design canvas components and from the map 
    let designCanvasIndex = this.state.designCanvases.indexOf(designCanvas); 
    this.state.designCanvases.splice(designCanvasIndex, 1); 
    delete this.designCanvasMap[designCanvasID]; 

    // Move the design into the collection of saved design canvas components
    this.state.trashedDesignCanvases.push(designCanvas);  
    this.trashedDesignCanvasesMap[designCanvasID] = designCanvas; 

    // Update the state
    this.setState({
      designCanvases: this.state.designCanvases, 
      trashedDesignCanvases: this.state.trashedDesignCanvases
    }); 
  }

  getShapesJSON() {
    // Get all of the shapes on the canvas into a collection 
    let shapeObjects = this.constraintsCanvasRef.current.getShapeHierarchy();
    return JSON.stringify(shapeObjects); 
  }

  getExploredSolutionsJSON() {
    let solutions = {}; 

    // Get saved solutions 
    let savedCanvases = this.state.savedDesignCanvases; 
    solutions.saved = []; 
    for(var i=0; i<savedCanvases.length; i++){
      solutions.saved.push({
        elements: savedCanvases[i].props.originalElements
      }); 
    }

    // Get trashed solutions 
    let trashedCanvases = this.state.trashedDesignCanvases; 
    solutions.trashed = []; 
    for(var j=0; j<trashedCanvases.length; j++){
      solutions.trashed.push({
        elements: trashedCanvases[j].props.originalElements
      }); 
    }

    // Get solutions in the design ideas panel 
    let designIdeasCanvases = this.state.designCanvases; 
    solutions.designs = []; 
    for(var k=0; k<designIdeasCanvases.length; k++){
      solutions.designs.push({
        elements: designIdeasCanvases[k].props.originalElements
      })
    }

    return JSON.stringify(solutions); 
  }

  parseSolutions(requestData) {
    let resultsParsed = JSON.parse(requestData); 
    let solutions = resultsParsed.solutions;
    let designCanvasList = this.state.designCanvases; 
    for(let i=0; i<solutions.length; i++) {
      let solution = solutions[i]; 
      let elements = solution.elements; 

      let originalElements = $.extend(true, [], elements);

      // Attach the JSON shapes for this canvas instance to the corresponding constraints canvas shapes
      this.constraintsCanvasRef.current.linkSolutionShapesToConstraintShapes(elements); 

      let designCanvas = <DesignCanvas key={solution.id} id={solution.id} 
                              elements={elements} originalElements={originalElements}
                              updateConstraintsCanvas={this.updateConstraintsCanvasShape}
                              saveDesignCanvas={this.saveDesignCanvas.bind(this)} 
                              trashDesignCanvas={this.trashDesignCanvas.bind(this)}
                              getRelativeDesigns={this.getRelativeDesigns.bind(this)}
                              scalingFactor={this.getDesignCanvasScalingFactor.bind(this)}/>; 
      designCanvasList.push(designCanvas); 
      this.designCanvasMap[solution.id] = designCanvas; 
    }

    let designsFound = solutions.length;
    this.setState({
      designsFound: designsFound,
      designCanvases: designCanvasList, 
      errorMessageShown: false
    });
  }

  getMoreDesigns() {
    // get more designs
    // without changing any new constraints
    let jsonShapes = this.getShapesJSON(); 

    // Get JSON for already retrieved designs/saved/trashed
    let exploredSolutions = this.getExploredSolutionsJSON();
   
   // Send an ajax request to the server 
   // Solve for the new designs
    $.post("/solve", {"elements": jsonShapes, "solutions": exploredSolutions}, this.parseSolutions, 'text');

    // Reset the state of the designs canvas
    this.setState({
      constraintChanged: false
    });
  }

  getRelativeDesigns(elements, action) {
    // get more designs relative to a specific design
    let jsonShapes = this.getShapesJSON(); 

    // Get JSON for already retrieved designs/saved/trashed
    let exploredSolutions = this.getExploredSolutionsJSON();
   
   // Send an ajax request to the server 
   // Solve for the new designs
    $.post("/solve", {
      "elements": jsonShapes, 
      "solutions": exploredSolutions, 
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

  onSetSidebarOpen() {

  }

  // onTreeNodeMoved(arg) {
  //   console.log("test");
  //   let constraintsTreeData = arg.treeData; 
  //   this.setState(state => ({
  //     constraintsTreeData: constraintsTreeData
  //   }));
  // }

  // updateConstraintsTreeState(treeData){
  //   let constraintsState = treeData; 
  //   this.setState({
  //     constraintsTreeData: constraintsState
  //   });
  // }

  render () {
    const designs = this.state.designCanvases;
    const designsFound = this.state.designsFound; 
    const numDesigns = this.state.designCanvases.length; 
    const errorMessageShown = this.state.errorMessageShown; 
    const constraintChanged = this.state.constraintChanged;
    const saved = this.state.savedDesignCanvases; 
    const numSaved = this.state.savedDesignCanvases.length; 
    const trashed = this.state.trashedDesignCanvases; 
    const numTrashed = this.state.trashedDesignCanvases.length; 
    const designsAlertMessage = designsFound > 0 ? "Here " + (designsFound > 1 ? "are" : "is") + " " + designsFound + " very different " + (designsFound > 1 ? "designs" : "design") + ". " : "No more designs found. "; 
  
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
                <canvas id="widgets-canvas" width="200px" height="333px">
                </canvas>
              </div>
            </div>
            <div className="panel panel-default containers-container">
              <div className="panel-heading"> 
                <h3 className="panel-title">Containers</h3>
              </div>  
              <div className="panel-body">         
                <canvas id="containers-canvas" width="200px" height="260px">
                </canvas>
              </div>
            </div>
          </div>
         <div className="panel panel-default constraints-container">
            <div className="panel-heading"> 
              <h3 className="panel-title">Constraints
                <button type="button" className="btn btn-default design-canvas-button" disabled={(designsFound > 0 || designsFound == -1) ? null : "disabled"} onClick={this.getMoreDesigns}>{(numDesigns == 0 ? "Get Designs" : "Show More")}</button>
              </h3>
            </div>
            <div className="constraints-canvas-container"> 
              <ConstraintsCanvas ref={this.constraintsCanvasRef} />
            </div>
           {/*<ConstraintsCanvas ref="constraintsCanvas" />*/}
          </div>
          <div className="panel-group design-canvas-container" id="accordion">
            { saved.length ? (<div className="panel designs-container panel-default">
              <span className="save-icon glyphicon glyphicon-star" aria-hidden="true"></span>
              <div className="panel-body saved-body">
                {saved}
              </div>
            </div>) : null }
            <div className={"panel designs-container " + (constraintChanged ? "panel-danger" : "panel-default")}>
              <div className="design-body">
                {designs}
              </div>
            </div>
            { trashed.length ? (<div className="panel designs-container panel-default">
              <span className="save-icon glyphicon glyphicon-trash" aria-hidden="true"></span>
              <div className="panel-body trashed-body">
                {trashed}
              </div>
            </div>) : null}
          </div>
        </div>
      </div>
    ); 
  }
}