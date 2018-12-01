// App.jsx
import React from "react";
import '../css/bootstrap.min.css';
import '../css/Canvas.css'; 
import '../css/PageContainer.css';
import ConstraintsCanvas from "./ConstraintsCanvas"; 
import WidgetsContainer from "./WidgetsContainer"; 
import Constants from './Constants'; 
import DesignCanvas from './DesignCanvas';
import SmallDesignCanvas from './SmallDesignCanvas';
import DesignCanvasContainer from './DesignCanvasContainer'; 
import { DragDropContextProvider } from 'react-dnd'; 
import HTML5Backend from 'react-dnd-html5-backend';
import $ from 'jquery';
import uuidv4 from 'uuid/v4'; 
import SVGInline from "react-svg-inline"; 
import ConstraintsCanvasSVGWidget from './ConstraintsCanvasSVGWidget';
import pageLogo from '../assets/logo.svg';
import groupSVG from '../assets/illustrator/groupContainer.svg';

export default class PageContainer extends React.Component {
  constructor(props) {
  	super(props); 

    // This should only be called at max once after the timeout. 
    this.checkSolutionValidity = _.debounce(this.checkSolutionValidity, 1000); 

    this.canvas = undefined; 

    // This is the set of design canvases in the design window
    this.state = { 
      solutions: [],
      designsFound: -1, 
      showDesignsAlert: false, 
      currentPallette: 'hollywood', 
      droppedFiles: [], 
      svgWidgets: [], 
      zoomedDesignCanvasID: undefined 
    };   

    // Dictionaries for being able to retrieve a design canvas by ID more efficiently
    this.solutionsMap = {};

    this.constraintsCanvasRef = React.createRef();

    this.prevTime = undefined; 
  }

  closeRightClickMenus = () => {
    // Close all of the right click menus in response to a click on the PageContainer
    if(this.constraintsCanvasRef) {
      this.constraintsCanvasRef.current.closeRightClickMenu(); 
    }

    for(var i=0; i<this.state.solutions.length; i++) {
      let canvasID = "design-canvas-" + this.state.solutions[i].id; 
      let designCanvas = this.refs[canvasID]; 
      if(designCanvas) {
        designCanvas.hideMenu();
      }
    }
  }

  // Update the addedShapes property on the constraints canvas to notify it to create new shapes
  // for a shape of this type
  addShapeToConstraintsCanvas = (id, src, type, width, height) => {
    return () => {
      this.constraintsCanvasRef.current.addShapeToCanvas(id, src, type, width, height);
    }
  }

  clearShapesFromConstraintsCanvas = () => {
    this.constraintsCanvasRef.current.clearShapesFromCanvas(); 
  }

  getDesignCanvas = (solution, id, zoomed=false, linkedSolutionId=undefined) => {
    return (<DesignCanvas 
              key={id} 
              id={id} 
              ref={"design-canvas-" + id}
              elements={solution.elements}
              savedState={solution.saved}
              valid={solution.valid}
              conflicts={solution.conflicts}
              added={solution.added}
              removed={solution.removed}
              zoomed={zoomed}
              linkedSolutionId={linkedSolutionId}
              invalidated={solution.invalidated}
              svgWidgets={this.state.svgWidgets}
              getConstraintsCanvasShape={this.getConstraintsCanvasShape}
              updateConstraintsCanvas={this.updateConstraintsCanvasFromDesignCanvas}
              highlightAddedWidget={this.highlightAddedWidget}
              highlightWidgetFeedback={this.highlightWidgetFeedback}
              saveDesignCanvas={this.saveDesignCanvas} 
              trashDesignCanvas={this.trashDesignCanvas}
              zoomInOnDesignCanvas={this.zoomInOnDesignCanvas}
              getRelativeDesigns={this.getRelativeDesigns}
              closeRightClickMenus={this.closeRightClickMenus} />); 
  }

  getSmallDesignCanvas = (solution, id, zoomed=false) => {
    return (<SmallDesignCanvas 
              key={id} 
              id={id} 
              elements={solution.elements}
              savedState={solution.saved}
              valid={solution.valid}
              conflicts={solution.conflicts}
              added={solution.added}
              removed={solution.removed}
              zoomed={zoomed}
              invalidated={solution.invalidated}
              svgWidgets={this.state.svgWidgets}
              getConstraintsCanvasShape={this.getConstraintsCanvasShape}
              updateConstraintsCanvas={this.updateConstraintsCanvasFromDesignCanvas}
              highlightAddedWidget={this.highlightAddedWidget}
              highlightWidgetFeedback={this.highlightWidgetFeedback}
              saveDesignCanvas={this.saveDesignCanvas} 
              trashDesignCanvas={this.trashDesignCanvas}
              zoomInOnDesignCanvas={this.zoomInOnDesignCanvas}
              getRelativeDesigns={this.getRelativeDesigns}
              closeRightClickMenus={this.closeRightClickMenus} />); 
  }

  checkSolutionValidity = (options={}) => {
    let currTime = Date.now()
    if(this.prevTime) {
      let diff = currTime - this.prevTime; 
      console.log(diff/1000); 
    }

    this.prevTime = currTime; 

    let getDesigns = options.getDesigns ? true : false; 
    if(!getDesigns) {
      // Only check for validity of the current solutions
      let jsonShapes = this.getShapesJSON(); 

      // Get all of the solutions so far to check their validity 
      if(this.state.solutions.length) {
        let prevSolutions = JSON.stringify(this.state.solutions);

        $.post("/check", {"elements": jsonShapes, "solutions": prevSolutions}, (requestData) => {
          let requestParsed = JSON.parse(requestData); 
          let valid = requestParsed.result; 
          if(!valid) {
            this.setState({
              errorMessageShown: true
            }); 
          }

          this.updateSolutionValidity(requestParsed.solutions);
        });         
      }
    }
    else {
      // Get design solutions for the current set of constraints
      this.getMoreDesigns();
    }
  }

  getMoreDesigns = () => {
    // get more designs
    // without changing any new constraints
    let jsonShapes = this.getShapesJSON(); 

    // Get JSON for already retrieved designs/saved/trashed
    let prevSolutions = JSON.stringify(this.state.solutions);
   
   // Send an ajax request to the server 
   // Solve for the new designs
    $.post("/solve", {"elements": jsonShapes, "solutions": prevSolutions}, this.parseSolutions, 'text');
  }

  getConstraintsCanvasShape = (shapeId) => {
    return this.constraintsCanvasRef.current.getConstraintsCanvasShape(shapeId); 
  }

  highlightWidgetFeedback = (shapeId, lock, highlighted) => {
    this.constraintsCanvasRef.current.highlightWidgetFeedback(shapeId, lock, highlighted);
  }

  highlightAddedWidget = (shapeId, highlighted) => {
    this.constraintsCanvasRef.current.highlightAddedWidget(shapeId, highlighted);
  }

  updateConstraintsCanvasFromDesignCanvas = (designCanvasShape, action, actionType) => {
    // Retrieve the shape object in the constraints tree and apply teh updates
    let constraintsCanvasShape = this.getConstraintsCanvasShape(designCanvasShape.name);
    action[actionType].updateConstraintsCanvasShape(constraintsCanvasShape, designCanvasShape);

    // Notify the constraintss canvas to add or remove the widget feedback to the tree
    this.constraintsCanvasRef.current.updateWidgetFeedbacks(constraintsCanvasShape, action, actionType);

    // Check the validity of the current constraints and update valid state of solutions
    this.checkSolutionValidity();
  }

  updateConstraintsCanvas = (constraintsCanvasShape, action) => {
    return () => {
      action["undo"].updateConstraintsCanvasShape(constraintsCanvasShape, undefined);

      // Notify the constraintss canvasa
      this.constraintsCanvasRef.current.updateWidgetFeedbacks(constraintsCanvasShape, action, "undo");

      // Check for the validity of current state of constriants, and update valid state of solutions
      this.checkSolutionValidity();       
    }
  }

  updateSolutionValidity = (solutions) => {
    // Update the state of each solution to display the updated valid/invalid state
    for(var i=0; i<solutions.length; i++) {
      let solution = solutions[i]; 
      let designSolution = this.solutionsMap[solution.id]; 
      designSolution.valid = solution.valid; 
      designSolution.added = solution.added; 
      designSolution.removed = solution.removed;
      designSolution.conflicts = solution.conflicts; 

      if(designSolution.valid) {
        designSolution.invalidated = false;
      }
    }

    // Update the state
    this.setState({
      solutions: this.state.solutions
    }); 
  }

  saveDesignCanvas = (designCanvasID) => {
    // Retrieve the solution corresponding to the design canvas ID
    let solution = this.solutionsMap[designCanvasID]; 
    solution.saved = 1;  

    // Update the state
    // Close the zoomed in canvas if it is open because a DesignCanvas can be saved 
    // from the zoomed in view. 
    this.setState({
      solutions: this.state.solutions, 
      zoomedDesignCanvasID: undefined
    }); 
  }

  trashDesignCanvas = (designCanvasID) => {
    // Retrieve a design canvas by its ID
    let solution = this.solutionsMap[designCanvasID];
    solution.saved = -1; 

    // Update the state
    // Close the zoomed in canvas if it is open because a DesignCanvas can be saved 
    // from the zoomed in view.     
    this.setState({
      solutions: this.state.solutions, 
      zoomedDesignCanvasID: undefined
    }); 
  }

  zoomInOnDesignCanvas = (designCanvasID) => {
    this.setState({
      zoomedDesignCanvasID: designCanvasID
    }); 
  }

  getZoomedDesignCanvas = () => {
    // Zoom in on the design canvas
    // Render the same canvas again in a new DesignCanvas container
    let solution = this.solutionsMap[this.state.zoomedDesignCanvasID];

    // Set isZoomed prop on the DesignCanvas
    // Inside of DesignCanvas, handle this by making the zoomed in canvas have larger dimensions
    // Inside of DesignCanvas, hide the zoom button when hovering  
    let solutionID = uuidv4();
    let designCanvas = this.getDesignCanvas(solution, solutionID, true, solution.id); 
    return designCanvas; 
  }

  closeZoomedInDesignCanvas = () => {
    this.setState({
      zoomedDesignCanvasID: undefined
    }); 
  }

  clearInvalidDesignCanvases = () => {
    // Go through previous solutions and see which ones need to be invalidated
    for(let i=0; i<this.state.solutions.length; i++) {
      let designSolution = this.state.solutions[i]; 
      
      // Invalidate the solution which means it should be moved into the right side panel 
      designSolution.invalidated = !designSolution.valid; 
    }

    // Update the state
    this.setState({
      solutions: this.state.solutions
    }); 
  }

  getShapesJSON = () => {
    // Get all of the shapes on the canvas into a collection 
    let shapeObjects = this.constraintsCanvasRef.current.getShapeHierarchy();

    // set the allowed colors here based on the palette
    // Later need a way to automatically generate these from the uploaded designs
    shapeObjects.colors = this.getBackgroundColors(); 

    return JSON.stringify(shapeObjects); 
  }

  parseSolutions = (requestData) => {
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
      
      // Invalidate the solution which means it should be moved into the right side panel 
      designSolution.invalidated = !designSolution.valid; 
    }

    this.setState({
      designsFound: designsFound,
      solutions: solutions.concat(this.state.solutions), 
      errorMessageShown: false, 
      showDesignsAlert: true
    });
  }

  getRelativeDesigns = (elements, action) => {
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
  }

  hideDesignsAlert = () => {
    this.setState({
      showDesignsAlert: false
    }); 
  }

  getBackgroundColors = () => {
    // let hollywoodColors = ['#C5CAE9', '#FFFFFF', '#3F51B5', '#212121', '#757575', '#BDBDBD', '#CFD8DC', '#dfe4ea', '#ced6e0', '#f1f2f6']
    let harvestColors = ['#FF4081', '#000000', '#304FFE', ]

    // Replace with the above when we can load these in
    // if(this.state.currentPallette == "hollywood") {
    //   return hollywoodColors; 
    // }
    // else {
    return harvestColors; 
    //}
  }

  readSVGIntoWidgetContainer = (e) => {
    let fileData = e.target.result; 
    let widgetID = _.uniqueId(); 
    if(fileData) {
      // Add widgets to the front of the list 
      // So that they are rendered at the top of the container
      // While the automatically added elements (group) appears at the bottom
      this.setState({
        svgWidgets: this.state.svgWidgets.concat({
            id: widgetID, 
            svgData: fileData
        })
      });  
    }
  }

  populateGroupNodeIntoWidgetContainer = () => {
    // Add the group container into the widgets panel 
    // It will just be automatically added in when the drop happens
    let groupID = _.uniqueId(); 
    this.setState({
      svgWidgets: this.state.svgWidgets.concat({
        id: groupID, 
        svgData: groupSVG, 
        type: "group"
      }) 
    }); 
  }

  handleFileDrop = (item, monitor) => {
    if (monitor) {
      const item = monitor.getItem(); 
      const droppedFiles = item.files;  
      this.setState({
        droppedFiles: droppedFiles
      });

      // Download the dropped file contents
      for(let i=0; i<droppedFiles.length; i++) {
        let file = droppedFiles[i]; 
        let reader = new FileReader(); 
        reader.onload = this.readSVGIntoWidgetContainer; 
        reader.readAsText(file); 
      }

      // Add the group container node into the widgets container
      // It will be added automatically when the designer drops in the other SVG elementst
      this.populateGroupNodeIntoWidgetContainer();
    }
  }

  moveDesignCanvas = (id) => {
    // Move a dragged design canvas into the main designs container 
    // Can be dragged from the saved, invalid, and trashed designs area
    let solution = this.solutionsMap[id]; 
    if(solution) {
      solution.saved = 0; 
      solution.invalidated = false;

      this.setState({
        solutions: this.state.solutions
      }); 
    }
  }

  render () {
    const self = this;
    const designsFound = this.state.designsFound; 
    const errorMessageShown = this.state.errorMessageShown; 
    const designsAlertShown = this.state.showDesignsAlert; 
    const designsAlertMessage = designsFound > 0 ? "Here " + (designsFound > 1 ? "are" : "is") + " " + designsFound + " very different " + (designsFound > 1 ? "designs" : "design") + ". " : "No more designs found. "; 
    const savedCanvases = this.state.solutions.filter((solution) => { return (solution.saved == 1); })
              .map((solution) => {
                  return this.getSmallDesignCanvas(solution, solution.id); 
                }); 

    const designCanvases = this.state.solutions
      .filter((solution) => { 
        return (solution.saved == 0 && (!solution.invalidated)); 
      }) 
      .sort(function(a, b) {
        // Do a sort of the designs by cost
        if(a.cost < b.cost) {
          return -1; 
        }
        else if(a.cost > b.cost) {
          return 1; 
        }
        return 0; 
      })
      .map((solution) => {
        return self.getDesignCanvas(solution, solution.id); 
      }); 

    const trashedCanvases = this.state.solutions
      .filter((solution) => { return solution.saved == -1; })
      .map((solution) => {
          if(solution.saved == -1) {
            return self.getSmallDesignCanvas(solution, solution.id); 
          }
        });

    const invalidatedCanvases = this.state.solutions
      .filter((solution) => { 
        return solution.invalidated == true; 
      })
      .map((solution) => {
        if(solution.invalidated == true) {
          return self.getSmallDesignCanvas(solution, solution.id); 
        }
      }); 

    // Get the zoomed design canvas, if there is one set
    let zoomedDesignCanvas = this.state.zoomedDesignCanvasID ? this.getZoomedDesignCanvas() : undefined; 

    return (
      <DragDropContextProvider backend={HTML5Backend}>
        <div className="page-container" onClick={this.closeRightClickMenus} onContextMenu={this.closeRightClickMenus}>
          <nav className="navbar navbar-expand-lg navbar-dark bg-primary">
            <div className="navbar-header">
              <SVGInline className="scout-logo" svg={pageLogo} />
              <h1>Scout</h1>
            </div>
          </nav>
          <div className="bottom">
              <div className="widgets-panel-container"> 
                <WidgetsContainer 
                  onDrop={this.handleFileDrop} 
                  widgets={this.state.svgWidgets}
                  addShapeToConstraintsCanvas={this.addShapeToConstraintsCanvas} />
              </div>
            <ConstraintsCanvas ref={this.constraintsCanvasRef} 
              updateConstraintsCanvas={this.updateConstraintsCanvas} 
              checkSolutionValidity={this.checkSolutionValidity}/>
            <div className="panel panel-primary designs-area-container">
              <div className="panel-heading"> 
                <h3 className="panel-title">Designs
                  <div className="btn-group header-button-group">
                    <button 
                      type="button" 
                      className="btn btn-default design-canvas-button" 
                      onClick={this.checkSolutionValidity.bind(this, {getDesigns: true})}>More Designs</button>
                    <button className="btn btn-default design-canvas-button">{designCanvases.length}</button>
                  </div>
                  <div className="btn-group header-button-group">
                    <button 
                      type="button" 
                      className="btn btn-default design-canvas-button" 
                      onClick={this.checkSolutionValidity.bind(this, {getDesigns: true})}>More not like these (TBD).</button>
                    <button 
                      type="button" 
                      className="btn btn-default design-canvas-button" 
                      onClick={this.checkSolutionValidity.bind(this, {getDesigns: true})}>More like these (TBD).</button>
                  </div>
                  <div 
                    className="btn-group header-button-group">
                    <button type="button" className="btn btn-default design-canvas-button">Export Designs</button>
                    <button type="button" className="btn btn-default design-canvas-button" 
                      onClick={this.clearInvalidDesignCanvases}>Clear Invalid</button>
                  </div>
                </h3>
              </div>  
              <div className="design-canvas-container">
                <div className="left-container">
                  { savedCanvases.length ? (<div className="panel designs-container saved-designs-container panel-default">
                    <div>
                      <span className="save-icon glyphicon glyphicon-star" aria-hidden="true"></span>
                      <span>({savedCanvases.length})</span>
                    </div>
                    <div className="panel-body saved-body">
                      {savedCanvases}
                    </div>
                  </div>) : null }
                  { designCanvases.length ? (<div className="panel designs-container current-designs-container panel-default">
                      {(designsAlertShown ? (<div className="designs-canvas-container-alert alert alert-success alert-dismissable" role="alert">
                        <button type="button" className="close" data-dismiss="alert" aria-label="Close">
                          <span aria-hidden="true">&times;</span>
                        </button>
                        Scout has generated 10 new designs that meet your constraints. 
                      </div>) : undefined)}
                      <DesignCanvasContainer 
                        onDrop={this.moveDesignCanvas}
                        designCanvases={designCanvases} 
                        onScroll={this.hideDesignsAlert} />
                  </div>) : null }
                  { trashedCanvases.length ? (<div className="panel designs-container trashed-designs-container panel-default">
                    <div>
                      <span className="save-icon glyphicon glyphicon-trash" aria-hidden="true"></span>
                      <span>({trashedCanvases.length})</span>
                    </div>
                    <div className="panel-body trashed-body">
                      {trashedCanvases}
                    </div>
                  </div>) : null }
                </div>
                {invalidatedCanvases.length ? (<div className="right-container"> 
                  <div className="panel invalid-container panel-default"> 
                    <div>
                      <span className="save-icon glyphicon glyphicon-asterisk" aria-hidden="true"></span>
                      <span>({invalidatedCanvases.length})</span>
                    </div>
                    <div className="panel-body invalidated-body">
                      {invalidatedCanvases}
                    </div>
                  </div>
                </div>) : null}
              </div>
            </div>
          </div>
          {this.state.zoomedDesignCanvasID ? (
            <div 
              className="zoomed-design-container-background"
              onClick={this.closeZoomedInDesignCanvas}>
            </div>
          ) : undefined}
          {this.state.zoomedDesignCanvasID ? 
            (<div className="zoomed-design-container"> 
              {zoomedDesignCanvas}
            </div>) : undefined}
        </div>
      </DragDropContextProvider>
    ); 
  }
}