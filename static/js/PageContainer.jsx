// App.jsx
import React from "react";
import '../css/bootstrap.min.css';
import '../css/Canvas.css'; 
import '../css/PageContainer.css';
import ConstraintsCanvas from "./ConstraintsCanvas"; 
import FeedbackContainer from "./FeedbackContainer"; 
import WidgetsContainer from "./WidgetsContainer"; 
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
import {getUniqueID} from './util'; 

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
      zoomedDesignCanvasID: undefined, 
      activeDesignPanel: "designs", 
      selectedElement: undefined, 
      widgetsCollapsed: false, 
      activeDesignWidget: undefined
    };   

    // Dictionaries for being able to retrieve a design canvas by ID more efficiently
    this.solutionsMap = {};

    this.constraintsCanvasRef = React.createRef();

    this.prevTime = undefined; 
  }

  componentDidMount = () => {
    // Initialize the SVGs from local storage if they are cached. 
    this.readSVGsFromLocalStorage(); 
    this.loadSolutionsFromCache();
  }

  loadSolutionsFromCache = () => {
    let solutionsCached = JSON.parse(localStorage.getItem('solutions'));
    if(solutionsCached) {
      for(let i=0; i<solutionsCached.length; i++){
        let solution = solutionsCached[i];
        this.solutionsMap[solution.id] = solution; 
      }

      this.setState({
        solutions: solutionsCached
      }); 
    }     
  }

  updateSolutionsCache = () => {
    let solutionsJSON = JSON.stringify(this.state.solutions); 
    localStorage.setItem('solutions', solutionsJSON);
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
              new={solution.new}
              conflicts={solution.conflicts}
              added={solution.added}
              removed={solution.removed}
              zoomed={zoomed}
              linkedSolutionId={linkedSolutionId}
              invalidated={solution.invalidated}
              svgWidgets={this.state.svgWidgets}
              highlightAddedWidget={this.highlightAddedWidget}
              highlightWidgetFeedback={this.highlightWidgetFeedback}
              saveDesignCanvas={this.saveDesignCanvas} 
              trashDesignCanvas={this.trashDesignCanvas}
              zoomInOnDesignCanvas={this.zoomInOnDesignCanvas}
              getRelativeDesigns={this.getRelativeDesigns}
              displayWidgetFeedback={this.displayWidgetFeedbackFromDesignCanvas} />); 
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
              highlightAddedWidget={this.highlightAddedWidget}
              highlightWidgetFeedback={this.highlightWidgetFeedback}
              saveDesignCanvas={this.saveDesignCanvas} 
              trashDesignCanvas={this.trashDesignCanvas}
              zoomInOnDesignCanvas={this.zoomInOnDesignCanvas}
              getRelativeDesigns={this.getRelativeDesigns}
              displayWidgetFeedback={this.displayWidgetFeedbackFromDesignCanvas} />); 
  }

  checkSolutionValidity = (options={}) => {
    let currTime = Date.now()
    console.log(currTime); 
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

  showWidgetFeedback = (shapeId, evt) => {
    evt.stopPropagation();
    this.constraintsCanvasRef.current.showWidgetFeedback(shapeId); 
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

  updateConstraintsCanvasFromFeedbackContainer = () => {
    // Notify the tree to re-render in response to the update
    // from the FeedbackContainer    
    this.constraintsCanvasRef.current.renderTree();

    // re-verify the constraints after feedback is applied
    this.checkSolutionValidity();
  }

  // updateConstraintsCanvas = (constraintsCanvasShape, action, property) => {
  //   return () => {
  //     action["undo"].updateConstraintsCanvasShape(property, constraintsCanvasShape, undefined);

  //     // Check for the validity of current state of constriants, and update valid state of solutions
  //     this.checkSolutionValidity();       
  //   }
  // }

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
    }, this.updateSolutionsCache); 
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
    }, this.updateSolutionsCache); 
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
    }, this.updateSolutionsCache); 
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
    }, this.updateSolutionsCache); 
  }

  clearDesignsUnderConsideration = () => {
    for(let i=0; i<this.state.solutions.length; i++) {
      let designSolution = this.state.solutions[i]; 
      
      if(designSolution.saved == 0 && (designSolution.valid || !designSolution.invalidated)) {
        designSolution.saved = -1; 
      }
    }

    // Update the state
    this.setState({
      solutions: this.state.solutions
    }, this.updateSolutionsCache); 
  }

  clearSavedDesigns = () => {
    for(let i=0; i<this.state.solutions.length; i++) {
      let designSolution = this.state.solutions[i]; 
      
      if(designSolution.saved == 1) {
        designSolution.saved = -1; 
      }
    }

    // Update the state
    this.setState({
      solutions: this.state.solutions
    }, this.updateSolutionsCache); 
  }

  clearDiscardedDesigns = () => {
    const notDiscardedSolutions = this.state.solutions
      .filter((solution) => { 
        return ((!solution.saved == -1) && (!solution.invalidated)); 
    });  

    // Update the state
    this.setState({
      solutions: notDiscardedSolutions
    }, this.updateSolutionsCache); 
  }

  clearAllDesigns = () => {
    // Update the state
    this.setState({
      solutions: []
    }, this.updateSolutionsCache);

    this.solutionsMap = {}; 
  }

  getShapesJSON = () => {
    // Get all of the shapes on the canvas into a collection 
    let shapeObjects = this.constraintsCanvasRef.current.getShapeHierarchy();
    return JSON.stringify(shapeObjects); 
  }

  parseSolutions = (requestData) => {
    let resultsParsed = JSON.parse(requestData); 
    let solutions = resultsParsed.solutions;
    if(solutions) {
      let designCanvasList = this.state.mainDesignCanvases; 
      for(let i=0; i<solutions.length; i++) {
        let solution = solutions[i]; 
        solution.new = true; 
        this.solutionsMap[solution.id] = solution; 
      }

      let designsFound = solutions.length;

      // Go through previous solutions and see which ones need to be invalidated
      for(let i=0; i<this.state.solutions.length; i++) {
        let designSolution = this.state.solutions[i]; 
        
        // Invalidate the solution which means it should be moved into the right side panel 
        designSolution.invalidated = !designSolution.valid;

        // Mark old solutions as not new
        designSolution.new = false;
      }

      this.setState({
        designsFound: designsFound,
        solutions: solutions.concat(this.state.solutions), 
        showDesignsAlert: true, 
        activeDesignPanel: "designs"
      }, this.updateSolutionsCache);      
    }
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

  readSVGsFromLocalStorage = () => {
    let svgWidgets = localStorage.getItem('svgWidgets'); 
    if(svgWidgets) {
      let svgWidgetsParsed = JSON.parse(svgWidgets); 
      if(svgWidgetsParsed && svgWidgetsParsed.length){
        this.setState({
          svgWidgets: this.state.svgWidgets.concat(svgWidgetsParsed)
        });
      }
    }

    let widgetsCollapsed = localStorage.getItem('widgetsCollapsed'); 
    if(widgetsCollapsed && widgetsCollapsed == "true") {
      this.setState({
        widgetsCollapsed: true
      }); 
    }
  }

  readSVGIntoWidgetContainer = (e) => {
    let fileData = e.target.result; 
    if(fileData) {
      let svgItem = {
        id: getUniqueID(), 
        svgData: fileData, 
        visible: true
      }

      this.setState({
        svgWidgets: this.state.svgWidgets.concat(svgItem)
      });  

      // Look for SVG widgets in local storage and cache them for future refreshes
      let svgWidgets = localStorage.getItem('svgWidgets')
      let svgWidgetsParsed = JSON.parse(svgWidgets); 
      if(svgWidgetsParsed && svgWidgetsParsed.length) {
        svgWidgetsParsed.push(svgItem); 
        localStorage.setItem('svgWidgets', JSON.stringify(svgWidgetsParsed)); 
      }
      else {
        let items = [svgItem]; 
        items = JSON.stringify(items); 
        localStorage.setItem('svgWidgets', items); 
      }
    }
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
    }
  }

  toggleActiveDesignPanel = (activePanel) => {
    this.setState({
      activeDesignPanel: activePanel
    }); 
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
      }, this.updateSolutionsCache); 
    }
  }

  clearWidgetsContainer = () => {
    for(let i=0; i<this.state.svgWidgets.length; i++) {
      // Mark widgets that we are removing as false
      // When designs are later cleared, we can completely remove them once the 
      // Designs using them are no longer there. 
      this.state.svgWidgets[i].visible = false; 
    }

    // Update the local storage cache
    let widgets = JSON.stringify(this.state.svgWidgets);
    localStorage.setItem('svgWidgets', widgets); 

    this.setState({
      svgWidgets: this.state.svgWidgets
    });
  }

  toggleWidgetsPanel = () => {
    let newState = !this.state.widgetsCollapsed; 
    this.setState({
      widgetsCollapsed: newState
    }); 

    localStorage.setItem('widgetsCollapsed', newState); 
  }

  displayWidgetFeedback = (shape, feedbackCallbacks, fromDesign=false) => {
    if(!fromDesign) {
      this.setState({
        activeDesignWidget: undefined
      }); 
    }

    this.setState({
      selectedElement: shape, 
      feedbackCallbacks: feedbackCallbacks
    }); 
  }

  hideWidgetFeedback = () => {
    this.setState({
      selectedElement: undefined, 
      feedbackCallbacks: undefined
    }); 
  }

  displayWidgetFeedbackFromDesignCanvas = (shape) => {
    // Set this property to activate the corresponding element in the tree
    // And display feedback based on this instance of the element in the design canvas
    this.setState({
      activeDesignWidget: shape
    });
  }

  render () {
    const self = this;
    const designsFound = this.state.designsFound; 
    const designsAlertMessage = designsFound > 0 ? "Here " + (designsFound > 1 ? "are" : "is") + " " + designsFound + " very different " + (designsFound > 1 ? "designs" : "design") + ". " : "No more designs found. "; 
    const savedCanvases = this.state.solutions.filter((solution) => { return (solution.saved == 1); })
              .map((solution) => {
                  return this.getDesignCanvas(solution, solution.id); 
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
            return self.getDesignCanvas(solution, solution.id); 
          }
        });

    const invalidatedCanvases = this.state.solutions
      .filter((solution) => { 
        return solution.invalidated == true; 
      })
      .map((solution) => {
        if(solution.invalidated == true) {
          return self.getDesignCanvas(solution, solution.id); 
        }
      }); 

    const discardedCanvases = trashedCanvases.concat(invalidatedCanvases);

    // Get the zoomed design canvas, if there is one set
    let zoomedDesignCanvas = this.state.zoomedDesignCanvasID ? this.getZoomedDesignCanvas() : undefined; 

    return (
      <DragDropContextProvider backend={HTML5Backend}>
        <div className="page-container" onClick={this.closeRightClickMenus} onContextMenu={this.closeRightClickMenus}>
          <nav className="navbar navbar-expand-lg navbar-dark bg-primary">
            <div className="navbar-header">
              <SVGInline className="scout-logo" svg={pageLogo} />
              <h1>Scout <span className="scout-tagline"><small>Exploring design layout alternatives</small></span></h1>
            </div>
          </nav>
          <div className="bottom">
              <div className="widgets-panel-container"> 
                <WidgetsContainer 
                  onDrop={this.handleFileDrop} 
                  widgets={this.state.svgWidgets}
                  onClick={this.clearWidgetsContainer}
                  widgetsCollapsed={this.state.widgetsCollapsed}
                  toggleWidgetsPanel={this.toggleWidgetsPanel}
                  addShapeToConstraintsCanvas={this.addShapeToConstraintsCanvas} />
              </div>
            <ConstraintsCanvas ref={this.constraintsCanvasRef} 
              updateConstraintsCanvas={this.updateConstraintsCanvas} 
              displayWidgetFeedback={this.displayWidgetFeedback}
              hideWidgetFeedback={this.hideWidgetFeedback}
              checkSolutionValidity={this.checkSolutionValidity}
              activeDesignWidget={this.state.activeDesignWidget}
              svgWidgets={this.state.svgWidgets} />
            <FeedbackContainer selectedElement={this.state.selectedElement}
              feedbackCallbacks={this.state.feedbackCallbacks}
              getConstraintsCanvasShape={this.getConstraintsCanvasShape}
              updateConstraintsCanvas={this.updateConstraintsCanvasFromFeedbackContainer}
              checkSolutionValidity={this.checkSolutionValidity} />
            <div className="panel panel-primary designs-area-container">
              <div className="panel-heading"> 
                <h3 className="panel-title">Designs
                </h3>
                <div>
                  <ul className="nav nav-pills designs-area-nav-pills">
                    <li className="nav-item">
                      <a className={"nav-link" + (this.state.activeDesignPanel == "designs" ? " active" : "")} 
                         href="#"
                         onClick={this.toggleActiveDesignPanel.bind(this, "designs")}>
                         <span className="designs-area-number">{designCanvases.length}</span>
                         Under Consideration</a> 
                    </li> 
                    <li className="nav-item"> 
                      <a className={"nav-link" + (this.state.activeDesignPanel == "saved" ? " active" : "")}  
                        href="#"
                        onClick={this.toggleActiveDesignPanel.bind(this, "saved")}>
                         <span className="designs-area-number">{savedCanvases.length}</span>
                        Saved</a>
                    </li> 
                    <li className="nav-item"> 
                      <a className={"nav-link" + (this.state.activeDesignPanel == "discarded" ? " active" : "")} 
                        href="#"
                        onClick={this.toggleActiveDesignPanel.bind(this, "discarded")}>
                         <span className="designs-area-number">{discardedCanvases.length}</span>
                        Discarded</a>
                    </li>
                  </ul> 
                </div>
                <div className="designs-area-actions">
                  {this.state.activeDesignPanel == "designs" ? 
                    (<div 
                      className="btn-group header-button-group">
                      <button type="button" className="btn btn-default design-canvas-button" 
                        onClick={this.clearInvalidDesignCanvases}>Discard Invalid</button>
                    </div>) : null}
                  {this.state.activeDesignPanel == "designs" ? 
                    (<div 
                      className="btn-group header-button-group">
                      <button type="button" className="btn btn-default design-canvas-button" 
                        onClick={this.clearDesignsUnderConsideration}>Discard Under Consideration</button>
                    </div>) : null}
                  {this.state.activeDesignPanel == "saved" ? 
                    (<div 
                      className="btn-group header-button-group">
                      <button type="button" className="btn btn-default design-canvas-button" 
                        onClick={this.clearSavedDesigns}>Discard Saved Designs</button>
                    </div>) : null}
                  {this.state.activeDesignPanel == "discarded" ? 
                    (<div 
                      className="btn-group header-button-group">
                      <button type="button" className="btn btn-default design-canvas-button" 
                        onClick={this.clearDiscardedDesigns}>Clear Discarded Designs</button>
                    </div>) : null}
                  <div 
                    className="btn-group header-button-group">
                    <button type="button" className="btn btn-default design-canvas-button" 
                      onClick={this.clearAllDesigns}>Clear All Designs</button>
                  </div>
                  <div 
                    className="btn-group header-button-group">
                    <button type="button" className="btn btn-default design-canvas-button">Export Saved Designs</button>
                  </div>
                </div>
              </div>  
              {(this.state.activeDesignPanel == "designs" && designCanvases.length == 0) ? 
                (<div className="designs-area-alert-container">
                  <div className="card card-body bg-light">
                    <span>You currently have no designs under consideration. Click <span className="card-emph">Generate Designs</span> in the outline to see more.</span>
                  </div>
                </div>) : null
              }
              {(this.state.activeDesignPanel == "saved" && savedCanvases.length == 0) ? 
                (<div className="designs-area-alert-container">
                  <div className="card card-body bg-light">
                    <span>You currently have no saved designs. Click the star icon above a design in the <span className="card-emph">Under Consideration</span> panel to save a design.</span>
                  </div>
                </div>) : null
              }
              {(this.state.activeDesignPanel == "discarded" && discardedCanvases.length == 0) ? 
                (<div className="designs-area-alert-container">
                  <div className="card card-body bg-light">
                    <span>You currently have no discarded designs. Click the trash icon in the <span className="card-emph">Under Consideration</span> panel to discard any designs that you don't like.</span>
                  </div>
                </div>) : null
              }
              <div className="design-canvas-container">
                  { this.state.activeDesignPanel == "designs" && designCanvases.length ? 
                    (<div className="panel designs-container current-designs-container panel-default">
                      <DesignCanvasContainer 
                        onDrop={this.moveDesignCanvas}
                        designCanvases={designCanvases} />
                    </div>) : null
                  }
                  { this.state.activeDesignPanel == "saved" && savedCanvases.length ? 
                    (<div className="panel designs-container current-designs-container panel-default">
                      <DesignCanvasContainer 
                        onDrop={this.moveDesignCanvas}
                        designCanvases={savedCanvases} />
                    </div>) : null }
                  { this.state.activeDesignPanel == "discarded" && discardedCanvases.length ? 
                    (<div className="panel designs-container current-designs-container panel-default">
                      <DesignCanvasContainer 
                        onDrop={this.moveDesignCanvas}
                        designCanvases={discardedCanvases} />
                    </div>) : null }
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