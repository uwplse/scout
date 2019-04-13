// App.jsx
import React from "react";
import '../css/bootstrap.min.css';
import '../css/Canvas.css'; 
import '../css/PageContainer.css';
import { DragDropContextProvider } from 'react-dnd'; 
import HTML5Backend from 'react-dnd-html5-backend';
import $ from 'jquery';
import uuidv4 from 'uuid/v4'; 
import SVGInline from "react-svg-inline"; 
import ConstraintsCanvasSVGWidget from './ConstraintsCanvasSVGWidget';
import pageLogo from '../assets/logo.svg';
import {getUniqueID} from './util'; 
import { saveAs } from 'file-saver';
import ConstraintsCanvas from "./ConstraintsCanvas"; 
import Exporter from "./Exporter"; 
import FeedbackContainer from "./FeedbackContainer"; 
import WidgetsContainer from "./WidgetsContainer"; 
import DesignCanvas from './DesignCanvas';
import SmallDesignCanvas from './SmallDesignCanvas';
import DesignCanvasContainer from './DesignCanvasContainer'; 

const STORAGE_MAX_SOLUTIONS = 200; 

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
      droppedFiles: [], 
      svgWidgets: [], 
      zoomedDesignCanvasID: undefined, 
      activeDesignPanel: "designs", 
      activeCanvasShape: undefined, 
      activeDesignShape: undefined, 
      widgetsCollapsed: false, 
      activeDesignShape: undefined, 
      primarySelection: undefined, 
      solutionsFound: true
    };   

    // Dictionaries for being able to retrieve a design canvas by ID more efficiently
    this.solutionsMap = {};

    this.constraintsCanvasRef = React.createRef();
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
    // Check the number of solutions already kept in local storage and
    // remove > invalid solutions
    let solutionsJSON = JSON.stringify(this.state.solutions); 
    localStorage.setItem('solutions', solutionsJSON);

    // Keep the most recent 200 and discard the rest
    const discardedCanvases = this.state.solutions.filter((solution) => { 
      return solution.saved == -1 || solution.invalidated; }); 
  }

  addShapeToConstraintsCanvas = (id, src, type, width, height) => {
    return () => {
      this.constraintsCanvasRef.current.addShapeToCanvas(id, src, type, width, height);
    }
  }

  showWidgetFeedback = (shapeId, evt) => {
    evt.stopPropagation();
    this.constraintsCanvasRef.current.showWidgetFeedback(shapeId); 
  }

  getConstraintsCanvasShape = (shapeId) => {
    return this.constraintsCanvasRef.current.getConstraintsCanvasShape(shapeId); 
  }

  highlightFeedbackConflict = (conflict, highlighted) => {
    this.constraintsCanvasRef.current.highlightFeedbackConflict(conflict, highlighted);
  }

  highlightAddedWidget = (shapeId, highlighted) => {
    this.constraintsCanvasRef.current.highlightAddedWidget(shapeId, highlighted);
  }

  getDesignCanvas = (solution, id, zoomed=false, solutionID=undefined, scaling=undefined) => {
    return (<DesignCanvas 
              key={id} 
              id={id} 
              ref={"design-canvas-" + id}
              cost={solution.cost}
              elements={solution.elements}
              savedState={solution.saved}
              scaling={scaling}
              valid={solution.valid}
              new={solution.new}
              conflicts={solution.conflicts}
              added={solution.added}
              removed={solution.removed}
              zoomed={zoomed}
              solutionID={solutionID}
              activePanel={this.state.activeDesignPanel}
              primarySelection={this.state.primarySelection}
              invalidated={solution.invalidated}
              svgWidgets={this.state.svgWidgets}
              highlightAddedWidget={this.highlightAddedWidget}
              highlightFeedbackConflict={this.highlightFeedbackConflict}
              saveDesignCanvas={this.saveDesignCanvas} 
              trashDesignCanvas={this.trashDesignCanvas}
              zoomInOnDesignCanvas={this.zoomInOnDesignCanvas}
              considerDesignCanvas={this.considerDesignCanvas}
              getConstraintsCanvasShape={this.getConstraintsCanvasShape}
              setPrimarySelection={this.setPrimarySelection} />); 
  }

  parseSolutions = (requestData) => {
    if(requestData && requestData.length) {
      let resultsParsed = JSON.parse(requestData); 
      let solutions = resultsParsed.solutions;
      if(solutions.length) {
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

          let invalidated = false; 
          if(designSolution.valid) {
            if(designSolution.conflicts && designSolution.conflicts.length && designSolution.invalidated) {
              invalidated = true; 
            }
          }
          else {
            invalidated = true;
          }

          designSolution.invalidated = invalidated; 

          // Mark old solutions as not new
          designSolution.new = false;
        }

        this.state.solutions.push(...solutions); 
        this.setState({
          designsFound: designsFound,
          solutions: this.state.solutions,  
          showDesignsAlert: true, 
          activeDesignPanel: "designs", 
          solutionsFound: true
        }, this.updateSolutionsCache);      
      } else {
        this.setState({
          solutionsFound: false
        }); 
      }
    }
    else {
      this.setState({
        solutionsFound: false
      }); 
    }
  }

  getMoreDesigns = (callback) => {
    // get more designs
    // without changing any new constraints
    let jsonShapes = this.getShapesJSON(); 

    // Get JSON for already retrieved designs/saved/trashed
    let prevSolutions = JSON.stringify(this.state.solutions);
   
   // Send an ajax request to the server 
   // Solve for the new designs
    let self = this;
    $.post("/scout/solve", {"elements": jsonShapes, "solutions": prevSolutions}, 
      function processDesigns(requestData) {
        self.parseSolutions(requestData); 
        if(callback){
          callback(); 
        }
      }, 'text');
  }

  checkSolutionValidity = (options={}) => {
    let getDesigns = options.getDesigns ? true : false; 
    if(!getDesigns) {
      // Only check for validity of the current solutions
      let jsonShapes = this.getShapesJSON(); 

      // Get all of the solutions so far to check their validity 
      if(this.state.solutions.length) {
        let notDiscardedSolutions = this.state.solutions.filter((solution) => !solution.invalidated);
        let prevSolutions = JSON.stringify(notDiscardedSolutions);

        $.post("/scout/check", {"elements": jsonShapes, "solutions": prevSolutions}, (requestData) => {
          let requestParsed = JSON.parse(requestData); 
          this.updateSolutionValidityFromRequest(requestParsed.solutions);

          if(options.callback) {
            options.callback();
          }
        });         
      }
    }
    else {
      // Get design solutions for the current set of constraints
      this.getMoreDesigns(options.callback);
    }
  }

  updateSolutionValidityFromRequest = (solutions) => {
    // Update the state of each solution to display the updated valid/invalid state
    for(var i=0; i<solutions.length; i++) {
      let solution = solutions[i]; 
      let designSolution = this.solutionsMap[solution.id]; 

      // In case the design was already removed while the request was processing. 
      if(designSolution) {
        designSolution.valid = solution.valid; 
        designSolution.added = solution.added; 
        designSolution.removed = solution.removed;
        designSolution.conflicts = solution.conflicts; 

        if(designSolution.valid && !solutions.conflicts) {
          designSolution.invalidated = false;
        }
      }
    }

    // Update the state
    this.setState({
      solutions: this.state.solutions
    }, this.updateSolutionsCache); 
  }

  reflowSolutions = (solutions) => {
    if(solutions) {
      for(var i=0; i<solutions.length; i++) {
        let solution = solutions[i]; 
        let designSolution = this.solutionsMap[solution.id]; 

        designSolution.conflicts = solution.conflicts; 
        designSolution.elements = solution.elements; 
      }
    }

    // Update the state
    this.setState({
      solutions: this.state.solutions
    }, this.updateSolutionsCache); 
  }

  updateConstraintsCanvas = (shape, property, value, keepOrPrevent="") => {
    // Notify the tree to re-render in response to the update
    // from the FeedbackContainer    
    this.constraintsCanvasRef.current.renderTreeCacheUpdate();

    // Also update the activeCanvasShape to trigger the FeedbackContainer to re-render
    // To update the state of the unlocked properties
    this.setState({
      activeCanvasShape: this.state.activeCanvasShape
    }); 

    // Only check the validity of the lock and prevent values on the solutions
    // This means that we do not need to make a request to the solver to check them 
    let invalidSolutions = this.checkSolutionValidityClient(shape);

    // if(keepOrPrevent == "keep" || keepOrPrevent == "prevent") {
    //   invalidSolutions = JSON.stringify(invalidSolutions);
    //   let jsonShapes = this.getShapesJSON(); 
    //   let callVariables = {
    //     "elements": jsonShapes, 
    //     "solutions": invalidSolutions, 
    //     "changed_element_id": shape.name, 
    //     "changed_property": property, 
    //     "changed_value": value, 
    //     "keep_or_prevent": keepOrPrevent
    //   }; 

    //   $.post("/reflow", callVariables, (requestData) => {
    //     let requestParsed = JSON.parse(requestData); 
    //     this.reflowSolutions(requestParsed.solutions);
    //   }); 
    // }
  }

  getElementFromTree = (shape, element_tree) => {
    if(element_tree.name == shape.name) {
      return element_tree; 
    }

    if(element_tree.children) {
      for(let i=0; i<element_tree.children.length; i++) {
        let elt = this.getElementFromTree(shape, element_tree.children[i]); 
        if(elt) {
          return elt; 
        }
      }
    }
  }

  checkSolutionValidityClient = (shape) => {
    let invalidSolutions = []; 
    for(let i=0; i < this.state.solutions.length; i++) {
      let solution = this.state.solutions[i]; 
      let shapeId = shape.name; 
      let element = this.getElementFromTree(shape, solution.elements);

      let conflicts = solution.conflicts; 
      let keepConflicts = []; 
      if(shape.locks && shape.locks.length && element) {
        for(let j=0; j<shape.locks.length; j++) {
          let lock = shape.locks[j];
          let elementValue = element[lock];
          let lockedValues = shape["locked_values"][lock]; 
          if(lockedValues && lockedValues.length) {
            let elementValueKept = lockedValues.indexOf(elementValue) > -1; 
            if(!elementValueKept) {
              keepConflicts.push({
                type: "lock",
                shapeID: shape.name, 
                variable: lock, 
                value: elementValue
              }); 
            }
          }
        }
      }

      let preventConflicts = []; 
      if(shape.prevents && shape.prevents.length && element) {
        for(let j=0; j<shape.prevents.length; j++) {
          let prevent = shape.prevents[j];
          let elementValue = element[prevent];
          let preventedValues = shape["prevented_values"][prevent]; 
          if(preventedValues && preventedValues.length) {
            let elementValuePrevented = preventedValues.indexOf(elementValue) > -1; 
            if(elementValuePrevented) {
              preventConflicts.push({
                type: "prevent",
                shapeID: shape.name, 
                variable: prevent, 
                value: elementValue
              }); 
            }
          }
        }
      }

      // Remove previous conflicts corresponding to this shape 
      let previousConflicts = conflicts.filter(conflict => conflict.shapeID != shape.name); 
      if(keepConflicts.length) {
        previousConflicts.push(...keepConflicts); 
      }

      if(preventConflicts.length) {
        previousConflicts.push(...preventConflicts); 
      }
      solution.conflicts = previousConflicts; 

      if(conflicts.length) {
        invalidSolutions.push(solution);
      }
    }

    // Update the state
    this.setState({
      solutions: this.state.solutions
    }, this.updateSolutionsCache); 

    return invalidSolutions; 
  }

  considerDesignCanvas = (designCanvasID) => {
    // Retrieve the solution corresponding to the design canvas ID
    let solution = this.solutionsMap[designCanvasID]; 
    solution.saved = 0;  
    solution.invalidated = 0; 
    solution.trashed = false; 

    // Update the state
    this.setState({
      solutions: this.state.solutions, 
      zoomedDesignCanvasID: undefined
    }, this.updateSolutionsCache); 
  }

  saveDesignCanvas = (designCanvasID) => {
    // Retrieve the solution corresponding to the design canvas ID
    let solution = this.solutionsMap[designCanvasID]; 
    solution.saved = 1;  
    solution.invalidated = 0

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
    solution.trashed = true; 

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
      designSolution.invalidated = (!designSolution.valid || designSolution.conflicts.length); 
    }

    // Update the state
    this.setState({
      solutions: this.state.solutions
    }, this.updateSolutionsCache); 
  }

  clearDesignsUnderConsideration = () => {
    for(let i=0; i<this.state.solutions.length; i++) {
      let designSolution = this.state.solutions[i]; 
      
      if(designSolution.saved == 0) {
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

  // getRelativeDesigns = (elements, action) => {
  //   // get more designs relative to a specific design
  //   let jsonShapes = this.getShapesJSON(); 

  //   // Get JSON for already retrieved designs/saved/trashed
  //   let prevSolutions = JSON.stringify(this.state.solutions);
   
  //  // Send an ajax request to the server 
  //  // Solve for the new designs
  //   $.post("/solve", {
  //     "elements": jsonShapes, 
  //     "solutions": prevSolutions, 
  //     "relative_designs": {
  //       "relative_design": elements, 
  //       "relative_action": action
  //     }
  //   }, this.parseSolutions, 'text');
  // }

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

  displayWidgetFeedback = (shape, feedbackCallbacks, constraintsCanvasShape=undefined) => {
    this.setState({ 
      activeCanvasShape: constraintsCanvasShape, 
      primarySelection: shape, 
      feedbackCallbacks: feedbackCallbacks
    }); 
  }

  hideWidgetFeedback = () => {
    this.setState({
      feedbackCallbacks: undefined, 
      primarySelection: undefined,
      activeCanvasShape: undefined
    }); 
  }

  setPrimarySelection = (shape) => {
    // Set this property to activate the corresponding element in the tree
    // And display feedback based on this instance of the element in the design canvas
    this.setState({
      primarySelection: shape
    });
  }

  unsetPrimarySelection = () => {
    this.setState({
      primarySelection: undefined, 
      feedbackCallbacks: undefined, 
      activeCanvasShape: undefined
    });

    if(this.constraintsCanvasRef) {
      this.constraintsCanvasRef.current.closeRightClickMenu(); 
    }
  }

  exportSavedDesigns = () => {
    // Export all of the currently explored solutions into JSON and SVGs 
    let exporter = new Exporter(this.state.svgWidgets); 
    exporter.exportDesigns(this.state.solutions); 
  }

  closeNoSolutionsAlert = () => {
    this.setState({
      solutionsFound: true
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

    const pinnedCanvases = this.state.solutions.filter((solution) => { return (solution.saved == 1); })
              .map((solution) => {
                  return this.getDesignCanvas(solution, solution.id, false, undefined, 0.5); 
                }); 

    const designCanvases = this.state.solutions
      .filter((solution) => { 
        return (solution.saved == 0 && (!solution.invalidated)); 
      }) 
      .sort(function(a, b) {
        // Do a sort of the designs by cost
        if(a.cost > b.cost) {
          return -1; 
        }
        else if(a.cost < b.cost) {
          return 1; 
        }
        return 0; 
      })
      .map((solution) => {
        return self.getDesignCanvas(solution, solution.id); 
      }); 

    const discardedCanvases = this.state.solutions
      .filter((solution) => { return solution.saved == -1 || solution.invalidated; })
      .map((solution) => {
          if(solution.saved == -1 || solution.invalidated) {
            return self.getDesignCanvas(solution, solution.id); 
          }
        });
      
    // Get the zoomed design canvas, if there is one set
    let zoomedDesignCanvas = this.state.zoomedDesignCanvasID ? this.getZoomedDesignCanvas() : undefined; 

    return (
      <DragDropContextProvider backend={HTML5Backend}>
        <div className="page-container"
          onClick={this.unsetPrimarySelection}>
          <nav className="navbar navbar-expand-lg navbar-dark bg-primary">
            <div className="navbar-header">
              <SVGInline className="scout-logo" svg={pageLogo} />
              <h1>Scout <span className="scout-tagline"><small>Exploring alternative layout ideas for wireframes.</small></span></h1>
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
              primarySelection={this.state.primarySelection}
              svgWidgets={this.state.svgWidgets} />
            <FeedbackContainer 
              activeCanvasShape={this.state.activeCanvasShape}
              primarySelection={this.state.primarySelection}
              feedbackCallbacks={this.state.feedbackCallbacks}
              updateConstraintsCanvas={this.updateConstraintsCanvas}
              checkSolutionValidity={this.checkSolutionValidity} />
            <div className="panel panel-primary designs-area-container">
              <div className="panel-heading"> 
                <h3 className="panel-title">Layout Ideas
                </h3>
                <div>
                  <ul className="nav nav-pills designs-area-nav-pills">
                    <li className="nav-item">
                      <a className={"nav-link designs-area-link" + (this.state.activeDesignPanel == "designs" ? " active" : "")} 
                         href="#"
                         onClick={this.toggleActiveDesignPanel.bind(this, "designs")}>
                         <span className="designs-area-number">{designCanvases.length}</span>
                         Under Consideration</a> 
                    </li> 
                    <li className="nav-item"> 
                      <a className={"nav-link  designs-area-link" + (this.state.activeDesignPanel == "saved" ? " active" : "")}  
                        href="#"
                        onClick={this.toggleActiveDesignPanel.bind(this, "saved")}>
                         <span className="designs-area-number">{savedCanvases.length}</span>
                        Saved</a>
                    </li> 
                    <li className="nav-item"> 
                      <a className={"nav-link  designs-area-link" + (this.state.activeDesignPanel == "discarded" ? " active" : "")} 
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
                  {/*this.state.activeDesignPanel == "designs" ? 
                    (<div 
                      className="btn-group header-button-group">
                      <button type="button" className="btn btn-default design-canvas-button" 
                        onClick={this.clearDesignsUnderConsideration}>Discard Under Consideration</button>
                    </div>) : null*/}
                  {this.state.activeDesignPanel == "saved" ? 
                    (<div 
                      className="btn-group header-button-group">
                      <button type="button" className="btn btn-default design-canvas-button" 
                        onClick={this.clearSavedDesigns}>Discard Saved Ideas</button>
                    </div>) : null}
                  {this.state.activeDesignPanel == "discarded" ? 
                    (<div 
                      className="btn-group header-button-group">
                      <button type="button" className="btn btn-default design-canvas-button" 
                        onClick={this.clearDiscardedDesigns}>Clear Discarded Ideas</button>
                    </div>) : null}
                  {<div 
                    className="btn-group header-button-group">
                    <button type="button" className="btn btn-default design-canvas-button" 
                      onClick={this.clearAllDesigns}>Clear All Ideas</button>
                  </div>}
                  {this.state.activeDesignPanel == "saved" ? (<div 
                    className="btn-group header-button-group">
                    <button type="button" 
                      onClick={this.exportSavedDesigns}
                      className="btn btn-default design-canvas-button">Export Saved Ideas</button>
                  </div>) : null}
                </div>
              </div>  
              {(!this.state.solutionsFound ? (
                <div className="alert alert-warning alert-dismissible design-canvas-alert" role="alert">
                  <strong>Sorry!</strong> Scout was not able to find any more layout ideas for your wireframes. <br /> <br />
                  <span>Adjust your constraints in the Outline panel to help Scout find more layout ideas.</span>
                  <button type="button" className="close" aria-label="Close"
                    onClick={this.closeNoSolutionsAlert}>
                    <span aria-hidden="true">&times;</span>
                  </button>
                </div>) : undefined)}
              {(this.state.activeDesignPanel == "saved" && savedCanvases.length == 0) ? 
                (<div className="designs-area-alert-container">
                  <div className="card card-body bg-light">
                    <span>You currently have no saved layout ideas. Click the star icon above a layout idea canvas in the <span className="card-emph">Under Consideration</span> panel to save an idea.</span>
                  </div>
                </div>) : null
              }
              {(this.state.activeDesignPanel == "discarded" && discardedCanvases.length == 0) ? 
                (<div className="designs-area-alert-container">
                  <div className="card card-body bg-light">
                    <span>You currently have no discarded layout ideas. Click the trash icon above a layout idea canvas in the <span className="card-emph">Under Consideration</span> panel to discard ideas that you don't like.</span>
                  </div>
                </div>) : null
              }
              <div className="design-canvas-container">
                  { this.state.activeDesignPanel == "designs" ? 
                    (<div className="panel designs-container current-designs-container panel-default">{
                      (pinnedCanvases.length ? <DesignCanvasContainer 
                        saved={true}
                        onDrop={this.moveDesignCanvas}
                        designCanvases={pinnedCanvases} /> : null)}
                      {(designCanvases.length ? (<DesignCanvasContainer 
                        onDrop={this.moveDesignCanvas}
                        designCanvases={designCanvases} />) : 
                        (<div className="designs-area-alert-container">
                          <div className="card card-body bg-light">
                            <span>You currently have no layout ideas under consideration. Click <span className="card-emph">See More Layout Ideas</span> in the outline to see more.</span>
                          </div>
                        </div>))}
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
