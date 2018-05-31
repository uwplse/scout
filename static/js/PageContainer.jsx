// App.jsx
import React from "react";
import '../css/Canvas.css'; 
import ConstraintsCanvas from "./ConstraintsCanvas"; 
import DesignCanvas from './DesignCanvas';
import Sidebar from 'react-sidebar';
import $ from 'jquery';
import SVGInline from "react-svg-inline"; 
import SVGWidget from './SVGWidget';
import field from '../assets/illustrator/field.svg';
import search from '../assets/illustrator/search.svg';
import image from '../assets/illustrator/image.svg';
import placeholder from '../assets/illustrator/placeholder.svg';
import filledButton from '../assets/illustrator/filledButton.svg';
import labelDynamic from '../assets/illustrator/label.svg';
import labelStatic from '../assets/illustrator/label_widgets.svg';
import labelContainer from '../assets/illustrator/labelContainer.svg';
import groupContainer from '../assets/illustrator/groupContainer.svg';
import multilineLabel from '../assets/illustrator/multiline_label.svg';

export default class PageContainer extends React.Component {
  constructor(props) {
  	super(props); 

    // Method bindings
    this.getMoreDesigns = this.getMoreDesigns.bind(this); 
    this.parseSolutions = this.parseSolutions.bind(this);
    this.updateConstraintsCanvasFromDesignCanvas = this.updateConstraintsCanvasFromDesignCanvas.bind(this); 
    this.updateConstraintsCanvas = this.updateConstraintsCanvas.bind(this);
    this.getConstraintsCanvasShape = this.getConstraintsCanvasShape.bind(this);
    this.highlightWidgetFeedback = this.highlightWidgetFeedback.bind(this);
    this.clearInvalidDesignCanvases = this.clearInvalidDesignCanvases.bind(this); 
    
    this.canvas = undefined; 

    // This is the set of design canvases in the design window
    this.state = { 
      solutions: [],
      constraintChanged: false , 
      designsFound: -1, 
      treeData: []
    };   

    // Dictionaries for being able to retrieve a design canvas by ID more efficiently
    this.solutionsMap ={};

    this.constraintsCanvasRef = React.createRef();
  }

  // Update the addedShapes property on the constraints canvas to notify it to create new shapes
  // for a shape of this type
  addShapeToConstraintsCanvas(type, controlType, src) {
    this.constraintsCanvasRef.current.addShapeOfTypeToCanvas(type, controlType, src);
  }

  getDesignCanvas(solution) {
    return (<DesignCanvas 
              key={solution.id} id={solution.id} 
              elements={solution.elements}
              savedState={solution.saved}
              valid={solution.valid}
              conflicts={solution.conflicts}
              invalidated={solution.invalidated}
              getConstraintsCanvasShape={this.getConstraintsCanvasShape}
              updateConstraintsCanvas={this.updateConstraintsCanvasFromDesignCanvas}
              highlightWidgetFeedback={this.highlightWidgetFeedback}
              saveDesignCanvas={this.saveDesignCanvas.bind(this)} 
              trashDesignCanvas={this.trashDesignCanvas.bind(this)}
              getRelativeDesigns={this.getRelativeDesigns.bind(this)}/>); 
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

  getConstraintsCanvasShape(shapeId) {
    return this.constraintsCanvasRef.current.getConstraintsCanvasShape(shapeId); 
  }

  highlightWidgetFeedback(shapeId, lock, highlighted) {
    this.constraintsCanvasRef.current.highlightWidgetFeedback(shapeId, lock, highlighted);
  }

  updateConstraintsCanvasFromDesignCanvas(designCanvasShape, action, actionType) {
    // Retrieve the shape object in the constraints tree and apply teh updates
    let constraintsCanvasShape = this.getConstraintsCanvasShape(designCanvasShape.name);
    action[actionType].updateConstraintsCanvasShape(constraintsCanvasShape, designCanvasShape);

    // Notify the constraintss canvas to add or remove the widget feedback to the tree
    this.constraintsCanvasRef.current.updateWidgetFeedbacks(constraintsCanvasShape, action, actionType);

    // Check the validity of the current constraints and update valid state of solutions
    this.checkSolutionValidity();
  }

  updateConstraintsCanvas(constraintsCanvasShape, action) {
    action["undo"].updateConstraintsCanvasShape(constraintsCanvasShape, undefined);

    // Notify the constraintss canvasa
    this.constraintsCanvasRef.current.updateWidgetFeedbacks(constraintsCanvasShape, action, "undo");

    // Check for the validity of current state of constriants, and update valid state of solutions
    this.checkSolutionValidity(); 
  }

  updateSolutionValidity(solutions) {
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

  clearInvalidDesignCanvases() {
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
      
      // Invalidate the solution which means it should be moved into the right side panel 
      if(designSolution.valid) {
        designSolution.invalidated = false;
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
                  return self.getDesignCanvas(solution); 
                }); 

    const designCanvases = this.state.solutions.filter(function(solution) { return (solution.saved == 0 && (!solution.invalidated)); }) 
              .map(function(solution) {
                  return self.getDesignCanvas(solution); 
                }); 

    const trashedCanvases = this.state.solutions.filter(function(solution) { return solution.saved == -1; })
              .map(function(solution) {
                    if(solution.saved == -1) {
                      return self.getDesignCanvas(solution); 
                    }
                });

    const invalidatedCanvases = this.state.solutions.filter(function(solution) { return solution.invalidated == true; })
        .map(function(solution) {
              if(solution.invalidated == true) {
                return self.getDesignCanvas(solution); 
              }
          });      
    return (
      <div className="page-container">
        <nav className="navbar navbar-default">
         <div className="container-fluid">
          <div className="navbar-header">
            <h2>Scout</h2>
          </div>
         </div>
        </nav>
        <div className="bottom">
          <div className="panel panel-default widgets-container">
            <div className="panel-heading"> 
              <h3 className="panel-title">Widgets</h3>
            </div>  
            <div className="panel-body widgets-panel">         
              { /*<canvas id="widgets-canvas" width="150px" height="400px">
              </canvas> */ }
              <SVGInline className="widget-control widget-control-field" 
                height={SVGWidget.initialHeights('field') + "px"} width={SVGWidget.initialWidths('field') + "px"} 
                svg={ field } onClick={this.addShapeToConstraintsCanvas.bind(this, 'field', 'field', field)}/>
              { /*<SVGInline className="widget-control" svg={ search } onClick={this.addShapeToConstraintsCanvas.bind(this, 'field', 'search', search)}/> */}
              <SVGInline className="widget-control widget-control-button" 
                height={SVGWidget.initialHeights('button') + "px"} width={SVGWidget.initialWidths('button') + "px"} 
                svg={ filledButton } onClick={this.addShapeToConstraintsCanvas.bind(this, 'button', 'button', filledButton)}/>
              <SVGInline className="widget-control widget-control-label" 
                height={SVGWidget.initialHeights('label') + "px"} width={SVGWidget.initialWidths('label') + "px"} 
                svg={ labelStatic } onClick={this.addShapeToConstraintsCanvas.bind(this, 'label', 'label', labelDynamic)}/>
              <SVGInline className="widget-control widget-control-label" 
                height={SVGWidget.initialHeights('multilineLabel') + "px"} width={SVGWidget.initialWidths('multilineLabel') + "px"} 
                svg={ multilineLabel } onClick={this.addShapeToConstraintsCanvas.bind(this, 'label', 'multilineLabel', multilineLabel)}/>
              <SVGInline className="widget-control widget-control-search" 
                height={SVGWidget.initialHeights('search') + "px"} width={SVGWidget.initialWidths('search') + "px"} 
                svg={ search } onClick={this.addShapeToConstraintsCanvas.bind(this, 'field', 'search', search)}/>
              <div className="widget-control-group">
                <SVGInline className="widget-control widget-control-image" 
                  height={SVGWidget.initialHeights('image') + "px"} width={SVGWidget.initialWidths('image') + "px"} 
                  svg={ image } onClick={this.addShapeToConstraintsCanvas.bind(this, 'image', 'image', image)}/> 
                <SVGInline className="widget-control widget-control-placeholder" 
                  height={SVGWidget.initialHeights('placeholder') + "px"} width={SVGWidget.initialWidths('placeholder') + "px"} 
                  svg={ placeholder } onClick={this.addShapeToConstraintsCanvas.bind(this, 'image', 'placeholder', placeholder)}/>
                <SVGInline className="widget-control widget-container" svg={ groupContainer } 
                  onClick={this.addShapeToConstraintsCanvas.bind(this, 'group', 'group', groupContainer)}/>
              </div>
            </div>
          </div>
            {/*<div className="panel panel-default containers-container">
              <div className="panel-heading"> 
                <h3 className="panel-title">Containers</h3>
              </div>  
              <div className="panel-body containers-panel">         
                <SVGInline className="widget-control widget-container" svg={ labelContainer } onClick={this.addShapeToConstraintsCanvas.bind(this, 'labelGroup', 'labelGroup', labelContainer)}/>
              </div>
            </div>*/}
         <div className="panel panel-default constraints-container">
            <div className="panel-heading"> 
              <h3 className="panel-title">Constraints</h3>
            </div>
            <div className="constraints-canvas-container"> 
              <ConstraintsCanvas ref={this.constraintsCanvasRef} 
                updateConstraintsCanvas={this.updateConstraintsCanvas} 
                checkSolutionValidity={this.checkSolutionValidity.bind(this)}/> {/* Enables the constraints canvas to trigger re-checking solutions for validity when widgets are removed */ }
            </div>
           {/*<ConstraintsCanvas ref="constraintsCanvas" />*/}
          </div>
          <div className="panel panel-default designs-area-container">
            <div className="panel-heading"> 
              <h3 className="panel-title">Designs
                <div className="btn-group btn-group-xs designs-area-button-group">
                  <button type="button" className="btn btn-default design-canvas-button" onClick={this.getMoreDesigns}>More Designs</button>
                  <button type="button" className="btn btn-default design-canvas-button" onClick={this.clearInvalidDesignCanvases}>Clear Invalid</button>
                </div>
                <div className="btn-group btn-group-xs designs-area-button-group">
                  <button type="button" className="btn btn-default design-canvas-button" onClick={this.getMoreDesigns}>More not like these</button>
                  <button type="button" className="btn btn-default design-canvas-button" onClick={this.getMoreDesigns}>More like these</button>
                </div>
              </h3>
            </div>  
            <div className="design-canvas-container">
              <div className="left-container">
                { designCanvases.length? <div className="alert alert-success" role="alert">Here are 10 randomly selected designs.</div> : undefined }
                { savedCanvases.length ? (<div className="panel designs-container saved-designs-container panel-default">
                  <span className="save-icon glyphicon glyphicon-star" aria-hidden="true"></span>
                  <div className="panel-body saved-body">
                    {savedCanvases}
                  </div>
                </div>) : null }
                { designCanvases.length ? (<div className="panel designs-container current-designs-container panel-default">
                  <div className="design-body">
                    {designCanvases}
                  </div>
                </div>) : null }
                { trashedCanvases.length ? (<div className="panel designs-container trashed-designs-container panel-default">
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
      </div>
    ); 
  }
}