// App.jsx
import React from "react";
import '../css/bootstrap.min.css';
import '../css/Canvas.css'; 
import '../css/PageContainer.css';
import ConstraintsCanvas from "./ConstraintsCanvas"; 
import WidgetsContainer from "./WidgetsContainer"; 
import WidgetsContainerSVGWidget from "./WidgetsContainerSVGWidget"; 
import Constants from './Constants'; 
import DesignCanvas from './DesignCanvas';
import { DragDropContextProvider } from 'react-dnd'; 
import HTML5Backend from 'react-dnd-html5-backend';
import $ from 'jquery';
import SVGInline from "react-svg-inline"; 
import ConstraintsCanvasSVGWidget from './ConstraintsCanvasSVGWidget';
import pageLogo from '../assets/logo.svg';

// import field from '../assets/illustrator/field.svg';
// import search from '../assets/illustrator/search.svg';
// import image from '../assets/illustrator/image.svg';
// import image2 from '../assets/illustrator/image2.svg';
// import image3 from '../assets/illustrator/image3.svg';
// import placeholder from '../assets/illustrator/placeholder.svg';
// import filledButton from '../assets/illustrator/filledButton.svg';
// import orangeButton from '../assets/illustrator/orangeButton.svg';
// import label from '../assets/illustrator/label.svg';
// import orangeLabel from '../assets/illustrator/orangeLabel.svg'; 
// import labelContainer from '../assets/illustrator/labelContainer.svg';
// import groupContainer from '../assets/illustrator/groupContainer.svg';
// import repeatGrid from '../assets/illustrator/repeatGrid.svg';
// import multilineLabel from '../assets/illustrator/multiline_label.svg';
// import smallLabelStatic from '../assets/illustrator/smallLabel_widgets.svg';
// import smallLabelDynamic from '../assets/illustrator/smallLabel.svg';
// import smallLabelStatic2 from '../assets/illustrator/smallLabel_widgets_2.svg';
// import smallLabelDynamic2 from '../assets/illustrator/smallLabel_2.svg';
// import logo from '../assets/illustrator/logo.svg';
// import newsLogo from '../assets/illustrator/newsLogo.svg';

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
      svgWidgets: []
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
  addShapeToConstraintsCanvas = (src, width, height) => {
    return () => {
      this.constraintsCanvasRef.current.addShapeToCanvas(src, width, height);
    }
  }

  clearShapesFromConstraintsCanvas = () => {
    this.constraintsCanvasRef.current.clearShapesFromCanvas(); 
  }

  getDesignCanvas = (solution) => {
    return (<DesignCanvas 
              key={solution.id} id={solution.id} 
              ref={"design-canvas-" + solution.id}
              elements={solution.elements}
              savedState={solution.saved}
              valid={solution.valid}
              conflicts={solution.conflicts}
              added={solution.added}
              removed={solution.removed}
              invalidated={solution.invalidated}
              getConstraintsCanvasShape={this.getConstraintsCanvasShape}
              updateConstraintsCanvas={this.updateConstraintsCanvasFromDesignCanvas}
              highlightAddedWidget={this.highlightAddedWidget}
              highlightWidgetFeedback={this.highlightWidgetFeedback}
              saveDesignCanvas={this.saveDesignCanvas} 
              trashDesignCanvas={this.trashDesignCanvas}
              getRelativeDesigns={this.getRelativeDesigns}
              closeRightClickMenus={this.closeRightClickMenus} />); 
  }

  checkSolutionValidity = (options={}) => {
    console.log("check validity");
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
    this.setState({
      solutions: this.state.solutions
    }); 
  }

  trashDesignCanvas = (designCanvasID) => {
    // Retrieve a design canvas by its ID
    let solution = this.solutionsMap[designCanvasID];
    solution.saved = -1; 

    // Update the state
    this.setState({
      solutions: this.state.solutions
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

  // getWidgetPallette = () => {
  //   if(this.state.currentPallette == "hollywood") {
  //     return (
  //       <div>
  //         <SVGInline className="widget-control widget-control-button" 
  //           height={Constants.controlHeights('button') + "px"} width={Constants.controlWidths('button') + "px"} 
  //           svg={ filledButton } onClick={this.addShapeToConstraintsCanvas('button', 'button', filledButton)}/>
  //         <div className="widget-control-group">
  //           <SVGInline className="widget-control widget-control-label" 
  //             height={Constants.controlHeights('label') + "px"} width={Constants.controlWidths('label') + "px"} 
  //             svg={ label } onClick={this.addShapeToConstraintsCanvas('label', 'label', label)}/>
  //           <SVGInline className="widget-control widget-control-label" 
  //             height={Constants.controlHeights('smallLabel2') + "px"} width={Constants.controlWidths('smallLabel2') + "px"} 
  //             svg={ smallLabelStatic2 } onClick={this.addShapeToConstraintsCanvas('label', 'smallLabel2', smallLabelDynamic2)}/>
  //           <SVGInline className="widget-control widget-control-label" 
  //             height={Constants.controlHeights('multilineLabel') + "px"} width={Constants.controlWidths('multilineLabel') + "px"} 
  //             svg={ multilineLabel } onClick={this.addShapeToConstraintsCanvas('paragraph', 'multilineLabel', multilineLabel)}/>
  //         </div>
  //         <div className="widget-control-group">
  //           <SVGInline className="widget-control widget-control-image" 
  //             height={Constants.controlHeights('image') + "px"} width={Constants.controlWidths('image') + "px"} 
  //             svg={ image } onClick={this.addShapeToConstraintsCanvas('image', 'image', image)}/> 
  //           <SVGInline className="widget-control widget-control-placeholder" 
  //             height={Constants.controlHeights('image') + "px"} width={Constants.controlWidths('image') + "px"} 
  //             svg={ image2 } onClick={this.addShapeToConstraintsCanvas('image', 'image2', image2)}/>
  //           <SVGInline className="widget-control widget-control-placeholder" 
  //             height={Constants.controlHeights('image') + "px"} width={Constants.controlWidths('image') + "px"} 
  //             svg={ image3 } onClick={this.addShapeToConstraintsCanvas('image', 'image3', image3)}/>
  //           <SVGInline className="widget-control widget-control-placeholder" 
  //             height={Constants.controlHeights('placeholder') + "px"} width={Constants.controlWidths('placeholder') + "px"} 
  //             svg={ placeholder } onClick={this.addShapeToConstraintsCanvas('image', 'placeholder', placeholder)}/>
  //         </div>
  //         <SVGInline className="widget-control widget-container" svg={ groupContainer } 
  //           height={Constants.controlHeights('group') + "px"} width={Constants.controlWidths('group') + "px"}
  //           onClick={this.addShapeToConstraintsCanvas('group', 'group', groupContainer)}/>
  //       </div>); 
  //   }
  //   else {
  //     return (
  //     <div className="widget-control-group">
  //       <SVGInline className="widget-control widget-control-field" 
  //                 height={Constants.controlHeights('field') + "px"} width={Constants.controlWidths('field') + "px"} 
  //                 svg={ field } onClick={this.addShapeToConstraintsCanvas('field', 'field', field)}/>
  //       <SVGInline className="widget-control widget-control-button" 
  //         height={Constants.controlHeights('button') + "px"} width={Constants.controlWidths('button') + "px"} 
  //         svg={ orangeButton } onClick={this.addShapeToConstraintsCanvas('button', 'orangeButton', orangeButton)}/>
  //       <SVGInline className="widget-control widget-control-label" 
  //         height={Constants.controlHeights('label') + "px"} width={Constants.controlWidths('label') + "px"} 
  //         svg={ orangeLabel } onClick={this.addShapeToConstraintsCanvas('label', 'orangeLabel', orangeLabel)}/>
  //      <SVGInline className="widget-control widget-control-label" 
  //         height={Constants.controlHeights('smallLabel') + "px"} width={Constants.controlWidths('smallLabel') + "px"} 
  //         svg={ smallLabelStatic } onClick={this.addShapeToConstraintsCanvas('label', 'smallLabel', smallLabelDynamic)}/>
  //       <SVGInline className="widget-control widget-container" svg={ groupContainer } 
  //         height={Constants.controlHeights('group') + "px"} width={Constants.controlWidths('group') + "px"}
  //         onClick={this.addShapeToConstraintsCanvas('group', 'group', groupContainer)}/>
  //       <SVGInline className="widget-control widget-control-logo" 
  //         height={Constants.controlHeights('image') + "px"} width={Constants.controlWidths('image') + "px"} 
  //         svg={ logo } onClick={this.addShapeToConstraintsCanvas('image', 'logo', logo)}/>
  //     </div>); 
  //   }
  // }

  // getBackgroundColors = () => {
  //   let hollywoodColors = ['#C5CAE9', '#FFFFFF', '#3F51B5', '#212121', '#757575', '#BDBDBD', '#CFD8DC', '#dfe4ea', '#ced6e0', '#f1f2f6']
  //   let harvestColors = ['#FF5722', '#D7CCC8', '#FFFFFF', '#757575', '#795548', '#BDBDBD', '#FFECB3']

  //   // Replace with the above when we can load these in
  //   if(this.state.currentPallette == "hollywood") {
  //     return hollywoodColors; 
  //   }
  //   else {
  //     return harvestColors; 
  //   }
  // }

  // configureWidgetPallette = (e) => { Configure later to enable more sets of
  // pallettes to be loaded   if(this.state.currentPallette == 'hollywood') {
  // this.setState({       currentPallette: 'farming'     });    }   else {
  // this.setState({       currentPallette: 'hollywood'     });    }

  //   // Also clear out the current set of solutions
  //   // Later we should probably prompt for exporting before destroying the designs
  //   this.setState({
  //     solutions: []
  //   });

  //   this.clearShapesFromConstraintsCanvas();
  // }

  // handleWidgetSVGDrag = (evt) => {
  //   // Prevent the browser's default drag behavior
  //   evt.preventDefault();
  // }

  // handleWidgetSVGDrop = (evt) => {
  //   console.log("being called");
  //   // Default behavior is to open the file. Prevent this
  //   evt.preventDefault(); 

  //   if (ev.dataTransfer.items) {
  //     for (var i = 0; i < ev.dataTransfer.items.length; i++) {
  //       if (ev.dataTransfer.items[i].kind === 'file') {
  //         var file = ev.dataTransfer.items[i].getAsFile();
  //         console.log('... file[' + i + '].name = ' + file.name);
  //       }
  //     }
  //   } else {
  //     // Use DataTransfer interface to access the file(s)
  //     for (var i = 0; i < ev.dataTransfer.files.length; i++) {
  //       console.log('... file[' + i + '].name = ' + ev.dataTransfer.files[i].name);
  //     }
  //   } 

  //   this.removeDragData(evt); 
  // }

  readSVGIntoWidgetContainer = (e) => {
    let fileData = e.target.result; 
    if(fileData) {
      this.setState({
        svgWidgets: this.state.svgWidgets.concat(
           <WidgetsContainerSVGWidget 
            className="widget-control" 
            svgData={fileData}
            addShapeToConstraintsCanvas={this.addShapeToConstraintsCanvas}/>
        )
      })

    }
  }

  handleFileDrop = (item, monitor) => {
    if (monitor) {
      const droppedFiles = monitor.getItem().files; 
      this.setState({
        droppedFiles: droppedFiles
      });

      // Ensure the files are SVG 

      // Download the dropped file contents
      for(let i=0; i<droppedFiles.length; i++) {
        let file = droppedFiles[i]; 
        let reader = new FileReader(); 
        reader.onload = this.readSVGIntoWidgetContainer; 
        reader.readAsText(file); 
      }
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
                  return this.getDesignCanvas(solution); 
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
        return self.getDesignCanvas(solution); 
      }); 

    const trashedCanvases = this.state.solutions
      .filter((solution) => { return solution.saved == -1; })
      .map((solution) => {
          if(solution.saved == -1) {
            return self.getDesignCanvas(solution); 
          }
        });

    const invalidatedCanvases = this.state.solutions
      .filter((solution) => { 
        return solution.invalidated == true; 
      })
      .map((solution) => {
        if(solution.invalidated == true) {
          return self.getDesignCanvas(solution); 
        }
      });    

    // const currentWidgetPallette = this.getWidgetPallette();  
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
                <WidgetsContainer onDrop={this.handleFileDrop} widgets={this.state.svgWidgets} />
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
                      onClick={this.checkSolutionValidity.bind(this, {getDesigns: true})}>More not like these</button>
                    <button 
                      type="button" 
                      className="btn btn-default design-canvas-button" 
                      onClick={this.checkSolutionValidity.bind(this, {getDesigns: true})}>More like these</button>
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
                      <div className="design-body" onScroll={this.hideDesignsAlert}>
                        {designCanvases}
                      </div>
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
        </div>
      </DragDropContextProvider>
    ); 
  }
}