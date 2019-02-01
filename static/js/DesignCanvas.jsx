// App.jsx
import React from "react";
import DesignCanvasMenu from "./DesignCanvasMenu"; 
import DesignMenu from "./DesignMenu";
import DesignCanvasSVGWidget from "./DesignCanvasSVGWidget";
import groupSVG from '../assets/illustrator/groupDesign.svg';
import '../css/DesignCanvas.css'; 

export default class DesignCanvas extends React.Component {
  constructor(props) {
  	super(props);

  	// Object shapes to be drawn onto the canvas
  	this.elements = props.elements; 
  	this.id = props.id; 
  	this.elementDict = {}; 

    // The original solution shapes from the solver
    // Should remain by later feedback constraints
    this.originalElements = props.originalElements; 
    this.renders = 0; 

  	this.state = {
      childSVGs: [],
  		constraintsMenuShape: undefined, // Current shape that triggered the open menu
      designMenu: undefined, // The design saving options menu with trash and star icons
      savedState: props.savedState, 
      valid: props.valid, 
      new: props.new, 
      invalidated: props.invalidated, 
      conflicts: props.conflicts, // The conflicting constraints current if there are any
      added: props.added, // The elements that were added since this solution was generated
      removed: props.removed, // The elements that were removed since this solution was generated
      canvasShape: undefined, // The root level shape of the DesignCanvas
      hovered: false
  	}; 

  	// a callback method to update the constraints canvas when a menu item is selected
  	this.updateConstraintsCanvas = props.updateConstraintsCanvas; 
    this.getConstraintsCanvasShape = props.getConstraintsCanvasShape;
    this.showWidgetFeedback = props.showWidgetFeedback; 

    // // Way to close all of the right click menus currently open before opening a new one
    // this.closeRightClickMenus = props.closeRightClickMenus; 

    // Callback method in the parent PageContainer to get a widget and widget feedback item to be highlighted in the ConstraintsCanvas
    this.highlightWidgetFeedback = props.highlightWidgetFeedback; 
    this.highlightAddedWidget = props.highlightAddedWidget; 

    this.canvasWidth = 375; 
    this.canvasHeight = 667; 

    // Original scaling factor
    this.scalingFactor = this.getScalingFactor();
  }

  static getDerivedStateFromProps(nextProps, prevState) {
    return {
      constraintsMenuShape: prevState.constraintsMenuShape,
      designMenu: prevState.designMenu, 
      savedState: prevState.savedState,
      valid: nextProps.valid, 
      new: nextProps.new, 
      invalidated: nextProps.invalidated, 
      added: nextProps.added, 
      removed: nextProps.removed, 
      conflicts: nextProps.conflicts,
    }    
  }

  componentDidMount() {
    this.drawDesign();
  }
 
  getScalingFactor = () => {
    if(this.props.zoomed) {
      return 1.5; 
    }

    // Return the amount of scaling to use depending on the state of this DesignCanvas
    if(this.state.savedState == 1 || this.state.savedState == -1 || this.state.invalidated) {
      return 0.5; 
    } 
    
    return 0.5;
  }

  performActionAndCloseMenu = (menuTriggerShape, action, actionType, property) => {
    // Do the menu action and close the menu 
    return (evt) => {
      // Shape and option clicked on should be the arguments here
      // The linked shape in the constraints canvass
      this.updateConstraintsCanvas(menuTriggerShape, action, actionType, property); 
      this.hideMenu();
    }
  }

  hideMenu = () => {
    if(this.state.constraintsMenuShape) {
      this.setState({
        constraintsMenuShape: undefined, 
      });  
    }
  }

  getDesignCanvasWidget = (shape, svgSource, width, height, left, top) => {
    let shapeId = shape.name;
    let inMainCanvas = (this.state.savedState == 0 && (!this.state.invalidated)); 
    return (<DesignCanvasSVGWidget 
            key={shapeId} 
            shape={shape} 
            id={shapeId} 
            source={svgSource}            
            width={width}
            height={height}
            left={left}
            top={top}
            scaling={this.scalingFactor}
            inMainCanvas={inMainCanvas}
            showWidgetFeedback={this.showWidgetFeedback}/>); 
  }

  getSVGSource = (node) => {
    if(node.type == "group" && !node.alternate) {
      return groupSVG;
    }

    let svgID = node.id; 
    if(node.alternate) {
      svgID = node.alternate; 
    }

    let svgElements = this.props.svgWidgets; 
    let svgElement = svgElements.filter(element => element.id == svgID); 
    if(svgElement && svgElement.length) {
      svgElement = svgElement[0]; 
      return svgElement.svgData; 
    }

    return ""; 
  }

  createSVGElement = (shape) => {
    // Get the control SVG element from the control type
    let type = shape.type; 
    let svgSource = this.getSVGSource(shape); 
    if(svgSource != undefined) {
      let padding = 0; 
      if(shape.type == "group" && !shape.alternate) {
        padding = 5;
      }

      let computedHeight = (shape.height * this.scalingFactor + (padding * 2));
      let computedWidth = (shape.width * this.scalingFactor + (padding * 2)); 
      let computedLeft = ((shape.x * this.scalingFactor) - padding); 
      let computedTop = ((shape.y * this.scalingFactor) - padding);

      let designCanvasWidget = this.getDesignCanvasWidget(shape, svgSource, computedWidth, computedHeight, computedLeft, computedTop);
      this.state.childSVGs.push(designCanvasWidget);
      this.setState({
        childSVGs: this.state.childSVGs
      }); 
    }
  }

  drawDesign = () => {
    // Initialize the canvas and page elements first 
    // so they are at the top of the dom hierarchy
    let canvas = this.elements["canvas"]; 
    this.createSVGElement(canvas); 
    this.setState({
      canvasShape: canvas
    });

    let elementsList = []; 
    for(let elementID in this.elements) {
      if(this.elements.hasOwnProperty(elementID)) {
        let element = this.elements[elementID];
        if(element.type != "canvas") {
          elementsList.push(element); 
        }
      }
    }

    // Make sure the elements are sorted by containment 
    elementsList.sort(function(a, b) {
      let a_x = a.x; 
      let a_y = a.y; 
      let a_width = a.width;
      let a_height = a.height; 

      let b_x = b.x; 
      let b_y = b.y; 
      let b_width = b.width; 
      let b_height = b.height; 

      // Sort by containment
      if(a_x >= b_x && a_y >= b_y && (a_y+a_height <= b_y+b_height) && (a_x+a_width <= b_x+b_width)) {
        // Sort b first if b contains a so it appears higher in the DOM hierarchy
        return 1; 
      }

      return -1; 
    }); 

    for(let i=0; i<elementsList.length; i++) {
      let element = elementsList[i]; 
      this.createSVGElement(element); 
    }
  }

  performDesignCanvasMenuAction = (action) => {
    // For a zoomed design, perform these actions on the linked design instead 
    // of the zoomed in design ID as that is not maintained in the solutionsMap
    // in PageContainer
    let designId = this.id; 
    if(this.props.zoomed) {
      designId = this.props.linkedSolutionId; 
    }

    if(action == "save") {
      this.props.saveDesignCanvas(designId);
      this.state.savedState = 1; 
    }
    else if(action == "trash") {
      this.props.trashDesignCanvas(designId);
      this.state.savedState = -1; 
    }
    else if(action == "like"){
      // Do something here 
      this.props.getRelativeDesigns(this.originalElements, "like"); 
    }
    else if(action == "zoom") {
      // Open up the zoomed in design canvas dialog
      this.props.zoomInOnDesignCanvas(designId);
    }

    this.setState({
      designMenu: undefined, 
      savedState: this.state.savedState
    });
  }

  showMenuAndHighlightConstraints = (e) => {
    let saved = this.state.savedState == 1; 
    let trashed = this.state.savedState == -1; 
    let invalidated = this.state.invalidated; 
    if(saved || trashed || invalidated) {
      // Return if the canvas is currently in the saved, trashed areas or is an invalidated design 
      return; 
    }

    // Trigger constraint highlighting if the solution is not current valid
    // Do not trigger constraint highlighting if the solution is in the zoom container
    if(!this.state.valid && !this.props.zoomed) {
      if(this.state.conflicts) {
        for(var i=0; i<this.state.conflicts.length; i++) {
          var conflict = this.state.conflicts[i];
          var variable = conflict.variable;
          this.highlightWidgetFeedback(conflict.shape_id, variable, true); 
        }
      }

      if(this.state.added) {
        for(var i=0; i<this.state.added.length; i++) {
          var addedID = this.state.added[i]; 
          this.highlightAddedWidget(addedID, true); 
        }
      }
    }

    this.setState({
      hovered: true
    });
  }

  closeMenuAndRemoveHighlightConstraints = (e) => {
    // Trigger constraint highlighting if the solution is not current valid
    if(!this.state.valid) {
      if(this.state.conflicts) {
        for(var i=0; i<this.state.conflicts.length; i++) {
          var conflict = this.state.conflicts[i];
          var variable = conflict.variable; 
          this.highlightWidgetFeedback(conflict.shape_id, variable, false); 
        }
      }

      if(this.state.added) {
        for(var i=0; i<this.state.added.length; i++) {
          var addedID = this.state.added[i]; 
          this.highlightAddedWidget(addedID, false); 
        }
      }
    }

    this.setState({
      hovered: false
    });
  }

  render () {
    // The shape metadata and location for the current opened constraints menu, if there is one
    let constraintsMenuShape = this.state.constraintsMenuShape; 

    // The current design menu object for saving and trashing the designs 
    let saved = this.state.savedState == 1; 
    let trashed = this.state.savedState == -1; 
    let valid = this.state.valid; 
    let menuVisible = !saved && !trashed && valid && !this.state.hovered; 
    let invalidated = this.state.invalidated; 
    let scalingFactor = this.getScalingFactor();      
    let inMainCanvas = (this.state.savedState == 0 && (!this.state.invalidated)); 
    let childSVGs = this.state.childSVGs; 

    // Show invalid designs indicators? 
    // Don't show it for the saved designs that are in the saved area. 
    let showInvalidIndicatorLines = (!this.state.valid) && (!saved)

    return  (      
      <div 
           className={"canvas-container " + " " + ((!this.state.valid && !inMainCanvas) ? "canvas-container-invalid-scaled" : "")} 
           id={"canvas-box-" + this.id} 
           style={{
            height: (this.canvasHeight * scalingFactor) + "px", 
            width: (this.canvasWidth * scalingFactor) + "px", 
            backgroundColor: "#ffffff"}}> 
        <DesignMenu 
          showZoom={!this.props.zoomed}
          visible={menuVisible}
          hidden={saved || trashed || invalidated}
          menuAction={this.performDesignCanvasMenuAction}
          new={this.state.new} />
        <div id={"design-canvas-" + this.id} 
            className={"design-canvas " + (showInvalidIndicatorLines ? "canvas-container-invalid " : " ") 
            + (this.state.hovered ? "hovered " : " ")}
            onClick={this.showWidgetFeedback.bind(this, "canvas")}
            onMouseEnter={this.showMenuAndHighlightConstraints} 
            onMouseLeave={this.closeMenuAndRemoveHighlightConstraints}
            style={{height: "100%", width: "100%"}}>
          {childSVGs}
        </div>
	    </div>); 
  }
}









