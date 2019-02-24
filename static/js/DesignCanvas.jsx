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
  	this.id = props.id; 
  	this.elementDict = {}; 

    // The original solution shapes from the solver
    // Should remain by later feedback constraints
    this.originalElements = props.originalElements; 

  	this.state = {
      childSVGs: [],
      elements: props.elements, 
      designMenu: undefined, // The design saving options menu with trash and star icons
      savedState: props.savedState, 
      valid: props.valid, 
      new: props.new, 
      invalidated: props.invalidated, 
      added: props.added, // The elements that were added since this solution was generated
      removed: props.removed, // The elements that were removed since this solution was generated
      canvasShape: props.elements["canvas"], // The root level shape of the DesignCanvas
      hovered: false, 
      primarySelection: props.primarySelection, 
      elementsList: []
  	}; 

  	// a callback method to update the constraints canvas when a menu item is selected
  	this.updateConstraintsCanvas = props.updateConstraintsCanvas; 
    this.getConstraintsCanvasShape = props.getConstraintsCanvasShape;
    this.displayWidgetFeedback = props.displayWidgetFeedback; 

    // Callback method in the parent PageContainer to get a widget and widget feedback item to be highlighted in the ConstraintsCanvas
    this.highlightFeedbackConflict = props.highlightFeedbackConflict; 
    this.highlightAddedWidget = props.highlightAddedWidget; 

    this.canvasWidth = 360; 
    this.canvasHeight = 640; 

    // Original scaling factor
    this.scalingFactor = this.getScalingFactor();
  }

  static getDerivedStateFromProps(nextProps, prevState) {
    let elementsChanged = nextProps.elements != prevState.elements; 
    return {
      designMenu: prevState.designMenu, 
      savedState: prevState.savedState,
      valid: nextProps.valid, 
      new: nextProps.new, 
      invalidated: nextProps.invalidated, 
      added: nextProps.added, 
      removed: nextProps.removed, 
      conflicts: prevState.conflicts,
      primarySelection: nextProps.primarySelection, 
      canvasShape: prevState.canvasShape, 
      elements: prevState.elements
    }    
  }
  
  componentDidMount() {
    this.initElements();
  }

  componentDidUpdate(prevProps, prevState) {
    if(prevProps.elements != this.props.elements) {
      this.initElements(); 
    }
  }

  getScalingFactor = () => {
    if(this.props.zoomed) {
      return 1.5; 
    }

    if(this.state.savedState == 1) {
      return 1.0; 
    }

    // Return the amount of scaling to use depending on the state of this DesignCanvas
    if(this.state.savedState == -1 || this.state.invalidated) {
      return 0.5; 
    } 
    
    return 0.5;
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
            primarySelection={this.state.primarySelection}
            displayWidgetFeedback={this.displayWidgetFeedback}/>); 
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
      return designCanvasWidget; 
    }
  }

  initElements = () => {
    // Initialize the canvas and page elements first 
    // so they are at the top of the dom hierarchy
    let canvas = this.props.elements["canvas"]; 
    this.createSVGElement(canvas); 
    this.setState({
      canvasShape: canvas
    });

    let elementsList = []; 
    for(let elementID in this.props.elements) {
      if(this.state.elements.hasOwnProperty(elementID)) {
        let element = this.props.elements[elementID];
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
      let a_is_group = a.type == "group" && !a.alternate; 

      let b_x = b.x; 
      let b_y = b.y; 
      let b_width = b.width; 
      let b_height = b.height;
      let b_is_group = b.type == "group" && !b.alternate; 

      // Sort by containment
      if(a_is_group && !b_is_group) {
        // Groups should be always sorted after elements
        return -1; 
      }
      else if(!a_is_group && b_is_group) {
        return 1; 
      }
      else if(a_is_group && b_is_group) {
        if(a_x >= b_x && a_y >= b_y && (a_y+a_height <= b_y+b_height) && (a_x+a_width <= b_x+b_width)) {
          // Sort b first if b contains a so it appears higher in the DOM hierarchy
          // then sort by boundigng box
          return -1; 
        }
        else if(b_x >= a_x && b_y >= a_y && (b_y+b_height <= a_y+a_height) && (b_x+b_width <= a_x+a_width)) {
          return -1; 
        }
      }

      return 0; 
    }); 

    this.setState({
      elementsList: elementsList
    }); 
  }

  performDesignCanvasMenuAction = (action) => {
    // For a zoomed design, perform these actions on the linked design instead 
    // of the zoomed in design ID as that is not maintained in the solutionsMap
    // in PageContainer
    let designId = this.id; 
    if(this.props.zoomed) {
      designId = this.props.solutionID; 
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

  highlightConflicts = (e) => {
    let saved = this.state.savedState == 1; 
    let trashed = this.state.savedState == -1; 
    let invalidated = this.state.invalidated; 
    if(saved || trashed || invalidated) {
      // Return if the canvas is currently in the saved, trashed areas or is an invalidated design 
      return; 
    }

    // Trigger constraint highlighting if the solution is not current valid
    // Do not trigger constraint highlighting if the solution is in the zoom container
    if((!this.state.valid || this.props.conflicts.length) && !this.props.zoomed) {
      if(this.props.conflicts) {
        for(var i=0; i<this.props.conflicts.length; i++) {
          var conflict = this.props.conflicts[i];
          this.highlightFeedbackConflict(conflict, true); 
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

  unhighlightConflicts = (e) => {
    // Trigger constraint highlighting if the solution is not current valid
    if(!this.state.valid || this.props.conflicts.length) {
      if(this.props.conflicts) {
        for(var i=0; i<this.props.conflicts.length; i++) {
          let conflict = this.props.conflicts[i]; 
          this.highlightFeedbackConflict(conflict, false); 
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

  onCanvasClick = (evt) => {
    // When the canvas node is clicked, display the widget feedback
    evt.stopPropagation();

    this.displayWidgetFeedback(this.state.canvasShape);
  }

  render () {
    // The current design menu object for saving and trashing the designs 
    let saved = this.state.savedState == 1; 
    let trashed = this.state.savedState == -1; 
    let valid = this.state.valid; 
    let hasConflicts = this.props.conflicts.length; 
    let menuVisible = !this.state.hovered; 
    let invalidated = this.state.invalidated; 
    let scalingFactor = this.getScalingFactor();      
    let inMainCanvas = (this.state.savedState == 0 && (!this.state.invalidated)); 
    let childSVGs = this.state.childSVGs; 

    // Show invalid designs indicators? 
    // Don't show it for the saved designs that are in the saved area. 
    let showInvalidIndicatorLines = (!this.state.valid || this.props.conflicts.length) && (!saved)

    // Process the elements list
    const svgElements = this.state.elementsList.map((element) => {
        return this.createSVGElement(element);
    });

    const canvasIsPrimary = this.props.primarySelection && this.props.primarySelection == this.state.canvasShape; 
    const canvasIsSecondary = this.props.primarySelection && !canvasIsPrimary && this.state.canvasShape && this.props.primarySelection.name == this.state.canvasShape.name; 

    return  (      
      <div 
           className={"canvas-container " + " " + (((!this.state.valid || this.props.conflicts.length) && !inMainCanvas) ? "canvas-container-invalid-scaled" : "")} 
           id={"canvas-box-" + this.id}>
        <DesignMenu 
          showZoom={!this.props.zoomed}
          visible={menuVisible}
          menuAction={this.performDesignCanvasMenuAction}/>
        <div id={"design-canvas-" + this.id}
           style={{
            height: (this.canvasHeight * scalingFactor) + "px", 
            width: (this.canvasWidth * scalingFactor) + "px"}}
            className={"design-canvas " + (showInvalidIndicatorLines ? "canvas-container-invalid " : " ") 
            + (this.state.hovered ? "hovered " : " ")
            + (canvasIsPrimary ? "primary-selection " : " ")
            + (canvasIsSecondary ? "secondary-selection " : " ")
            + (this.state.new ? "new-design" : "")}
            onClick={this.onCanvasClick}
            onMouseEnter={this.highlightConflicts} 
            onMouseLeave={this.unhighlightConflicts}>
          {svgElements}
        </div>
	    </div>); 
  }
}









