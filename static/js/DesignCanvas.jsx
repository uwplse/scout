// App.jsx
import React from "react";
import DesignCanvasMenu from "./DesignCanvasMenu"; 
import Constants from "./Constants";
import DesignMenu from "./DesignMenu";
import DesignCanvasSVGWidget from "./DesignCanvasSVGWidget";
import group from '../assets/illustrator/groupDesign.svg';
import item from '../assets/illustrator/item.svg';
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
      constraintsMenuX: 0, // Current X location of the constraints menu
      constraintsMenuY: 0, // Current Y location of the constriants menu
      designMenu: undefined, // The design saving options menu with trash and star icons
      savedState: props.savedState, 
      valid: props.valid, 
      invalidated: props.invalidated, 
      conflicts: props.conflicts, // The conflicting constraints current if there are any
      added: props.added, // The elements that were added since this solution was generated
      removed: props.removed, // The elements that were removed since this solution was generated
      designShape: undefined, // The root level shape of the DesignCanvas
      hovered: false, 
      backgroundColor: "#E1E2E1"
  	}; 

  	// a callback method to update the constraints canvas when a menu item is selected
  	this.updateConstraintsCanvas = props.updateConstraintsCanvas; 
    this.getConstraintsCanvasShape = props.getConstraintsCanvasShape;

    // Way to close all of the right click menus currently open before opening a new one
    this.closeRightClickMenus = props.closeRightClickMenus; 

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
      constraintsMenuX: prevState.constraintsMenuX,
      constraintsMenuY: prevState.constraintsMenuY, 
      constraintsMenuShape: prevState.constraintsMenuShape,
      designMenu: prevState.designMenu, 
      savedState: prevState.savedState, 
      backgroundColor: prevState.backgroundColor,
      valid: nextProps.valid, 
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
      return 1.0; 
    }

    // Return the amount of scaling to use depending on the state of this DesignCanvas
    if(this.state.savedState == 1 || this.state.savedState == -1 || this.state.invalidated) {
      return 0.10; 
    } 
    
    return 0.5;
  }

  initDesignCanvas = (shape) => {
    // Intialize the background color and root level design shape
    this.setState({
      designShape: shape,
      backgroundColor: shape.background_color
    });
  }

  showConstraintsContextMenu = (shape) => {
    return (evt) => {
      evt.stopPropagation();
      evt.preventDefault();

      // Close all right click menus before opening new ones
      this.closeRightClickMenus();

      this.setState({
        constraintsMenuShape: undefined
      }); 

      if(this.state.savedState == 0) {
        this.setState({
          constraintsMenuShape: shape, 
          constraintsMenuX: evt.clientX, 
          constraintsMenuY: evt.clientY, 
        });
      }
    }
  }

  performActionAndCloseMenu = (menuTriggerShape, action, actionType) => {
    // Do the menu action and close the menu 
    return (evt) => {
      // Shape and option clicked on should be the arguments here
      // The linked shape in the constraints canvass
      this.updateConstraintsCanvas(menuTriggerShape, action, actionType); 
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
            contextMenu={this.showConstraintsContextMenu}/>); 
  }

  getSVGSourceByID = (id) => {
    let svgElements = this.props.svgWidgets; 
    let svgElement = svgElements.filter(element => element.id == id); 
    if(svgElement && svgElement.length) {
      svgElement = svgElement[0]; 
      return svgElement.svgData; 
    }

    return ""; 
  }

  createSVGElement = (shape) => {
    // Get the control SVG element from the control type
    let type = shape.type; 
    let isContainer = type == "group" || type == "labelGroup" || type == "page"; 
    let isItem = shape.item;
    let svgSource = isItem ? item : (isContainer ? group : this.getSVGSourceByID(shape.id)); 
    if(svgSource != undefined) {
      let padding = 0; 
      if(isContainer) {
        padding = 5;
      }

      let computedHeight = (shape.size.height * this.scalingFactor + (padding * 2));
      let computedWidth = (shape.size.width * this.scalingFactor + (padding * 2)); 

      if(isContainer) {
        console.log(computedWidth); 
        console.log(computedHeight);
      } 
      
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
    this.initDesignCanvas(canvas); 

    let page = this.elements["page"]; 
    this.createSVGElement(page); 

    let elementsList = []; 
    for(let elementID in this.elements) {
      if(this.elements.hasOwnProperty(elementID)) {
        let element = this.elements[elementID];
        if(element.type != "canvas" && element.type != "page") {
          elementsList.push(element); 
        }
      }
    }

    // Make sure the elements are sorted by containment 
    elementsList.sort(function(a, b) {
      let a_x = a.x; 
      let a_y = a.y; 
      let a_width = a.size.width;
      let a_height = a.size.height; 

      let b_x = b.x; 
      let b_y = b.y; 
      let b_width = b.size.width; 
      let b_height = b.size.height; 

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

    // Check for the status of menuShown to see if we need to close out another menu before opening this one
    if(this.state.designMenu != undefined) {
      this.setState({
        designMenu: undefined
      }); 
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

    var designCanvas = document.getElementById("design-canvas-" + this.id); 
    var componentBoundingBox = designCanvas.getBoundingClientRect();
    
    // The menuTrigger is the JSON of the shape that triggered the open
    this.setState({
      designMenu: <DesignMenu 
                    // left={componentBoundingBox.x} 
                    // top={componentBoundingBox.y} 
                    showZoom={!this.props.zoomed}
                    menuAction={this.performDesignCanvasMenuAction} />,
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

    // Close the menu if it is open 
    var designCanvas = document.getElementById("design-canvas-" + this.id); 
    var componentBoundingBox = designCanvas.getBoundingClientRect();
    // Make sure the mouse is actually outside the div because mouse out can be triggered by child elements of this container. 
    if(e.clientX <= componentBoundingBox.x || e.clientX >= (componentBoundingBox.x + componentBoundingBox.width) 
      || e.clientY <= componentBoundingBox.y || e.clientY >= (componentBoundingBox.y + componentBoundingBox.height)) {
      if(this.state.designMenu != undefined) {
        this.setState({
          designMenu: undefined
        }); 
      }      
    }

    this.setState({
      hovered: false
    });
  }

  render () {
    // The shape metadata and location for the current opened constraints menu, if there is one
   	let constraintsMenuY = this.state.constraintsMenuY; 
   	let constraintsMenuX = this.state.constraintsMenuX; 
    let constraintsMenuShape = this.state.constraintsMenuShape; 

    // The current design menu object for saving and trashing the designs 
    let designMenu = this.state.designMenu; 
    let saved = this.state.savedState == 1; 
    let trashed = this.state.savedState == -1; 
    let valid = this.state.valid; 
    let invalidated = this.state.invalidated; 
    let scalingFactor = this.getScalingFactor();      
    let inMainCanvas = (this.state.savedState == 0 && (!this.state.invalidated)); 
    let childSVGs = this.state.childSVGs; 

    return  (      
      <div onMouseEnter={this.showMenuAndHighlightConstraints} 
           onMouseLeave={this.closeMenuAndRemoveHighlightConstraints} 
           className={"canvas-container " + " " + ((!this.state.valid && !inMainCanvas) ? "canvas-container-invalid-scaled" : "")} 
           id={"canvas-box-" + this.id} 
           style={{
            height: (this.canvasHeight * scalingFactor) + "px", 
            width: (this.canvasWidth * scalingFactor) + "px", 
            backgroundColor: this.state.backgroundColor}}> 
  			<div className={(constraintsMenuShape ? "" : "hidden")}>
        {constraintsMenuShape ? 
          (<DesignCanvasMenu 
            left={constraintsMenuX} 
            top={constraintsMenuY} 
            menuTrigger={constraintsMenuShape} 
            onClick={this.performActionAndCloseMenu} 
            getConstraintsCanvasShape={this.getConstraintsCanvasShape} />) : undefined}
  			</div>
        <div>
          {designMenu}
        </div>
        <div id={"design-canvas-" + this.id} 
            className={"design-canvas " + (!this.state.valid ? "canvas-container-invalid " : " ") 
            + (this.state.hovered ? "hovered" : "")}
            onContextMenu={this.showConstraintsContextMenu(this.state.designShape)}
            style={{height: "100%", width: "100%"}}>
          {childSVGs}
        </div>
	    </div>); 
  }
}









