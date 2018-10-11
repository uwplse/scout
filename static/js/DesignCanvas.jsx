// App.jsx
import React from "react";
import DesignCanvasMenu from "./DesignCanvasMenu"; 
import Constants from "./Constants";
import DesignMenu from "./DesignMenu";
import DesignCanvasSVGWidget from "./DesignCanvasSVGWidget";
import field from '../assets/illustrator/field_designs.svg';
import search from '../assets/illustrator/search.svg';
import image from '../assets/illustrator/image.svg'
import image2 from '../assets/illustrator/image2.svg'
import image3 from '../assets/illustrator/image3.svg'
import logo from '../assets/illustrator/logo.svg'
import newsLogo from '../assets/illustrator/newsLogo.svg'
import placeholder from '../assets/illustrator/placeholder.svg'
import filledButton from '../assets/illustrator/filledButton.svg';
import orangeButton from '../assets/illustrator/orangeButton.svg';
import label from '../assets/illustrator/label.svg';
import orangeLabel from '../assets/illustrator/orangeLabel.svg';
import smallLabel from '../assets/illustrator/smallLabel_designs.svg';
import multilineLabel from '../assets/illustrator/multiline_label_designs.svg';
import group from '../assets/illustrator/groupDesign.svg';

export default class DesignCanvas extends React.Component {
  static svgElements(controlType) {
    let svgElements = {
      'field': field, 
      'search': search, 
      'button': filledButton, 
      'orangeButton': orangeButton,
      'label': label, 
      'orangeLabel': orangeLabel,
      'multilineLabel': multilineLabel,
      'smallLabel': smallLabel, 
      'group': group, 
      'page': group,
      'labelGroup': group,
      'placeholder': placeholder, 
      'image': image, 
      'image2': image2,
      'image3': image3,
      'logo': logo, 
      'logo2': newsLogo
      /* Add others here */
    }; 
    return svgElements[controlType]; 
  };

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
      hovered: false
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
      valid: nextProps.valid, 
      invalidated: nextProps.invalidated, 
      added: nextProps.added, 
      removed: nextProps.removed, 
      conflicts: nextProps.conflicts
    }    
  }

  componentDidMount() {
    this.drawDesign();
  }
 
  getScalingFactor = () => {
    // Return the amount of scaling to use depending on the state of this DesignCanvas
    if(this.state.savedState == 1 || this.state.savedState == -1 || this.state.invalidated) {
      return 0.10; 
    } 
    
    return 0.5;
  }

  initDesignCanvas = (shape) => {
    // Intialize the background color and root level design shape
    console.log(shape.grid); 
    this.setState({
      designShape: shape,
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

      this.setState({
        constraintsMenuShape: shape, 
        constraintsMenuX: evt.clientX, 
        constraintsMenuY: evt.clientY, 
      });
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
        constraintsMenuShape: undefined
      });  
    }
  }

  getDesignCanvasWidget = (shape, width, height, left, top) => {
    let shapeId = shape.name;
    let source = DesignCanvas.svgElements(shape.controlType);
    let inMainCanvas = (this.state.savedState == 0 && (!this.state.invalidated)); 
    return (<DesignCanvasSVGWidget 
            key={shapeId} 
            shape={shape} 
            id={shapeId} 
            source={source}            
            width={width}
            height={height}
            left={left}
            top={top}
            scaling={this.scalingFactor}
            inMainCanvas={inMainCanvas}
            contextMenu={this.showConstraintsContextMenu}/>); 
  }

  createSVGElement = (designCanvas, shape) => {
    // Get the control SVG element from the control type
    let controlType = shape.controlType;
    let svg = DesignCanvas.svgElements(controlType); 
    if(svg != undefined) {
      let padding = 0; 
      if(controlType == "group" || controlType == "labelGroup" || controlType == "page") {
        padding = 5;
      }

      let computedHeight = (shape.size.height * this.scalingFactor + (padding * 2));
      let computedWidth = (shape.size.width * this.scalingFactor + (padding * 2)); 
      let computedLeft = ((shape.x * this.scalingFactor) - padding); 
      let computedTop = ((shape.y * this.scalingFactor) - padding);

      let designCanvasWidget = this.getDesignCanvasWidget(shape, computedWidth, computedHeight, computedLeft, computedTop);
      this.state.childSVGs.push(designCanvasWidget);
      this.setState({
        childSVGs: this.state.childSVGs
      }); 
    }
  }

  drawDesign = () => {
    // When the component mounts, draw the shapes onto the canvas
    let designId = "design-canvas-" + this.id;
    let designCanvas = document.getElementById(designId);  

    // Initialize the canvas and page elements first 
    // so they are at the top of the dom hierarchy
    let canvas = this.elements["canvas"]; 
    this.initDesignCanvas(canvas); 

    let page = this.elements["page"]; 
    this.createSVGElement(designCanvas, page); 

    for(let elementID in this.elements) {
      if(this.elements.hasOwnProperty(elementID)) {
        let element = this.elements[elementID];
        if(element.type != "canvas" && element.type != "page") {
          this.createSVGElement(designCanvas, element);
        }
      }
    }
  }

  performDesignCanvasMenuAction = (action) => {
    if(action == "save") {
      this.props.saveDesignCanvas(this.id);
      this.state.savedState = 1; 
    }
    else if(action == "trash") {
      this.props.trashDesignCanvas(this.id);
      this.state.savedState = -1; 
    }
    else if(action == "like"){
      // Do something here 
      this.props.getRelativeDesigns(this.originalElements, "like"); 
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
    if(!this.state.valid) {
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

      // TODO: Removed? 
    }

    var designCanvas = document.getElementById("design-canvas-" + this.id); 
    var componentBoundingBox = designCanvas.getBoundingClientRect();
    
    // The menuTrigger is the JSON of the shape that triggered the open
    this.setState({
      designMenu: <DesignMenu 
                    left={componentBoundingBox.x} 
                    top={componentBoundingBox.y} 
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

    if(constraintsMenuShape != undefined) {
      console.log("design canvas");
      console.log(constraintsMenuShape.type); 
    }

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
           id={"canvas-box-" + this.id} style={{height: (this.canvasHeight * scalingFactor) + "px", width: (this.canvasWidth * scalingFactor) + "px"}}> 
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











