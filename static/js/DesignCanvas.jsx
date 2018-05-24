// App.jsx
import React from "react";
import CanvasMenu from "./CanvasMenu"; 
import Constants from "./Constants";
import DesignMenu from "./DesignMenu";
import DesignCanvasSVGWidget from "./DesignCanvasSVGWidget";
import field from '../assets/illustrator/field.svg';
import search from '../assets/illustrator/search.svg';
import image from '../assets/illustrator/image.svg'
import placeholder from '../assets/illustrator/placeholder.svg'
import filledButton from '../assets/illustrator/filledButton.svg';
import label from '../assets/illustrator/label.svg';
import group from '../assets/illustrator/groupDesign.svg';

export default class DesignCanvas extends React.Component {
  static svgElements(controlType) {
    let svgElements = {
      'field': field, 
      'search': search, 
      'button': filledButton, 
      'label': label, 
      'group': group, 
      'placeholder': placeholder, 
      'image': image
      /* Add others here */
    }; 
    return svgElements[controlType]; 
  };

  constructor(props) {
  	super(props);
  	this.showConstraintsContextMenu.bind(this); 
    this.performDesignCanvasMenuAction.bind(this);

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
  		menuShown: false, 
  		menuPosition: { x: 0, y: 0 }, 
  		activeCanvasMenu: undefined,
      designMenu: undefined, 
      savedState: props.savedState, 
      valid: props.valid, 
      invalidated: props.invalidated, 
      conflicts: props.conflicts // The conflicting constraints current if there are any
  	}; 

  	// a callback method to update the constraints canvas when a menu item is selected
  	this.updateConstraintsCanvas = props.updateConstraintsCanvas; 
    this.getConstraintsCanvasShape = props.getConstraintsCanvasShape;

    // Callback method in the parent PageContainer to get a widget and widget feedback item to be highlighted in the ConstraintsCanvas
    this.highlightWidgetFeedback = props.highlightWidgetFeedback; 

    this.canvasWidth = 375; 
    this.canvasHeight = 667; 

    // Original scaling factor
    this.scalingFactor = this.getScalingFactor();
  }

  static getDerivedStateFromProps(nextProps, prevState) {
    return {
      menuShown: prevState.menuShown, 
      menuPosition: prevState.menuPosition, 
      activeCanvasMenu: prevState.activeCanvasMenu, 
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
 
  getScalingFactor() {
    if(this.state.savedState == 1) {
      return 0.10; 
    } 
    
    if(this.state.savedState == -1) {
      return 0.10; 
    }

    if(this.state.invalidated) {
      return 0.10; 
    }

    return 0.5;
  }

  showConstraintsContextMenu(shape,evt) {
    evt.stopPropagation();

		// Check for the status of menuShown to see if we need to close out another menu before opening this one
		if(this.state.menuShown) {
			this.setState({
				activeCanvasMenu: undefined, 
				menuShown: false
			}); 
		}

		// Show the context menu. 
    var designCanvas = document.getElementById("design-canvas-" + this.id); 
		let componentBoundingBox = designCanvas.getBoundingClientRect();

    this.setState({
      activeCanvasMenu: <CanvasMenu menuTrigger={shape} onClick={this.performActionAndCloseMenu.bind(this)} getConstraintsCanvasShape={this.getConstraintsCanvasShape} />,
      menuShown: true, 
      menuPosition: {
      	x: evt.clientX, 
      	y: evt.clientY
      }
    });
  }

  showHoverIndicator(element, evt) {
    evt.stopPropagation();
    element.classList.add("design-canvas-hovered"); 
  }

  hideHoverIndicator(element, evt) {
    element.classList.remove("design-canvas-hovered"); 
  }

  // hideConstraintsContextMenu
  performActionAndCloseMenu(menuTriggerShape, action, actionType, evt) {
  	// Shape and option clicked on should be the arguments here
  	// The linked shape in the constraints canvass
  	this.updateConstraintsCanvas(menuTriggerShape, action, actionType); 
  	this.hideMenu();
  }

  hideMenu() {
    this.setState({
      menuShown: false, 
      activeCanvasMenu: undefined
    });  
  }

  initDesignCanvas(designCanvas, shape) {
    let inMainCanvas = (this.state.savedState == 0 && (!this.state.invalidated)); 

    // Dont' bind event handlers to canvases that are in a saved or trashed state. 
    if(inMainCanvas) {
      designCanvas.addEventListener("mousedown", this.showConstraintsContextMenu.bind(this, shape)); 

      designCanvas.addEventListener("mouseover", this.showHoverIndicator.bind(this, designCanvas)); 
      designCanvas.addEventListener("mouseout", this.hideHoverIndicator.bind(this, designCanvas)); 
    }

    // Initialize the background color
    designCanvas.style.backgroundColor = shape.background; 
  }

  getDesignCanvasWidget(shape, width, height, left, top){
    let shapeId = shape.name;
    let source = DesignCanvas.svgElements(shape.controlType);
    let inMainCanvas = (this.state.savedState == 0 && (!this.state.invalidated)); 
    if(inMainCanvas) {
      return (<DesignCanvasSVGWidget 
              key={shapeId} 
              shape={shape} 
              id={shapeId} 
              source={source}
              width={width}
              height={height}
              left={left}
              top={top}
              onMouseEnter={this.showHoverIndicator.bind(this)}
              onMouseDown={this.showConstraintsContextMenu.bind(this)}
              onMouseOut={this.hideHoverIndicator.bind(this)} />);      
    }
    else {
      return (<DesignCanvasSVGWidget 
              key={shapeId} 
              shape={shape} 
              id={shapeId} 
              source={source}
              width={width}
              height={height} 
              left={left}
              top={top} />);
    }

  }

  drawSVGElement(designCanvas, shape) {
    // Get the control SVG element from the control type
    let controlType = shape.controlType;
    let svg = DesignCanvas.svgElements(controlType); 
    if(svg != undefined) {
      let padding = 0; 
      if(controlType == "group" || controlType == "labelGroup") {
        padding = 5;
      }

      let computedHeight = (shape.size.height * this.scalingFactor + (padding * 2));
      let computedWidth = (shape.size.width * this.scalingFactor + (padding * 2)); 
      let computedLeft = ((shape.location.x * this.scalingFactor) - padding); 
      let computedTop = ((shape.location.y * this.scalingFactor) - padding);
     
      let designCanvasWidget = this.getDesignCanvasWidget(shape, computedWidth, computedHeight, computedLeft, computedTop);
      this.state.childSVGs.push(designCanvasWidget);
      this.setState({
        childSVGs: this.state.childSVGs
      }); 
    }
  }

  drawDesign() {
    // When the component mounts, draw the shapes onto the canvas
    let designId = "design-canvas-" + this.id;
    let designCanvas = document.getElementById(designId);  

    for(let elementID in this.elements) {
      if(this.elements.hasOwnProperty(elementID)) {
        let element = this.elements[elementID];
        if(element.type == "canvas") {
          this.initDesignCanvas(designCanvas, element);
        }else {
          this.drawSVGElement(designCanvas, element);
        }
      }
    }
  }

  performDesignCanvasMenuAction(action) {
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

  onMouseEnter(e){
    // Check for the status of menuShown to see if we need to close out another menu before opening this one
    if(this.state.designMenu != undefined) {
      this.setState({
        designMenu: undefined
      }); 
    }

    // Trigger constraint highlighting if the solution is not current valid
    if(!this.state.valid && this.state.conflicts) {
      for(var i=0; i<this.state.conflicts.length; i++) {
        var conflict = this.state.conflicts[i];
        var variable = conflict.variable; 
        if(variable == "x" || variable == "y") {
          variable = "location"; 
        }

        this.highlightWidgetFeedback(conflict.shape_id, variable, true); 
      }
    }

    var designCanvas = document.getElementById("design-canvas-" + this.id); 
    var componentBoundingBox = designCanvas.getBoundingClientRect();
    
    // The menuTrigger is the JSON of the shape that triggered the open
    this.setState({
      designMenu: <DesignMenu left={componentBoundingBox.x} top={componentBoundingBox.y} menuAction={this.performDesignCanvasMenuAction.bind(this)} />
    });
  }

  onMouseOut(e) {
    // Trigger constraint highlighting if the solution is not current valid
    if(!this.state.valid && this.state.conflicts) {
      for(var i=0; i<this.state.conflicts.length; i++) {
        var conflict = this.state.conflicts[i];
        var variable = conflict.variable; 
        if(variable == "x" || variable == "y") {
          variable = "location"; 
        }

        this.highlightWidgetFeedback(conflict.shape_id, variable, false); 
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
  }

  render () {
   	let menuShown = this.state.menuShown; 
   	let menuPosition = this.state.menuPosition; 
   	let activeCanvasMenu = this.state.activeCanvasMenu; 
    let showMenuAndHighlightConstraints = this.onMouseEnter;
    let closeMenuAndRemoveHighlightConstraints = this.onMouseOut; 
    let designMenu = this.state.designMenu; 
    let saved = this.state.savedState == 1; 
    let trashed = this.state.savedState == -1; 
    let valid = this.state.valid; 
    let invalidated = this.state.invalidated; 
    let scalingFactor = this.getScalingFactor();      
    let inMainCanvas = (this.state.savedState == 0 && (!this.state.invalidated)); 
    let childSVGs = this.state.childSVGs; 

    return  (
      <div onMouseEnter={((saved || trashed || invalidated) ? undefined : showMenuAndHighlightConstraints.bind(this))} 
           onMouseOut={((saved || trashed || invalidated) ? undefined : closeMenuAndRemoveHighlightConstraints.bind(this))} 
           className={"canvas-container " + " " + ((!this.state.valid && !inMainCanvas) ? "canvas-container-invalid-scaled" : "")} 
           id={"canvas-box-" + this.id} style={{height: (this.canvasHeight * scalingFactor) + "px", width: (this.canvasWidth * scalingFactor) + "px"}}> 
  			<div style={{left: menuPosition.x, top: menuPosition.y}} className={"canvas-feedback-menu-container " + (menuShown ? "" : "hidden")}>
  				{activeCanvasMenu}
  			</div>
        <div>
          {designMenu}
        </div>
        <div id={"design-canvas-" + this.id} className={"design-canvas " + (!this.state.valid ? "canvas-container-invalid" : "")} style={{height: "100%", width: "100%"}}>
          {childSVGs}
        </div>
	    </div>); 
  }
}











