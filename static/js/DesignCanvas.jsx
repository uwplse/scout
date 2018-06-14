// App.jsx
import React from "react";
import CanvasMenu from "./CanvasMenu"; 
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
import label from '../assets/illustrator/label_designs.svg';
import orangeLabel from '../assets/illustrator/orangeLabel_designs.svg';
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
  		activeCanvasMenu: undefined,
      designMenu: undefined, 
      savedState: props.savedState, 
      valid: props.valid, 
      invalidated: props.invalidated, 
      conflicts: props.conflicts, // The conflicting constraints current if there are any
      added: props.added, // The elements that were added since this solution was generated
      removed: props.removed, // The elements that were removed since this solution was generated
      backgroundColor: "#ffffff", 
      designShape: undefined, 
      hovered: false
  	}; 

  	// a callback method to update the constraints canvas when a menu item is selected
  	this.updateConstraintsCanvas = props.updateConstraintsCanvas; 
    this.getConstraintsCanvasShape = props.getConstraintsCanvasShape;

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
      menuShown: prevState.menuShown, 
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

  showConstraintsContextMenu(shape, evt) {
    evt.stopPropagation();
    evt.preventDefault();

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
      activeCanvasMenu: <CanvasMenu left={evt.clientX} top={evt.clientY} menuTrigger={shape} onClick={this.performActionAndCloseMenu.bind(this)} getConstraintsCanvasShape={this.getConstraintsCanvasShape} />,
      menuShown: true
    });
  }

  // hideConstraintsContextMenu
  performActionAndCloseMenu(menuTriggerShape, action, actionType, evt) {
  	// Shape and option clicked on should be the arguments here
  	// The linked shape in the constraints canvass
  	this.updateConstraintsCanvas(menuTriggerShape, action, actionType); 
  	this.hideMenu();
  }

  hideMenu() {
    if(this.state.menuShown) {
      this.setState({
        menuShown: false, 
        activeCanvasMenu: undefined
      });  
    }
  }

  initDesignCanvas(shape) {
    // Intialize the background color
    this.setState({
      designShape: shape,
      backgroundColor: shape.background
    });
  }

  getDesignCanvasWidget(shape, width, height, left, top){
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
            contextMenu={this.showConstraintsContextMenu.bind(this)}/>); 
  }

  createSVGElement(designCanvas, shape) {
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
          this.initDesignCanvas(element);
        }else {
          this.createSVGElement(designCanvas, element);
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

  showMenuAndHighlightConstraints(e){
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
          if(variable == "x" || variable == "y") {
            variable = "location"; 
          }

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
      designMenu: <DesignMenu left={componentBoundingBox.x} top={componentBoundingBox.y} menuAction={this.performDesignCanvasMenuAction.bind(this)} />, 
      hovered: true
    
    });
  }

  closeMenuAndRemoveHighlightConstraints(e) {
    // Trigger constraint highlighting if the solution is not current valid
    if(!this.state.valid) {
      if(this.state.conflicts) {
        for(var i=0; i<this.state.conflicts.length; i++) {
          var conflict = this.state.conflicts[i];
          var variable = conflict.variable; 
          if(variable == "x" || variable == "y") {
            variable = "location"; 
          }

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
   	let menuShown = this.state.menuShown; 
   	let menuPosition = this.state.menuPosition; 
   	let activeCanvasMenu = this.state.activeCanvasMenu; 
    let designMenu = this.state.designMenu; 
    let saved = this.state.savedState == 1; 
    let trashed = this.state.savedState == -1; 
    let valid = this.state.valid; 
    let invalidated = this.state.invalidated; 
    let scalingFactor = this.getScalingFactor();      
    let inMainCanvas = (this.state.savedState == 0 && (!this.state.invalidated)); 
    let childSVGs = this.state.childSVGs; 

    return  (
      <div onMouseEnter={((saved || trashed || invalidated) ? undefined : this.showMenuAndHighlightConstraints.bind(this))} 
           onMouseLeave={((saved || trashed || invalidated) ? undefined : this.closeMenuAndRemoveHighlightConstraints.bind(this))} 
           className={"canvas-container " + " " + ((!this.state.valid && !inMainCanvas) ? "canvas-container-invalid-scaled" : "")} 
           id={"canvas-box-" + this.id} style={{height: (this.canvasHeight * scalingFactor) + "px", width: (this.canvasWidth * scalingFactor) + "px"}}> 
  			<div className={(menuShown ? "" : "hidden")}>
  				{activeCanvasMenu}
  			</div>
        <div>
          {designMenu}
        </div>
        <div id={"design-canvas-" + this.id} 
            className={"design-canvas " + (!this.state.valid ? "canvas-container-invalid " : " ") 
            + (this.state.hovered ? "design-canvas-hovered" : "")}
            onContextMenu={this.showConstraintsContextMenu.bind(this, this.state.designShape)}
            style={{height: "100%", width: "100%", backgroundColor: ""}}>
          {childSVGs}
        </div>
	    </div>); 
  }
}











