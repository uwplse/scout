// App.jsx
import React from "react";
import FabricHelpers from "./FabricHelpers.js"; 
import CanvasMenu from "./CanvasMenu"; 
import Constants from "./Constants";
import DesignMenu from "./DesignMenu";

export default class DesignCanvas extends React.Component {
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
  		menuShown: false, 
  		menuPosition: { x: 0, y: 0 }, 
  		activeCanvasMenu: undefined,
      designMenu: undefined, 
      savedState: props.savedState, 
      valid: props.valid, 
      invalidated: props.invalidated
  	}; 

  	// a callback method to update the constraints canvas when a menu item is selected
  	this.updateConstraintsCanvas = props.updateConstraintsCanvas; 
    this.getConstraintsCanvasShape = props.getConstraintsCanvasShape;

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
      invalidated: nextProps.invalidated
    }    
  }

  componentDidMount() {
    this.redrawCanvas(); 

    if(!this.state.valid) {
      this.invalidateCanvas();
    }
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

  showConstraintsContextMenu(element,evt) {
		// Check for the status of menuShown to see if we need to close out another menu before opening this one
		if(this.state.menuShown) {
			this.setState({
				activeCanvasMenu: undefined, 
				menuShown: false
			}); 
		}

		// Show the context menu. 
		let componentBoundingBox = this.refs["design-canvas-" + this.id].getBoundingClientRect();

		// The menuTrigger is the JSON of the shape that triggered the open
		let shape = element.shape; 
    let scaledWidth = shape.width * this.scalingFactor; 
    let scaledHeight = shape.height * this.scalingFactor; 

    this.setState({
      activeCanvasMenu: <CanvasMenu menuTrigger={element} onClick={this.performActionAndCloseMenu.bind(this)} getConstraintsCanvasShape={this.getConstraintsCanvasShape} />,
      menuShown: true, 
      menuPosition: {
      	x: evt.e.clientX, 
      	y: evt.e.clientY
      }
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
    this.setState({
      menuShown: false, 
      activeCanvasMenu: undefined
    });  
  }

  rerenderCanvas() {
    this.canvas.renderAll(); 

    if(!this.state.valid) {
      this.invalidateCanvas(); 
    }
  }

  showHoverIndicator(element, shape) {
    shape.set("stroke", "#000000"); 
    shape.set("strokeWidth", 1); 
    shape.set("strokeDashArray", [5,5]);
    this.rerenderCanvas(); 
  }

  hideHoverIndicator(element, shape) {
    shape.set("stroke", undefined); 
    shape.set("strokeDashArray", undefined);
    shape.set("strokeWidth", undefined);
    this.rerenderCanvas(); 
  }

  redrawCanvas() {
    if(!this.canvas) {
      this.canvas = new fabric.Canvas('design-canvas-' + this.id);       
    }

    this.canvas.clear(); 
    this.drawCanvas();
  }

  drawCanvas() {
    console.log("drawing the canvas");
    let inMainCanvas = (this.state.savedState == 0 && (!this.state.invalidated)); 

    // When the component mounts, draw the shapes onto the canvas
    let pageFabricShape = null;
    for(var i=0; i<this.elements.length; i++) {
      let element = this.elements[i]; 
      this.elementDict[element.id] = element; 

      // Scale down the values to fit into the design canvases
      if(element.type == "canvas") {
        let x = 0; 
        let y = 0; 
        let width = this.canvasWidth; 
        let height = this.canvasHeight; 
        
        // Make a white rectangle of this size to serve as the background layer
        let pageGroup = FabricHelpers.getDesignGroup(x,y,width-2,height-2, {
          cursor: 'hand', 
          selectable: false, 
          padding: 0
        }); 

        // Dont' bind event handlers to canvases that are in a saved or trashed state. 
        if(inMainCanvas) {
          pageGroup.on("mousedown", this.showConstraintsContextMenu.bind(this, element)); 

          pageGroup.on("mouseover", this.showHoverIndicator.bind(this, element, pageGroup)); 
          pageGroup.on("mouseout", this.hideHoverIndicator.bind(this, element, pageGroup)); 
        }

        // pageGroup.on("mouseout", this.hideMenu.bind(this));
        element.shape = pageGroup; 
        this.canvas.add(pageGroup);
        pageFabricShape = pageGroup; 
      } else {
        let x = element.location.x; 
        let y = element.location.y; 
        if(element.type == "button") {
          let button = FabricHelpers.getButton(x,y,element.size.width,element.size.height,{
              'cursor': 'hand', 
              'selectable': false, 
              'text': element["label"]
          }); 

          if(inMainCanvas) {
            button.on("mousedown", this.showConstraintsContextMenu.bind(this,element));

            let rect = button.getObjects()[0];
            button.on("mouseover", this.showHoverIndicator.bind(this, element, rect)); 
            button.on("mouseout", this.hideHoverIndicator.bind(this, element, rect)); 
          }

          element.shape = button; 
          this.canvas.add(button); 
        }
        else if (element.type == "text") {
          let text = FabricHelpers.getText(x,y,element.size.height,{
            'cursor': 'hand', 
            'selectable': false, 
            'text': element["label"]
          }); 

          if(inMainCanvas) {
            text.on("mousedown", this.showConstraintsContextMenu.bind(this,element));
            text.on("mouseover", this.showHoverIndicator.bind(this, element, text)); 
            text.on("mouseout", this.hideHoverIndicator.bind(this, element, text));
          }

          element.shape = text; 
          this.canvas.add(text); 
        }
        else if (element.type == "field") {
          let field = FabricHelpers.getField(x,y,element.size.width,element.size.height,{
            'cursor': 'hand', 
            'selectable': false, 
            'text': element["label"]
          }); 

          if(inMainCanvas) {
            field.on("mousedown", this.showConstraintsContextMenu.bind(this,element));

            let text = field.getObjects()[0]; 
            field.on("mouseover", this.showHoverIndicator.bind(this, element, text)); 
            field.on("mouseout", this.hideHoverIndicator.bind(this, element, text)); 
          }

          element.shape = field; 
          this.canvas.add(field); 
        }
        else if (element.type == "group") {
          let groupPadding = 0; // TODO: make constant for this
          let group = FabricHelpers.getDesignGroup(x-groupPadding,y-groupPadding,element.size.width+(groupPadding*2), element.size.height+(groupPadding*2), {
            cursor: 'hand', 
            selectable: false, 
            padding: 20,  
          }); 

          if(inMainCanvas) {
            group.on("mousedown", this.showConstraintsContextMenu.bind(this, element)); 
            group.on("mouseover", this.showHoverIndicator.bind(this, element, group)); 
            group.on("mouseout", this.hideHoverIndicator.bind(this, element, group));            
          }

          element.shape = group; 
          this.canvas.add(group);
          this.canvas.sendToBack(group); 
        }
      }
    }

    // Make sure to send the page fabric shape to the back layer
    this.canvas.sendToBack(pageFabricShape); 

    // Rescale the canvas to the given scaling factor
    this.rescaleCanvas();   
  }
 
  invalidateCanvas() {     
    var color1 = "#f5c6cb";
    var numberOfStripes = 100;     
    var drawingContext = this.canvas.getContext(); 
    var thickness = this.canvasWidth / numberOfStripes;
    for (var i=0;i < numberOfStripes*2;i++){
      if((i % 2) == 0) {
        drawingContext.beginPath();
        drawingContext.strokeStyle = color1;
        drawingContext.lineWidth = 1;
        drawingContext.lineCap = 'round';
         
        drawingContext.moveTo(i*thickness + thickness/2 - this.canvasWidth,0);
        drawingContext.lineTo(0 + i*thickness+thickness/2,this.canvasWidth);
        drawingContext.stroke();          
      }
    }
  }

  rescaleCanvas() {
    let scaling = this.scalingFactor;
    let canvasHeight = this.canvasHeight; 
    let canvasWidth = this.canvasWidth; 
    this.canvas.setHeight(canvasHeight * scaling);
    this.canvas.setWidth(canvasWidth * scaling); 
    var obj = this.canvas.getObjects(); 
    for (var i=0; i<obj.length; i++){
      var left = obj[i].get('left');
      var top = obj[i].get('top');

      obj[i].set('left', left * scaling);
      obj[i].set('top', top * scaling);
      obj[i].set('scaleX', scaling);
      obj[i].set('scaleY', scaling);

      obj[i].setCoords();
    }

    this.canvas.renderAll(); 
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

    let componentBoundingBox = this.refs["design-canvas-" + this.id].getBoundingClientRect();
    
    // The menuTrigger is the JSON of the shape that triggered the open
    this.setState({
      designMenu: <DesignMenu left={componentBoundingBox.x} top={componentBoundingBox.y} menuAction={this.performDesignCanvasMenuAction.bind(this)} />
    });
  }

  onMouseOut(e) {
    // Close the menu if it is open 
    let componentBoundingBox = this.refs["design-canvas-" + this.id].getBoundingClientRect();
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
    let openMenu = this.onMouseEnter;
    let closeMenu = this.onMouseOut; 
    let designMenu = this.state.designMenu; 
    let saved = this.state.savedState == 1; 
    let trashed = this.state.savedState == -1; 
    let invalidated = this.state.invalidated; 

    if(this.canvas) {
      this.rerenderCanvas();       
    }

    return  (
      <div onMouseEnter={((saved || trashed || invalidated) ? undefined : openMenu.bind(this))} 
           onMouseOut={((saved || trashed || invalidated) ? undefined : closeMenu.bind(this))} 
           className="canvas-container" id={"canvas-box-" + this.id}> 
  			<div style={{left: menuPosition.x, top: menuPosition.y}} className={"canvas-feedback-menu-container " + (menuShown ? "" : "hidden")}>
  				{activeCanvasMenu}
  			</div>
        <div>
          {designMenu}
        </div>
	    	<canvas ref={"design-canvas-" + this.id} className="design-canvas" id={"design-canvas-" + this.id} width={this.canvasWidth} height={this.canvasHeight}>
	     </canvas>
	    </div>); 
  }
}











