// App.jsx
import React from "react";
import FabricHelpers from "./FabricHelpers.js"; 
import CanvasMenu from "./CanvasMenu"; 
import Constants from "./Constants"
import SaveMenu from "./SaveMenu";

export default class DesignCanvas extends React.Component {
  constructor(props) {
  	super(props);
  	this.showConstraintsContextMenu.bind(this); 
    this.saveOrTrashDesignCanvas.bind(this);

  	// Object shapes to be drawn onto the canvas
  	this.elements = props.elements; 
  	this.id = props.id; 
  	this.elementDict = {}; 

    // The original solution shapes from the solver
    // Should remain by later feedback constraints
    this.originalElements = props.originalElements; 

    // Is this a saved design canvas?
    this.saved = props.saved; 

  	this.state = {
  		menuShown: false, 
  		menuPosition: { x: 0, y: 0 }, 
  		activeCanvasMenu: undefined,
      saveMenu: undefined, 
      saveMenuShown: false
  	}; 

  	// a callback method to update the constraints canvas when a menu item is selected
  	this.updateConstraintsCanvas = props.updateConstraintsCanvas; 

    this.canvasWidth = 187.5; 
    this.canvasHeight = 333; 
  } 

  showConstraintsContextMenu(jsonShape,evt) {
  	if(evt.button == 1) {
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
  		let shape = jsonShape.shape; 
	    this.setState({
	      activeCanvasMenu: <CanvasMenu menuTrigger={jsonShape} onClick={this.performActionAndCloseMenu.bind(this)} />,
	      menuShown: true, 
	      menuPosition: {
	      	x: componentBoundingBox.x + shape.left + (shape.width/2), 
	      	y: componentBoundingBox.y + shape.top + (shape.height/2)
	      }
	    });
    }
  }

  // hideConstraintsContextMenu
  performActionAndCloseMenu(menuTriggerShape, action, undoAction, evt) {
  	// Shape and option clicked on should be the arguments here
  	// The linked shape in the constraints canvas
  	let constraintsCanvasShape = menuTriggerShape.constraintsCanvasShape; 
  	this.updateConstraintsCanvas(constraintsCanvasShape, menuTriggerShape, action, undoAction); 
  	this.setState({
  		menuShown: false, 
  		activeCanvasMenu: undefined
  	});
  }

  componentDidMount() {
    this.canvas = new fabric.Canvas('design-canvas-' + this.id); 

	  // When the component mounts, draw the shapes onto the canvas
    let pageFabricShape = null;
  	for(var i=0; i<this.elements.length; i++) {
  		let element = this.elements[i]; 
  		this.elementDict[element.id] = element; 

  		// Scale down the values to fit into the design canvases
      if(element.type == "page") {
        let x = 0; 
        let y = 0; 
        let width = this.canvasWidth; 
        let height = this.canvasHeight; 
        
        // Make a white rectangle of this size to serve as the background layer
        let pageGroup = FabricHelpers.getGroup(x,y,width,height, {
          cursor: 'hand', 
          selectable: false, 
          opacity: 0, 
          stroke: undefined
        }); 

        pageGroup.on("mousedown", this.showConstraintsContextMenu.bind(this, element)); 
        element.shape = pageGroup; 
        this.canvas.add(pageGroup);
        pageFabricShape = pageGroup; 
      } else {
        let x = element.location.x/Constants.designCanvasScalingFactor(); 
        let y = element.location.y/Constants.designCanvasScalingFactor(); 

        if(element.type == "button") {
          // TODO: Figure out how to make a factor of the label size

          let button = FabricHelpers.getButton(x,y,element.size.width,element.size.height,{
              'cursor': 'hand', 
              'selectable': false, 
              'text': element["label"], 
              'scaleX': 1/Constants.designCanvasScalingFactor(), 
              'scaleY': 1/Constants.designCanvasScalingFactor()
          }); 
          button.on("mousedown", this.showConstraintsContextMenu.bind(this,element));
          element.shape = button; 
          this.canvas.add(button); 
        }
        else if (element.type == "text") {
          let text = FabricHelpers.getText(x,y,element.size.height,{
            'cursor': 'hand', 
            'selectable': false, 
            'text': element["label"], 
            'scaleX': 1/Constants.designCanvasScalingFactor(), 
            'scaleY': 1/Constants.designCanvasScalingFactor()
          }); 
          text.on("mousedown", this.showConstraintsContextMenu.bind(this,element));
          element.shape = text; 
          this.canvas.add(text); 
        }
        else if (element.type == "field") {
          let field = FabricHelpers.getField(x,y,element.size.width,element.size.height,{
            'cursor': 'hand', 
            'selectable': false, 
            'text': element["label"],
            'scaleX': 1/Constants.designCanvasScalingFactor(), 
            'scaleY': 1/Constants.designCanvasScalingFactor()
          }); 
          field.on("mousedown", this.showConstraintsContextMenu.bind(this,element));
          element.shape = field; 
          this.canvas.add(field); 
        }
        else if (element.type == "group") {
          let groupPadding = 0; // TODO: make constant for this
          let group = FabricHelpers.getGroup(x-groupPadding,y-groupPadding,element.size.width+(groupPadding*2), element.size.height+(groupPadding*2), {
            cursor: 'hand', 
            selectable: false, 
            opacity: 0, 
            stroke: undefined
          }); 

          group.on("mousedown", this.showConstraintsContextMenu.bind(this, element)); 
          element.shape = group; 
          this.canvas.add(group);
          this.canvas.sendToBack(group); 
        }
      }
  	}

    // Make sure to send the page fabric shape to the back layer
    this.canvas.sendToBack(pageFabricShape); 
  }

  saveOrTrashDesignCanvas(action) {
    if(action == "save") {
      this.props.saveDesignCanvas(this.id);
    }
    else {
      this.props.trashDesignCanvas(this.id);
    }
  }

  onRightClick(e){
    // show a menu 
    e.preventDefault();

    // Check for the status of menuShown to see if we need to close out another menu before opening this one
    if(this.state.saveMenuShown) {
      this.setState({
        saveMenu: undefined, 
        saveMenuShown: false
      }); 
    }

    // The menuTrigger is the JSON of the shape that triggered the open
    this.setState({
      saveMenu: <SaveMenu left={e.clientX} top={e.clientY} menuAction={this.saveOrTrashDesignCanvas.bind(this)} />,
      saveMenuShown: true
    });
  }

  render () {
   	let menuShown = this.state.menuShown; 
   	let menuPosition = this.state.menuPosition; 
   	let activeCanvasMenu = this.state.activeCanvasMenu; 
    let contextMenu = this.onRightClick;
    let saveMenuShown = this.state.saveMenuShown; 
    let saveMenu = this.state.saveMenu; 
    return  (
      <div onContextMenu={(this.saved ? undefined : contextMenu.bind(this))} className="canvas-container" id={"canvas-box-" + this.id}> 
  			<div style={{left: menuPosition.x, top: menuPosition.y}} className={"canvas-menu-container " + (menuShown ? "" : "hidden")}>
  				{activeCanvasMenu}
  			</div>
        <div> 
          {saveMenu}
        </div>
	    	<canvas ref={"design-canvas-" + this.id} className="design-canvas" id={"design-canvas-" + this.id} width={this.canvasWidth} height={this.canvasHeight}>
	     </canvas>
	    </div>); 
  }
}











