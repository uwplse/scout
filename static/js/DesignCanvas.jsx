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

    // Is this a saved design canvas?
    this.saved = props.saved; 

  	this.state = {
  		menuShown: false, 
  		menuPosition: { x: 0, y: 0 }, 
  		activeCanvasMenu: undefined,
      designMenu: undefined
  	}; 

  	// a callback method to update the constraints canvas when a menu item is selected
  	this.updateConstraintsCanvas = props.updateConstraintsCanvas; 

    this.canvasWidth = 375; 
    this.canvasHeight = 667; 
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
        let x = element.location.x; 
        let y = element.location.y; 
        if(element.type == "button") {
          let button = FabricHelpers.getButton(x,y,element.size.width,element.size.height,{
              'cursor': 'hand', 
              'selectable': false, 
              'text': element["label"]
          }); 
          button.on("mousedown", this.showConstraintsContextMenu.bind(this,element));
          element.shape = button; 
          this.canvas.add(button); 
        }
        else if (element.type == "text") {
          let text = FabricHelpers.getText(x,y,element.size.height,{
            'cursor': 'hand', 
            'selectable': false, 
            'text': element["label"]
          }); 
          text.on("mousedown", this.showConstraintsContextMenu.bind(this,element));
          element.shape = text; 
          this.canvas.add(text); 
        }
        else if (element.type == "field") {
          let field = FabricHelpers.getField(x,y,element.size.width,element.size.height,{
            'cursor': 'hand', 
            'selectable': false, 
            'text': element["label"]
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

    let scaling = Constants.designCanvasScalingFactor(); 
    this.canvas.setHeight(this.canvas.getHeight() * scaling);
    this.canvas.setWidth(this.canvas.getWidth() * scaling); 
    var obj = this.canvas.getObjects(); 
    for (var i=0; i<obj.length; i++){
      // let scaleHeight = obj[i].get('height'); 
      // let scaleWidth = obj[i].get('width'); 
      var left = obj[i].get('left');
      var top = obj[i].get('top');

      // obj[i].set('width', scaleWidth * scaling);
      // obj[i].set('height', scaleHeight * scaling);
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
    }
    else if(action == "trash") {
      this.props.trashDesignCanvas(this.id);
    }
    else if(action == "like"){
      // Do something here 
      this.props.getRelativeDesigns(this.originalElements, "like"); 
    }

    this.setState({
      designMenu: undefined
    });
  }

  onRightClick(e){
    // show a menu 
    e.preventDefault();

    // Check for the status of menuShown to see if we need to close out another menu before opening this one
    if(this.state.designMenu != undefined) {
      this.setState({
        designMenu: undefined
      }); 
    }

    // The menuTrigger is the JSON of the shape that triggered the open
    this.setState({
      designMenu: <DesignMenu left={e.pageX} top={e.pageY} menuAction={this.performDesignCanvasMenuAction.bind(this)} />
    });
  }

  render () {
   	let menuShown = this.state.menuShown; 
   	let menuPosition = this.state.menuPosition; 
   	let activeCanvasMenu = this.state.activeCanvasMenu; 
    let contextMenu = this.onRightClick;
    let designMenu = this.state.designMenu; 
    return  (
      <div onContextMenu={(this.saved ? undefined : contextMenu.bind(this))} className="canvas-container" id={"canvas-box-" + this.id}> 
  			<div style={{left: menuPosition.x, top: menuPosition.y}} className={"canvas-menu-container " + (menuShown ? "" : "hidden")}>
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











