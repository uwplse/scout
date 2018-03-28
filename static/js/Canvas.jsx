// App.jsx
import React from "react";
import FabricHelpers from "./FabricHelpers.js"; 
import CanvasMenu from "./CanvasMenu"; 
import Constants from "./Constants"

export default class Canvas extends React.Component {
  constructor(props) {
  	super(props);
  	this.showConstraintsContextMenu.bind(this); 
    this.showGroupHoveredState.bind(this); 

  	// Shapes to be drawn onto the canvas
  	this.elements = props.elements; 
  	this.id = props.id; 
  	this.elementDict = {}; 

  	this.state = {
  		menuShown: false, 
  		menuPosition: { x: 0, y: 0 }, 
  		activeCanvasMenu: undefined
  	}; 

  	// a callback method to update the constraints canvas when a menu item is selected
  	this.updateConstraintsCanvas = props.updateConstraintsCanvas; 
  } 

  showConstraintsContextMenu(jsonShape,evt) {
  	if(evt.button == 1) {
  		// evt.stopPropagation(); // Prevent it from bubbling to the canvas

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

  showGroupHoveredState(jsonShape,evt) {
    // Do something here to show that the group is being hovered over
    console.log("i am being hovered"); 
  }

  // hideConstraintsContextMenu
  performActionAndCloseMenu(menuTriggerShape, action, evt) {
  	// Shape and option clicked on should be the arguments here
  	// The linked shape in the constraints canvas
  	let constraintsCanvasShape = menuTriggerShape.constraintsCanvasShape; 
  	this.updateConstraintsCanvas(constraintsCanvasShape, menuTriggerShape, action); 
  	this.setState({
  		menuShown: false, 
  		activeCanvasMenu: undefined
  	});
  }

  componentDidMount() {
    this.canvas = new fabric.Canvas('design-canvas-' + this.id); 
    // this.canvas.on("mousedown", this.)

	  // When the component mounts, draw the shapes onto the canvas
  	for(var i=0; i<this.elements.length; i++) {
  		let element = this.elements[i]; 
  		this.elementDict[element.id] = element; 

  		// Scale down the values to fit into the design canvases
  		let x = element.location.x/Constants.designCanvasScalingFactor(); 
  		let y = element.location.y/Constants.designCanvasScalingFactor(); 
  		let width = element.size.width/Constants.designCanvasScalingFactor(); 
  		let height = element.size.height/Constants.designCanvasScalingFactor(); 

  		if(element.type == "button") {
        let fontSize = height/Constants.designCanvasScalingFactor; 
  			let button = FabricHelpers.getButton(x,y,width,height,{
            'cursor': 'hand', 
            'selectable': false, 
            'text': element["name"], 
            'fontSize': fontSize
        }); 
  			button.on("mousedown", this.showConstraintsContextMenu.bind(this,element));
  			element.shape = button; 
  			this.canvas.add(button); 
  		}
  		else if (element.type == "text") {
  			let fontSize = height/Constants.designCanvasScalingFactor; // TODO: Hack. Fix this later
  			let text = FabricHelpers.getText(x,y,fontSize,{
          'cursor': 'hand', 
          'selectable': false, 
          'text': element["name"]
        }); 
  			text.on("mousedown", this.showConstraintsContextMenu.bind(this,element));
  			element.shape = text; 
  			this.canvas.add(text); 
  		}
  		else if (element.type == "field") {
        let fontSize = height/Constants.designCanvasScalingFactor;
  			let field = FabricHelpers.getField(x,y,width,height,{
          'cursor': 'hand', 
          'selectable': false, 
          'text': element["name"], 
          'fontSize': fontSize
        }); 
  			field.on("mousedown", this.showConstraintsContextMenu.bind(this,element));
  			element.shape = field; 
  			this.canvas.add(field); 
  		}
      else if (element.type == "group") {
        let groupPadding = 0; // TODO: make constant for this
        let group = FabricHelpers.getGroup(x-groupPadding,y-groupPadding,width+(groupPadding*2), height+(groupPadding*2), {
          cursor: 'hand', 
          selectable: false, 
          opacity: 0, 
          stroke: undefined
        }); 

        group.on("mouseover", this.showGroupHoveredState.bind(this, element)); 
        group.on("mousedown", this.showConstraintsContextMenu.bind(this, element)); 
        element.shape = group; 
        this.canvas.add(group);
        this.canvas.sendToBack(group); 
      }
  	}
  }

  render () {
   	let menuShown = this.state.menuShown; 
   	let menuPosition = this.state.menuPosition; 
   	let activeCanvasMenu = this.state.activeCanvasMenu; 
    return  (<div className="canvas-container" id={"canvas-box-" + this.id}> 
    			<div style={{left: menuPosition.x, top: menuPosition.y}} className={"canvas-menu-container " + (menuShown ? "" : "hidden")}>
    				{activeCanvasMenu}
    			</div>
	    		<canvas ref={"design-canvas-" + this.id} className="design-canvas" id={"design-canvas-" + this.id} width="187.5px" height="333px">
	            </canvas>
	         </div>); 
  }
}











