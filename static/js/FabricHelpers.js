class FabricHelpers {
 	static getButton(left, top, width, height, cursor, selectable=true) {
	    var rect = new fabric.Rect({
	        width : width,
	        height : height,
	        fill : '#44ACB1'
	    });

	    var text = new fabric.IText('Button', {
	      fontSize: 20, 
	      fontFamily: 'Georgia', 
	      strokeWidth:0, 
	      fill: 'white', 
	      left: 25, 
	      top: 10
	    });

	    var group = new fabric.Group([ rect, text ], { 
	        left: left, 
	        top: top, 
	        selectable: false, 
	        hoverCursor: cursor, 
	        selectable: selectable
	      });

	    return group; 
	}

  	static getText(left, top, cursor, selectable=true) {
	    var text = new fabric.Text('Text', {
	      fontSize: 60,
	      left: left,
	      top: top,
	      fontFamily: 'Georgia',
	      fill: '#000', 
	      lockRotation: true, 
	      hoverCursor: cursor, 
	      selectable: selectable
	    });

	    return text; 
	}

    static getInteractiveText(left, top, cursor, selectable=true) {
	    var text = new fabric.IText('Text', {
	      fontSize: 60,
	      left: left,
	      top: top,
	      fontFamily: 'Georgia',
	      fill: '#000', 
	      lockRotation: true, 
	      hoverCursor: cursor, 
	      selectable: selectable
	    });

	    return text; 
	}

  	static getField(left, top, width, height, cursor, selectable=true) {
	    var rect = new fabric.Rect({
	        width : width,
	        height : height,
	        fill: 'white', 
	        stroke: 'black', 
	        strokeWidth: 1
	    });

	    var text = new fabric.Text('Field', {
	      fontSize: 20, 
	      fontFamily: 'Georgia', 
	      strokeWidth:0, 
	      fill: 'black', 
	      top: 10, 
	      left: 25
	    });

	    var group = new fabric.Group([ rect, text ], { 
	        left: left, 
	        top: top,
	        hoverCursor: cursor, 
	        selectable: selectable
	      });

	    return group;
	}
}

export default FabricHelpers; 