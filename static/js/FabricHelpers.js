class FabricHelpers {
	static getGroup(left, top, width, height, options={}) {
	    var rect = new fabric.Rect({
	    	top: top, 
	    	left: left,
	        width : width,
	        height : height,
	        fill : '#fff', 
	        stroke: 'blue'
	    });

	    return rect; 
	} 

 	static getButton(left, top, width, height, options={}) {
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
	        hoverCursor: options.cursor, 
	        selectable: options.selectable
	      });

	    return group; 
	}

  	static getText(left, top, fontSize, options={}) {
	    var text = new fabric.Text('Text', {
	      fontSize: fontSize,
	      left: left,
	      top: top,
	      fontFamily: 'Georgia',
	      fill: '#000', 
	      lockRotation: true, 
	      hoverCursor: options.cursor, 
	      selectable: options.selectable
	    });

	    return text; 
	}

    static getInteractiveText(left, top, fontSize, options={}) {
	    var text = new fabric.IText('Text', {
	      fontSize: fontSize,
	      left: left,
	      top: top,
	      fontFamily: 'Georgia',
	      fill: '#000', 
	      lockRotation: true, 
	      hoverCursor: options.cursor, 
	      selectable: options.selectable
	    });

	    return text; 
	}

  	static getField(left, top, width, height, options={}) {
	    var rect = new fabric.Rect({
	        width : width,
	        height : height,
	        fill: 'white', 
	        stroke: 'black', 
	        strokeWidth: 1
	    });

	    var text = new fabric.IText('Field', {
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
	        hoverCursor: options.cursor, 
	        selectable: options.selectable
	      });

	    return group;
	}
}

export default FabricHelpers; 