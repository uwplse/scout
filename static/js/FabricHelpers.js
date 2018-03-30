class FabricHelpers {
	static getGroup(left, top, width, height, options={}) {
		let opacity = options.opacity != undefined ? options.opacity : 1;
		let selectable = options.selectable != undefined ? options.selectable : true;  
	    var rect = new fabric.Rect({
	    	top: top, 
	    	left: left,
	        width : width,
	        height : height,
	        fill : '#fff', 
	        stroke: options.stroke, 
	        opacity: opacity, 
	        selectable: selectable, 
	        hoverCursor: options.cursor
	    });

	    return rect; 
	} 

 	static getButton(left, top, width, height, options={}) {
	    var rect = new fabric.Rect({
	        width : width,
	        height : height,
	        fill : '#39a1f4', 
	        rx: 2, 
	        ry: 2
	    });

	    let textValue = options.text ? options.text : "BUTTON"; 
	    let fontSize = options.fontSize ? options.fontSize : 14; 
	    var text = new fabric.IText(textValue, {
	      fontSize: fontSize, 
	      fontFamily: 'Helvetica Neue', 
	      fontWeight: 400,
	      strokeWidth:0, 
	      letterSpacing: 0.42,
	      letterSpacing: ".03em",
	      fill: 'white', 
	      left: 20, 
	      top: 10, 
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
  	    let textValue = options.text ? options.text : "Text"; 
	    var text = new fabric.Text(textValue, {
	      fontSize: fontSize,
	      left: left,
	      top: top,
	      fontFamily: 'Helvetica Neue',
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
	      fontFamily: 'Helvetica Neue',
	      fontWeight: 400,
	      fill: 'rgba(0,0,0,.87)', 
	      lockRotation: true, 
	      hoverCursor: options.cursor, 
	      selectable: options.selectable
	    });

	    return text; 
	}

  	static getField(left, top, width, height, options={}) {
	    var line = new fabric.Line([ left-20, top-25, left-20+width, top-25 ],{
	    	fill: 'rgba(0,0,0,.26)',
	        stroke: 'rgba(0,0,0,.26)', 
	        strokeWidth: 1
	    });

	    let textValue = options.text ? options.text : "Placeholder..."; 
	    var text = new fabric.IText(textValue, {
	      fontSize: 16, 
	      fontFamily: 'Helvetica Neue', 
	      fontWeight: 400,
	      strokeWidth:0, 
	      fill: 'rgba(0,0,0,.26)'
	    });

	    var group = new fabric.Group([ text, line ], { 
	        left: left, 
	        top: top,
	        hoverCursor: options.cursor, 
	        selectable: options.selectable
	      });


	    return group;
	}
}

export default FabricHelpers; 