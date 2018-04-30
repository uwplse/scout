class FabricHelpers {
 	static getGroup(left, top, width, height, options={}) {
	    let textValue = (options.text != undefined) ? options.text : options.groupType; 
	    let fontSize = options.fontSize ? options.fontSize : 20; 
	    let leftOffset = options.leftOffset ? options.leftOffset : 20; 
	    let topOffset = options.topOffset ? options.topOffset : 10; 
	    let scaleX = options.scaleX ? options.scaleX : 1; 
	    let scaleY = options.scaleY ? options.scaleY : 1;

	    var rect = new fabric.Rect({
	        width: width - 2,
	        height: height - 2,
	        fill: '#fff', 
	        rx: 2, 
	        ry: 2, 
	        scaleX: scaleX, 
	        scaleY: scaleY, 
	        originX: 'center',
	        originY: 'center', 
	        stroke: options.stroke, 
	        strokeDashArray: [5,5]
	    });
 
	    var text = new fabric.IText(textValue, {
	      fontSize: fontSize, 
	      fontFamily: 'Helvetica Neue', 
	      fontWeight: 400,
	      strokeWidth:0, 
	      letterSpacing: 0.42,
	      letterSpacing: ".03em",
	      fill: options.stroke,
	      scaleX: scaleX, 
	      scaleY: scaleY, 
	      originX: 'center',
	      originY: 'center'
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

	static getInteractiveButton(left, top, width, height, options={}) { 
		var rect = new fabric.Rect({
	        width : width,
	        height : height,
	        fill : '#39a1f4', 
	        rx: 2, 
	        ry: 2, 
	        left: left, 
	        top: top, 
	        selectable: false
	    });

	    let textValue = options.text ? options.text : "BUTTON"; 
	    let fontSize = options.fontSize ? options.fontSize : 20; 
	    var text = new fabric.IText(textValue, {
	      fontSize: fontSize, 
	      fontFamily: 'Helvetica Neue', 
	      fontWeight: 400,
	      strokeWidth:0, 
	      letterSpacing: 0.42,
	      letterSpacing: ".03em",
	      fill: 'white', 
	      left: left + 20, 
	      top: top + 10, 
	      selectable: true,
	      lockScalingY: true, 
	      lockScalingX: true, 
	      lockMovementX: true, 
	      lockMovementY: true
	    });

	    return { button: rect, label: text }; 	
	}

 	static getButton(left, top, width, height, options={}) {
	    let textValue = options.text ? options.text : "BUTTON"; 
	    let fontSize = options.fontSize ? options.fontSize : 20; 
	    let leftOffset = options.leftOffset ? options.leftOffset : 20; 
	    let topOffset = options.topOffset ? options.topOffset : 10; 
	    let scaleX = options.scaleX ? options.scaleX : 1; 
	    let scaleY = options.scaleY ? options.scaleY : 1;

	    var rect = new fabric.Rect({
	        width : width,
	        height : height,
	        fill : '#39a1f4', 
	        rx: 2, 
	        ry: 2, 
	        scaleX: scaleX, 
	        scaleY: scaleY, 
	        originX: 'center',
	        originY: 'center'
	    });
 
	    var text = new fabric.IText(textValue, {
	      fontSize: fontSize, 
	      fontFamily: 'Helvetica Neue', 
	      fontWeight: 400,
	      strokeWidth:0, 
	      letterSpacing: 0.42,
	      letterSpacing: ".03em",
	      fill: 'white',
	      scaleX: scaleX, 
	      scaleY: scaleY, 
	      originX: 'center',
	      originY: 'center'
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
    	let scaleX = options.scaleX ? options.scaleX : 1; 
  		let scaleY = options.scaleY ? options.scaleY : 1;
  	    let textValue = options.text ? options.text : "Text"; 
	    var text = new fabric.Text(textValue, {
	      fontSize: fontSize,
	      left: left,
	      top: top,
	      fontFamily: 'Helvetica Neue',
	      fill: '#000', 
	      lockRotation: true, 
	      hoverCursor: options.cursor, 
	      selectable: options.selectable, 
	      scaleX: scaleX, 
	      scaleY: scaleY
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
	      selectable: true, 
	      lockMovementX: true, 
	      lockMovementY: true, 
	      lockScalingX: true, 
	      lockScalingY: true
	    });

	    return text; 
	}

	static getInteractiveField(left, top, width, height, options={}){
	    var line = new fabric.Line([ left, top+25, left+width, top+25 ],{
	    	fill: 'rgba(0,0,0,.26)',
	        stroke: 'rgba(0,0,0,.26)', 
	        strokeWidth: 2, 
	        selectable: false
	    });

	    let textValue = "Field..."; 
	    let fontSize = options.fontSize ? options.fontSize : 16; 
	    var text = new fabric.IText(textValue, {
	      fontSize: fontSize, 
	      fontFamily: 'Helvetica Neue', 
	      fontWeight: 400,
	      strokeWidth:0, 
	      fill: 'rgba(0,0,0,.26)', 
	      selectable: true, 
	      left: left, 
	      top: top, 
	      lockScalingX: true, 
	      lockScalingY: true, 
	      lockMovementY: true, 
	      lockMovementX: true
	    });

	    return { field: text, line: line };
	}

  	static getField(left, top, width, height, options={}) {
  		let scaleX = options.scaleX ? options.scaleX : 1; 
  		let scaleY = options.scaleY ? options.scaleY : 1;
  		let lineDistance = 25; 
  		let scaledLineDistance = lineDistance * (scaleY);


	    var line = new fabric.Line([ 0, scaledLineDistance, width, scaledLineDistance ],{
	    	fill: 'rgba(0,0,0,.26)',
	        stroke: 'rgba(0,0,0,.26)', 
	        strokeWidth: 2, 
	        scaleX: scaleX, 
	        scaleY: scaleY
	    });

	    let textValue = options.text ? options.text : "Field..."; 
	    let fontSize = options.fontSize ? options.fontSize : 16; 
	    var text = new fabric.IText(textValue, {
	      fontSize: fontSize, 
	      fontFamily: 'Helvetica Neue', 
	      fontWeight: 400,
	      strokeWidth:0, 
	      fill: 'rgba(0,0,0,.26)', 
	      selectable: true, 
	      scaleX: scaleX, 
	      scaleY: scaleY
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