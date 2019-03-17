import domtoimage from 'dom-to-image'; 
import JSZip from 'jszip';
import Snap from 'snapsvg-cjs';
import ConstraintActions from "./ConstraintActions"; 

export default class Exporter  {
  constructor(svgWidgets) {
    this.zipFile = new JSZip();
    this.exportPromises = []; 
    this.svgWidgets = svgWidgets; 
  }

  convertDesignToPaper = (design) => {
    var s = Snap(ConstraintActions.canvas_width, ConstraintActions.canvas_height);
    s.attr('fill', 'white'); 
    var bgRect = s.rect(); 
    bgRect.attr('width', ConstraintActions.canvas_width); 
    bgRect.attr('height', ConstraintActions.canvas_height); 
    bgRect.attr('fill', 'white'); 
    s.append(bgRect); 

    this.drawDesignNode(s, design.elements); 
    return s; 
  }

  replaceWidthAndHeight = (svgSource, width, height) => {
    let newSvg = svgSource; 
    let newHeight = "height=\"" + height + "\"";
    let newWidth = "width=\"" + width + "\"";
    newSvg = svgSource.replace(/height="[0-9]+"/, newHeight);
    newSvg = newSvg.replace(/width="[0-9]+"/, newWidth);  
    return newSvg; 
  }

  getSVGForNode = (node) => {
    let id = node.id; 
    if(node.type == "group" && node.alternate) {
      id = node.alternate; 
    }

    let svgElement = this.svgWidgets.filter(svgNode => svgNode.id == id); 
    if(svgElement && svgElement.length) {
      svgElement = svgElement[0]; 
      return svgElement.svgData; 
    }

    return ""; 
  }

  drawDesignNode = (s, node) => {
    let svg = this.getSVGForNode(node); 
    let svgNode = s; 
    if(svg.length) {
      let transform = "T" + node.x + "," + node.y; 
      svg = this.replaceWidthAndHeight(svg, node.width, node.height); 
      let svgParsed = Snap.parse(svg); 
      var svgGroup = svgNode.g();
      svgGroup.append(svgParsed); 
      svgGroup.transform(transform); 
      svgGroup.attr('width', node.width); 
      svgGroup.attr('height', node.height); 
      svgNode.append(svgGroup); 
    }
    else if(node.type == "group") {
      let svgGroup = svgNode.g(); 
      svgNode.append(svgGroup); 
      svgNode = svgGroup;
    }

    if(!node.alternate) {
      if(node.children) {
        for(let i=0; i<node.children.length; i++) {
          this.drawDesignNode(svgNode, node.children[i]); 
        }
      }
    }
  }

  addDesignToExports = (design, designNode) => {
  	let designID = design.id;

    let svgDesign = this.convertDesignToPaper(design); 
    let svgString = svgDesign.toString();
    this.zipFile.file(designID + ".svg", svgString); 

    let hierarchy = design.elements; 
    let designJSON = JSON.stringify(hierarchy); 
    this.zipFile.file(designID + ".json", designJSON); 
  }
  
  exportDesigns = () => {
    this.zipFile.generateAsync({type:"blob"})
    .then(function(content) {
        // see FileSaver.js
        saveAs(content, "exported_from_scout.zip");
    });
  }
}



