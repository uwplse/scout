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

  computeDiversityScores = (designs) => {
    // Compute a pairwise diversity score for the three designs saved by the designer. 
    // Metric should compute an average of the diversity score for all three pairs. 

    // Comparing a single pair of designs
    // For each matched pair of shapes (Find the matching shape of the name property of the element in the element tree)
      // Compute difference across the following dimensions
          // Position - absolute value of distance moved (computed distance between two x,y coordinates) 
                // - Normalize by dividing by screen diagonal length 
          // Size - absolute value of the difference of the two areas (HxW) between the two shapes (Normalize )
                // - Normalize by dividing by the total area of the screen
          // Neighboring elements
              // Find the closest neighboring element in each direction for each element
              // L, T, B, R 
              // If there is no element in a direction (L,T,B,R), the neighboring element in that direction is the canvas
              // For each closest neighboring element along each dimension: 
                  // Neighbor is a different element: 1, Not a different element: 0 
                  // Distance to neighbor in that direction (T,B,L,R)
                      // -- normalize by dividing by width (L,R)  or height (T,B) of canvas 
              // There should be 8 metrics T_changed + T_distance + L_changed + L_distance + B_changed + B_distance + R_changed + R_distance
              // Divide the total score/8 to get the neighboring elements diversity score
          // Representation (only for Alternate groups) - Changed - 1, Not Changed - 0

      // Diversity score for a single pair is a weighted average of Position, Size, Neighboring Elements, Alternate Rep (only for Alternate groups)

    // Sum up the total of diversity scores for the full set of elements. 
    // Then return that as the total score. 
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



