import domtoimage from 'dom-to-image'; 
import JSZip from 'jszip';
import Snap from 'snapsvg-cjs';
import ConstraintActions from "./ConstraintActions"; 

export default class Exporter  {
  constructor(svgWidgets) {
    this.zipFile = new JSZip();
    this.svgWidgets = svgWidgets; 
  }

  convertDesignToPaper = (design) => {
    var s = Snap(ConstraintActions.canvas_width, ConstraintActions.canvas_height);
    s.attr('fill', 'white'); 
    var bgRect = s.rect(); 
    bgRect.attr('width', ConstraintActions.canvas_width); 
    bgRect.attr('height', ConstraintActions.canvas_height); 
    s.append(bgRect); 

    this.drawDesignNode(s, design.elements); 
    return s; 
  }

  getScaledSize = (svgSource, width, height) => {
    let newSvg = svgSource; 
    let viewBox = svgSource.match(/viewBox="([^"]+)"/); 
    let viewBoxSplit = viewBox[1].split(" "); 
    let vbWidth = parseInt(viewBoxSplit[2]); 
    let vbHeight = parseInt(viewBoxSplit[3]); 

    let scaledX = width/vbWidth; 
    let scaledY = height/vbHeight; 

    return { scaleX: scaledX, scaleY: scaledY };  
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
      let scale = this.getScaledSize(svg, node.width, node.height); 

      let transform2 = "translate(" + node.x + "," + node.y + ") scale(" + scale.scaleX + "," + scale.scaleY + ")"; 
      let svgParsed = Snap.parse(svg);
      var svgGroup = svgNode.g();
      if(svgParsed.node && svgParsed.node.children) {
        for(let i=0; i<svgParsed.node.children.length; i++) {
          svgGroup.append(svgParsed.node.children[i]); 
        }
      }
      svgGroup.transform(transform2); 
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
      /// Only leaf node shapes 
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
                // shape.alternate  = true 

      // Diversity score for a single pair is a weighted average of Position, Size, Neighboring Elements, Alternate Rep (only for Alternate groups)

    // Sum up the total of diversity scores for the full set of elements. 
    // Then return that as the total score. 
  }

  exportHierarchy = (solutions, hierarchyID) => {
    let solutionsJSON = JSON.stringify(solutions); 
    this.zipFile.file(hierarchyID + ".json", solutionsJSON); 
  }

  exportDesigns = (solutions) => {
    let savedSolutions = solutions.filter((solution) => { return solution.saved == 1; }); 

    let savedHierarchy = {}; 
    savedHierarchy['saved'] = savedSolutions; 
    this.exportHierarchy(savedHierarchy, 'saved'); 

    let trashedSolutions = solutions.filter((solution) => { return solution.trashed; }); 
    let trashedHierarchy = {}; 
    trashedHierarchy['trashed'] = trashedSolutions; 
    this.exportHierarchy(trashedHierarchy, 'trashed'); 

    let invalidated = solutions.filter((solution) => { return solution.invalidated; }); 
    let invalidatedHierarchy = {}; 
    invalidatedHierarchy['invalidated'] = invalidated; 
    this.exportHierarchy(invalidatedHierarchy, 'invalidated'); 

    let underConsideration = solutions.filter((solution) => { return solution.saved == 0 && !solution.invalidated}); 
    let underConsiderationHierarchy = {}; 
    underConsiderationHierarchy['under_consideration'] = underConsideration; 
    this.exportHierarchy(underConsiderationHierarchy, 'under_consideration'); 

    // Export SVGs and Images of saved designs, and then export the ZIP file
    this.exportZipFileAndSavedImages(savedSolutions); 
  }
  
  exportZipFileAndSavedImages = (savedSolutions) => {
    let self = this;
    let savedFolder = this.zipFile.folder('import_these_into_xd'); 

    for(let i=0; i<savedSolutions.length; i++) {
      let solutionDesignID = "design-canvas-" + savedSolutions[i].id; 
      let solution = document.getElementById(solutionDesignID); 
      if(solution) {
        let svgDesign = self.convertDesignToPaper(savedSolutions[i]); 
        let svgString = svgDesign.toString();
        savedFolder.file(solutionDesignID + ".svg", svgString); 
      }
    }

    this.zipFile.generateAsync({type:"blob"})
    .then(function(content) {
        // see FileSaver.js
        saveAs(content, "exported_from_scout.zip");
    });
  }
}



