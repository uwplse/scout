import domtoimage from 'dom-to-image'; 
import JSZip from 'jszip';

export default class Exporter  {
  constructor(props) {
    this.zipFile = new JSZip();
    this.exportPromises = []; 
  }

  convertDesignToHierarchy(design) {
  	let treeData = {}; 
  	let rootNode = design.elements["canvas"]; 
  	rootNode.width = rootNode.orig_width;
  	rootNode.height = rootNode.orig_height; 
  	this.getDataForNode(rootNode, treeData, design.elements); 
  	return treeData; 
  }

  getDataForNode(node, data, elements) {
  	let dataNode = elements[node.name]; 
  	data.x = dataNode.x; 
  	data.y = dataNode.y; 
  	data.width = dataNode.width; 
  	data.height = dataNode.height; 
  	data.type = dataNode.type; 

  	if(node.children && node.children.length) {
  		data.children = []; 
  		for(let i=0; i<node.children.length; i++) {
  			let child = node.children[i]; 
  			let childData = {}; 

  			this.getDataForNode(child, childData, elements);
  			data.children.push(childData);   
  		}
  	}
  }

  addDesignToExports = (design, designNode) => {
  	let self = this; 
  	let designID = design.id; 
  	this.exportPromises.push(domtoimage.toPng(designNode)
	    .then(function (imgData) {
	        /* do something */
	        let imgDataParsed = imgData.replace('data:image/png;base64,', ''); 
	       	self.zipFile.file(designID + ".png", imgDataParsed, {base64: true});

	       	let hierarchy = self.convertDesignToHierarchy(design); 
	        let designJSON = JSON.stringify(hierarchy); 
	        self.zipFile.file(designID + ".json", designJSON); 
	    })); 
  }
  
  exportDesigns = () => {
    Promise.all(this.exportPromises)
    .then(() => {
      this.zipFile.generateAsync({type:"blob"})
      .then(function(content) {
          // see FileSaver.js
          saveAs(content, "exported_from_scout.zip");
      });
    });
  }
}



