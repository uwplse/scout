import domtoimage from 'dom-to-image'; 
import JSZip from 'jszip';

export default class Exporter  {
  constructor(props) {
    this.zipFile = new JSZip();
    this.exportPromises = []; 
  }

  addDesignToExports = (design, designNode) => {
  	let self = this; 
  	let designID = design.id; 
  	this.exportPromises.push(domtoimage.toPng(designNode)
	    .then(function (imgData) {
	        /* do something */
	        let imgDataParsed = imgData.replace('data:image/png;base64,', ''); 
	       	self.zipFile.file(designID + ".png", imgDataParsed, {base64: true});

	       	let hierarchy = design.elements; 
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



