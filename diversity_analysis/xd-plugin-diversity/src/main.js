const {RootNode, Rectangle, Artboard} = require('scenegraph');
const storage = require('xd-storage-helper');
var { getArtboardAsJSON } = require("xd-json-wrapper");
const { alert, error } = require("../lib/dialogs.js");

/**
 *  Export a layout artboard out to JSON format.
 * @param {Selection} selection 
 * @param {RootNode} root 
 */
async function exportToJSON(selection, root) {
    let artboards = []; 
    let rootDoc = {}; 
    root.children.forEach(node => {                              // [1]
        if (node instanceof Artboard) {                                  // [2]
            if(node.name == "Alternative 1" || node.name == "Alternative 2" || node.name == "Alternative 3"
                || node.name == "Original")
             {
                // Create JSON tree structure for each of the measured artboards. 
                let elements = []; 

                // Parse child elements 
                node.children.forEach(child => {
                    let elementData = {}; 
                    elementData.width = child.boundsInParent.width; 
                    elementData.height = child.boundsInParent.height; 
                    elementData.x = child.boundsInParent.x; 
                    elementData.y = child.boundsInParent.y; 
                    elementData.name = child.name; 
                    elementData.type = "element";
                    elementData.id = child.name; 

                    let nameLower = child.name.toLowerCase(); 
                    if(nameLower.indexOf("alternate") > -1) {
                        elementData.id = child.name; 
                        elementData.type = "group"; 

                        // Parse out the altenate from the name
                        let underscoreIndex = child.name.lastIndexOf("_"); 
                        elementData.name = child.name.substring(0, underscoreIndex); 
                        elementData.alternate = child.name.substring(underscoreIndex, child.name.length); 
                    }

                    if(nameLower.indexOf("separator") > -1) {
                        elementData.separator = true; 
                    }

                    elements.push(elementData);
                }); 

                // Create the root
                let artboardData = {}; 
                artboardData.children = elements; 
                artboardData.type = "canvas"; 
                artboardData.id = "canvas";
                artboardData.x = 0; 
                artboardData.y = 0; 
                artboardData.width = 360;
                artboardData.height = 640;  

                // Name of the artboard
                artboardData.name = node.name; 
                let artboardTree = {}; 
                artboardTree.elements = artboardData; 
                artboards.push(artboardTree); 
            }
        }
    });              

    // for each element, get height/width/x,y 
    // Print JSON tree out the the console which we copy paste into another file for the analysis. 
    rootDoc.saved = artboards; 
    const json = JSON.stringify(rootDoc); 
    console.log(json);
}

module.exports.commands = {
    exportToScoutJSON: exportToJSON
};