const {RootNode, Rectangle, Artboard} = require('scenegraph');
const storage = require('xd-storage-helper');
var { getArtboardAsJSON } = require("xd-json-wrapper");
const { alert, error } = require("../lib/dialogs.js");

/**
 * The sample command.
 * @param {Selection} selection 
 * @param {RootNode} root 
 */
async function exportToJSON(selection, root) {
    // Go to Plugins > Development > Developer Console to see this log output
    console.log("Plugin command is running!");

    // Insert a red square at (0, 0) in the current artboard or group/container
    let artboards = []; 
    root.children.forEach(node => {                              // [1]
        if (node instanceof Artboard) {                                  // [2]
            let artboard = node;

            let elements = []; 
            artboard.children.forEach(node => {
                let elementData = {}; 
                elementData.width = node.boundsInParent.width; 
                elementData.height = node.boundsInParent.height; 
                elementData.x = node.boundsInParent.x; 
                elementData.y = node.boundsInParent.y; 
                elementData.name = node.name; 
                elements.push(elementData);
            }); 

            let artboardData = {}; 
            artboardData.children = elements; 
            artboards.push(artboardData); 
        }
    });              

    // for each element, get height/width/x,y 
    const json = JSON.stringify(artboards); 
    console.log(json); 
    await alert("Connect to the Internet", //[1]
        "In order to function correctly, this plugin requires access to the Internet. Please connect to a network that has Internet access."); //[2]
}

module.exports.commands = {
    exportToScoutJSON: exportToJSON
};