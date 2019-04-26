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
            console.log(node.name); 
            if(node.name == "Alternative 1" || node.name == "Alternative 2" || node.name == "Alternative 3")
             {
                let elements = []; 
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
                        elementData.alternate = true; 
                        elementData.id = "alternate"; 
                        elementData.type = "group"; 

                        // Parse out the altenate from the name
                        let underscoreIndex = child.name.lastIndexOf("_"); 
                        elementData.name = child.name.substring(0, underscoreIndex); 
                    }

                    if(nameLower.indexOf("separator") > -1) {
                        elementData.separator = true; 
                    }

                    elements.push(elementData);
                }); 

                let artboardData = {}; 
                artboardData.children = elements; 
                artboardData.type = "canvas"; 
                artboardData.id = "canvas";
                artboardData.x = 0; 
                artboardData.y = 0; 
                artboardData.width = 360;
                artboardData.height = 640;  
                artboards.push(artboardData); 
            }
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