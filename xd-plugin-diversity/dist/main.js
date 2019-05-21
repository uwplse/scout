module.exports=function(t){var e={};function r(n){if(e[n])return e[n].exports;var o=e[n]={i:n,l:!1,exports:{}};return t[n].call(o.exports,o,o.exports,r),o.l=!0,o.exports}return r.m=t,r.c=e,r.d=function(t,e,n){r.o(t,e)||Object.defineProperty(t,e,{enumerable:!0,get:n})},r.r=function(t){"undefined"!=typeof Symbol&&Symbol.toStringTag&&Object.defineProperty(t,Symbol.toStringTag,{value:"Module"}),Object.defineProperty(t,"__esModule",{value:!0})},r.t=function(t,e){if(1&e&&(t=r(t)),8&e)return t;if(4&e&&"object"==typeof t&&t&&t.__esModule)return t;var n=Object.create(null);if(r.r(n),Object.defineProperty(n,"default",{enumerable:!0,value:t}),2&e&&"string"!=typeof t)for(var o in t)r.d(n,o,function(e){return t[e]}.bind(null,o));return n},r.n=function(t){var e=t&&t.__esModule?function(){return t.default}:function(){return t};return r.d(e,"a",e),e},r.o=function(t,e){return Object.prototype.hasOwnProperty.call(t,e)},r.p="",r(r.s=1)}([function(t,e){t.exports=require("uxp")},function(t,e,r){const{RootNode:n,Rectangle:o,Artboard:a}=r(2);r(3);var{getArtboardAsJSON:s}=r(4);const{alert:i,error:c}=r(5);t.exports.commands={exportToScoutJSON:async function(t,e){console.log("Plugin command is running!"),console.log("Changes are here");let r=[],n={};e.children.forEach(t=>{if(t instanceof a&&(console.log(t.name),"Alternative 1"==t.name||"Alternative 2"==t.name||"Alternative 3"==t.name)){let e=[];t.children.forEach(t=>{let r={};r.width=t.boundsInParent.width,r.height=t.boundsInParent.height,r.x=t.boundsInParent.x,r.y=t.boundsInParent.y,r.name=t.name,r.type="element",r.id=t.name;let n=t.name.toLowerCase();if(n.indexOf("alternate")>-1){r.alternate=!0,r.id="alternate",r.type="group";let e=t.name.lastIndexOf("_");r.name=t.name.substring(0,e)}n.indexOf("separator")>-1&&(r.separator=!0),e.push(r)});let n={};n.children=e,n.type="canvas",n.id="canvas",n.x=0,n.y=0,n.width=360,n.height=640;let o={};o.elements=n,r.push(o)}}),n.saved=r,console.log(n);const o=JSON.stringify(n);console.log(o),await i("Connect to the Internet","In order to function correctly, this plugin requires access to the Internet. Please connect to a network that has Internet access.")}}},function(t,e){t.exports=require("scenegraph")},function(t,e,r){const n=r(0).storage,o=n.localFileSystem;let a;t.exports=class{static async init(){let t=await o.getDataFolder();try{let e=await t.getEntry("storage.json");return a=JSON.parse((await e.read({format:n.formats.utf8})).toString()),e}catch(e){const r=await t.createEntry("storage.json",{type:n.types.file,overwrite:!0});if(r.isFile)return await r.write("{}",{append:!1}),a={},r;throw new Error("Storage file storage.json was not a file.")}}static async get(t,e){if(!a){const t=await this.init();a=JSON.parse((await t.read({format:n.formats.utf8})).toString())}return void 0===a[t]?(await this.set(t,e),e):a[t]}static async set(t,e){const r=await this.init();return a[t]=e,await r.write(JSON.stringify(a),{append:!1,format:n.formats.utf8})}static async delete(t){return await this.set(t,void 0)}static async reset(){const t=await this.init();return await t.write("{}",{append:!1,format:n.formats.utf8})}}},function(t,e){class r{constructor(t){this.xdNode=t}toJSON(){const t=this.xdNode;return{type:t.constructor.name,guid:t.guid,parent:t.parent,children:t.children,isInArtworkTree:t.isInArtworkTree,isContainer:t.isContainer,selected:t.selected,visible:t.visible,opacity:t.opacity,transform:t.transform,translation:t.translation,rotation:t.rotation,globalBounds:t.globalBounds,localBounds:t.localBounds,boundsInParent:t.boundsInParent,topLeftInParent:t.topLeftInParent,localCenterPoint:t.localCenterPoint,globalDrawBounds:t.globalDrawBounds,name:t.name,hasDefaultName:t.hasDefaultName,locked:t.locked,markedForExport:t.markedForExport,hasLinkedContent:t.hasLinkedContent}}}class n{constructor(t){this.xdNode=t,this.parentNodeWrapper=new r(this.xdNode)}toJSON(){let t={};this.parentNodeWrapper&&(t=this.parentNodeWrapper.toJSON());const e=this.xdNode;return{type:e.constructor.name,fill:e.fill,fillEnabled:e.fillEnabled,stroke:e.stroke,strokeEnabled:e.strokeEnabled,strokeWidth:e.strokeWidth,strokePosition:e.strokePosition,strokeEndCaps:e.strokeEndCaps,strokeJoins:e.strokeJoins,strokeMiterLimit:e.strokeMiterLimit,strokeDashArray:e.strokeDashArray,strokeDashOffset:e.strokeDashOffset,shadow:e.shadow,blur:e.blur,pathData:e.pathData,hasLinkedGraphicFill:e.hasLinkedGraphicFill,...t}}}const o={Matrix:class{constructor(t){this.xdNode=t}toJSON(){return{type:this.xdNode.constructor.name}}},Color:class{constructor(t){this.xdNode=t}toJSON(){const t=this.xdNode;return{type:t.constructor.name,a:t.a,r:t.r,g:t.g,b:t.b}}},LinearGradientFill:class{constructor(t){this.xdNode=t}toJSON(){const t=this.xdNode;return{type:t.constructor.name,colorStops:t.colorStops,startX:t.startX,startY:t.startY,endX:t.endX,endY:t.endY}}},RadialGradientFill:class{constructor(t){this.xdNode=t}toJSON(){return{type:this.xdNode.constructor.name}}},ImageFill:class{constructor(t){this.xdNode=t}toJSON(){const t=this.xdNode;return{type:t.constructor.name,SCALE_STRETCH:t.SCALE_STRETCH,SCALE_COVER:t.SCALE_COVER,scaleBehaviour:t.scaleBehaviour,mimeType:t.mimeType,isLinkedContent:t.isLinkedContent,naturalWidth:t.naturalWidth,naturalHeight:t.naturalHeight}}},Shadow:class{constructor(t){this.xdNode=t}toJSON(){const t=this.xdNode;return{type:t.constructor.name,x:t.x,y:t.y,blur:t.blur,color:t.color,visible:t.visible}}},Blur:class{constructor(t){this.xdNode=t}toJSON(){const t=this.xdNode;return{type:t.constructor.name,blurAmount:t.blurAmount,brightnessAmount:t.brightnessAmount,fillOpacity:t.fillOpacity,isBackgroundEffect:t.isBackgroundEffect,visible:t.visible}}},SceneNode:r,GraphicsNode:n,Artboard:class{constructor(t){this.xdNode=t,this.parentNodeWrapper=new n(this.xdNode)}toJSON(){let t={};this.parentNodeWrapper&&(t=this.parentNodeWrapper.toJSON());const e=this.xdNode;return{type:e.constructor.name,width:e.width,height:e.height,viewportHeight:e.viewportHeight,...t}}},Rectangle:class{constructor(t){this.xdNode=t,this.parentNodeWrapper=new n(this.xdNode)}toJSON(){let t={};this.parentNodeWrapper&&(t=this.parentNodeWrapper.toJSON());const e=this.xdNode;return{type:e.constructor.name,width:e.width,height:e.height,cornerRadii:e.cornerRadii,hasRoundedCorners:e.hasRoundedCorners,effectiveCornerRadii:e.effectiveCornerRadii,...t}}},Ellipse:class{constructor(t){this.xdNode=t,this.parentNodeWrapper=new n(this.xdNode)}toJSON(){let t={};this.parentNodeWrapper&&(t=this.parentNodeWrapper.toJSON());const e=this.xdNode;return{type:e.constructor.name,radiusX:e.radiusX,radiusY:e.radiusY,isCircle:e.isCircle,...t}}},Line:class{constructor(t){this.xdNode=t,this.parentNodeWrapper=new n(this.xdNode)}toJSON(){let t={};this.parentNodeWrapper&&(t=this.parentNodeWrapper.toJSON());const e=this.xdNode;return{type:e.constructor.name,start:e.start,end:e.end,...t}}},Path:class{constructor(t){this.xdNode=t,this.parentNodeWrapper=new n(this.xdNode)}toJSON(){let t={};this.parentNodeWrapper&&(t=this.parentNodeWrapper.toJSON());const e=this.xdNode;return{type:e.constructor.name,pathData:e.pathData,...t}}},BooleanGroup:class{constructor(t){this.xdNode=t,this.parentNodeWrapper=new n(this.xdNode)}toJSON(){let t={};this.parentNodeWrapper&&(t=this.parentNodeWrapper.toJSON());const e=this.xdNode;return{type:e.constructor.name,pathOp:e.pathOp,...t}}},Text:class{constructor(t){this.xdNode=t,this.parentNodeWrapper=new n(this.xdNode)}toJSON(){let t={};this.parentNodeWrapper&&(t=this.parentNodeWrapper.toJSON());const e=this.xdNode;return{type:e.constructor.name,text:e.text,styleRanges:e.styleRanges,flipY:e.flipY,textAlign:e.textAlign,lineSpacing:e.lineSpacing,areaBox:e.areaBox,clippedByArea:e.clippedByArea,...t}}},Group:class{constructor(t){this.xdNode=t,this.parentNodeWrapper=new r(this.xdNode)}toJSON(){let t={};this.parentNodeWrapper&&(t=this.parentNodeWrapper.toJSON());const e=this.xdNode;return{type:e.constructor.name,mask:e.mask,...t}}},SymbolInstance:class{constructor(t){this.xdNode=t,this.parentNodeWrapper=new r(this.xdNode)}toJSON(){let t={};this.parentNodeWrapper&&(t=this.parentNodeWrapper.toJSON());const e=this.xdNode;return{type:e.constructor.name,symbolId:e.symbolId,...t}}},RepeatGrid:class{constructor(t){this.xdNode=t,this.parentNodeWrapper=new r(this.xdNode)}toJSON(){let t={};this.parentNodeWrapper&&(t=this.parentNodeWrapper.toJSON());const e=this.xdNode;return{type:e.constructor.name,width:e.width,height:e.height,numColumns:e.numColumns,numRows:e.numRows,paddingX:e.paddingX,paddingY:e.paddingY,cellSize:e.cellSize,...t}}},LinkedGraphic:class{constructor(t){this.xdNode=t,this.parentNodeWrapper=new r(this.xdNode)}toJSON(){let t={};return this.parentNodeWrapper&&(t=this.parentNodeWrapper.toJSON()),{type:this.xdNode.constructor.name,...t}}},RootNode:class{constructor(t){this.xdNode=t,this.parentNodeWrapper=new r(this.xdNode)}toJSON(){let t={};return this.parentNodeWrapper&&(t=this.parentNodeWrapper.toJSON()),{type:this.xdNode.constructor.name,...t}}}};function a(t){const e=o[t.constructor.name];if(void 0!==e)return new e(t)}function s(t){const e=[];return t.children.forEach(t=>{void 0!==a(t)&&e.push(a(t))}),e}t.exports={getXDWrapper:a,getArtboardAsJSON:s,getDocumentAsJSON:function(t){const e=[];return t.children.forEach(t=>{e.push(s(t))}),e}}},function(t,e,r){const{getManifest:n,getNearestIcon:o}=r(6);let a;async function s({title:t,icon:e="plugin-icon",msgs:r,prompt:s,multiline:i=!1,render:c,template:l,isError:d=!1,buttons:p=[{label:"Close",variant:"cta",type:"submit"}]}={},u=360,h="auto",m=18){console.log("create a dialog"),console.log(r);let N=Array.isArray(r)?r:[r];try{a||(a=await n())}catch(t){}console.log("here");let f=!1;"plugin-icon"===e&&a.icons&&(f=!0,e=o(a,m=24));const g=document.createElement("dialog");g.innerHTML=`\n<style>\n    form {\n        width: ${u}px;\n    }\n    .h1 {\n        display: flex;\n        flex-direction: row;\n        justify-content: space-between;\n        align-items: center;\n    }\n    .h1 img {\n        width: ${m}px;\n        height: ${m}px;\n        flex: 0 0 ${m}px;\n        padding: 0;\n        margin: 0;\n    }\n    img.plugin-icon {\n        border-radius: 4px;\n        overflow: hidden;\n    }\n    .list {\n        display: flex;\n        flex-direction: row;\n    }\n    .list .margin {\n        margin-bottom: 0;\n        margin-left: 0;\n    }\n    .list span {\n        flex: 0 0 auto;\n        border: 1px solid transparent;\n    }\n    .list .bullet {\n        text-align: center;\n    }\n    .list + .list {\n        margin-top: 0;\n    }\n    textarea {\n        height: 200px;\n    }\n    .container {\n        zoverflow-x: hidden;\n        overflow-y: auto;\n        height: ${"auto"===h?h:`${h}px`};\n    }\n</style>\n<form method="dialog">\n    <h1 class="h1">\n        <span ${d?'class="color-red"':""}>${t}</span>\n        ${e?`<img ${f?`class="plugin-icon" title="${a.name}"`:""} src="${e}" />`:""}\n    </h1>\n    <hr />\n    <div class="container">\n        ${!c&&(l?l():N.map(t=>(function t(e){if(Array.isArray(e))return e.map(e=>t(e)).join("");if("string"!=typeof e)return t(`${e}`);let r=e;r="##"===r.substr(0,2)?`<h3>${r.substr(2).trim().toUpperCase()}</h3>`:"#"===r.substr(0,1)?`<h2>${r.substr(1).trim()}</h2>`:"* "===r.substr(0,2)?`<p class="list"><span class="bullet margin">•</span><span class="margin">${r.substr(2).trim()}</span></p>`:"----"===r.substr(0,4)?`<hr class="small"/>${r.substr(5).trim()}`:"---"===r.substr(0,3)?`<hr/>${r.substr(4).trim()}`:`<p>${r.trim()}</p>`;const n=/\[([^\]]*)\]\(([^\)]*)\)/,o=e.match(n);if(o){const t=o[1];r=`<p><a href="${o[2]}">${r.replace(n,t).replace(/\<\|?p\>/g,"")}</a></p>`}return r})(t)).join("")+(s?`<label>${i?`<textarea id="prompt" placeholder="${s}"></textarea>`:`<input type="text" id="prompt" placeholder="${s}" />`}</label>`:""))}\n    </div>\n    <footer>\n        ${p.map(({label:t,type:e,variant:r}={},n)=>`<button id="btn${n}" type="${e}" uxp-variant="${r}">${t}</button>`).join("")}\n    </footer>\n</form>\n    `,c&&g.querySelector(".container").appendChild(c()),console.log("here");let y=-1,x=-1,b=-1;g.querySelector("form").onsubmit=(()=>g.close("ok")),console.log("here"),p.forEach(({type:t,variant:e}={},r)=>{const n=g.querySelector(`#btn${r}`);"submit"!==t&&"cta"!==e||(y=r),"reset"===t&&(x=r),n.onclick=(t=>{t.preventDefault(),b=r,g.close(r===x?"reasonCanceled":"ok")})}),console.log("here");try{return console.log("create dialog"),document.appendChild(g),"reasonCanceled"===await g.showModal()?{which:x,value:""}:(-1===b&&(b=y),{which:b,value:s?g.querySelector("#prompt").value:""})}catch(t){return console.log(t),{which:x,value:""}}finally{g.remove()}}t.exports={createDialog:s,alert:async function(t,...e){return s({title:t,msgs:e})},error:async function(t,...e){return s({title:t,isError:!0,msgs:e})},confirm:async function(t,e,r=["Cancel","OK"]){return s({title:t,msgs:[e],buttons:[{label:r[0],type:"reset",variant:"primary"},{label:r[1],type:"submit",variant:"cta"}]})},warning:async function(t,e,r=["Cancel","OK"]){return s({title:t,msgs:[e],buttons:[{label:r[0],type:"submit",variant:"primary"},{label:r[1],type:"button",variant:"warning"}]})},prompt:async function(t,e,r,n=["Cancel","OK"],o=!1){return s({title:t,msgs:[e],prompt:r,multiline:o,buttons:[{label:n[0],type:"reset",variant:"primary"},{label:n[1],type:"submit",variant:"cta"}]})}}},function(t,e,r){let n;t.exports={getManifest:async function(){if(!n){const t=r(0).storage.localFileSystem,e=await t.getPluginFolder(),o=await e.getEntry("manifest.json");if(o){const t=await o.read();n=JSON.parse(t)}}return n},getNearestIcon:function(t,e){if(t&&t.icons)return t.icons.sort((t,e)=>{const r=t.width,n=e.width;return r<n?1:r>n?-1:0}).reduce((t,r)=>(t?r.width>=e&&(t=r):t=r,t)).path}}}]);