/* eslint no-console:0 */
import 'rc-tree/assets/index.css';
import '../css/Tree.css';
import '../css/ConstraintsCanvas.css';
import React from 'react';
import ReactDOM from 'react-dom';
import Tree, { TreeNode } from 'rc-tree';
import pageLogo from '../../wireframes/accounts/pie_chart.svg';
import SVGInline from "react-svg-inline"

export default class Importer extends React.Component {
  state = {
    gData: [],
    autoExpandParent: true,
    expandedKeys: ['0-0-key', '0-0-0-key', '0-0-0-0-key'],
  };

  componentDidMount() {
    const treeData = []; 
    const item = {
      key: "1", 
      children: [
        {
          key: "2", 
          children: [
            {
              key: "3"
            }
          ]
        }, 
        {
          key: "3"
        }, 
        {
          key: "4"
        }
      ]
    }

    treeData.push(item);
    this.setState({
      gData: treeData
    });
  }
  
  onDragStart = (info) => {
    console.log('start', info);
  }
  
  onDragEnter = (info) => {
    console.log('enter', info);
    // this.setState({
    //   expandedKeys: info.expandedKeys,
    // });
    info.event.stopPropagation();
    info.event.preventDefault();
  }

  onDrop = (info) => {
    console.log('drop', info);
    const dropKey = info.node.props.eventKey;
    const dragKey = info.dragNode.props.eventKey;
    const dropPos = info.node.props.pos.split('-');
    const dropPosition = info.dropPosition - Number(dropPos[dropPos.length - 1]);

    const loop = (data, key, callback) => {
      data.forEach((item, index, arr) => {
        if (item.key === key) {
          callback(item, index, arr);
          return;
        }
        if (item.children) {
          loop(item.children, key, callback);
        }
      });
    };
    const data = [...this.state.gData];

    // Find dragObject
    let dragObj;
    loop(data, dragKey, (item, index, arr) => {
      arr.splice(index, 1);
      dragObj = item;
    });

    if (!info.dropToGap) {
      // Drop on the content
      loop(data, dropKey, (item) => {
        item.children = item.children || [];
        // where to insert 示例添加到尾部，可以是随意位置
        item.children.push(dragObj);
      });
    } else if (
      (info.node.props.children || []).length > 0 &&  // Has children
      info.node.props.expanded &&                     // Is expanded
      dropPosition === 1                              // On the bottom gap
    ) {
      loop(data, dropKey, (item) => {
        item.children = item.children || [];
        // where to insert 示例添加到尾部，可以是随意位置
        item.children.unshift(dragObj);
      });
    } else {
      // Drop on the gap
      let ar;
      let i;
      loop(data, dropKey, (item, index, arr) => {
        ar = arr;
        i = index;
      });
      if (dropPosition === -1) {
        ar.splice(i, 0, dragObj);
      } else {
        ar.splice(i + 1, 0, dragObj);
      }
    }

    this.setState({
      gData: data,
    });
  }

  onExpand = (expandedKeys) => {
    console.log('onExpand', arguments);
    this.setState({
      expandedKeys,
      autoExpandParent: false,
    });
  }

  nodeIcon = () => {
    return (<div><SVGInline 
            svg={pageLogo} 
            height={"116px"} 
            width={"116px"} />
             <div className="widget-feedback-container">
                    <div className="widget-feedback">
                      <ul className={"widget-feedback-items"}>
                        <li className="widget-feedback-items-list"> 
                          <span className="widget-feedback-items-label">
                          {"Keep arrangement vertical"}
                          </span>
                          <button 
                            className={"widget-feedback-items-remove "}>
                            <span className="glyphicon glyphicon-minus" aria-hidden="true"></span>
                          </button>
                        </li>
                      </ul>
                    </div>
                  </div>
            </div>);
  }


  onSelected = (selectedKeys, evt) => {
    let selected = selectedKeys[selectedKeys.length-1];

    // Determine if the newly selected ID is a sibling of the selectedd
    // If it is not a sibling, unselect 

    // Use selectedKeys to set initially selectedx
  }

  render() {



    const nodeIconSVG = this.nodeIcon();
    const loop = data => {
      return data.map((item) => {
        if (item.children && item.children.length) {
          return <TreeNode key={item.key} icon={nodeIconSVG} title={""}>{loop(item.children)}</TreeNode>;
        }
        return <TreeNode key={item.key} icon={nodeIconSVG} title={""} />;
      });
    };

    return (<div className="draggable-demo">
      <h2>draggable</h2>
      <p>drag a node into another node</p>
      <div className="draggable-container">
        <Tree
          draggable={true}
          selectable={true}
          showLine={false}
          multiple={true}
          selectedKeys={["3", "4"]}
          onSelect={this.onSelected}
          onDragStart={this.onDragStart}
          onDragEnter={this.onDragEnter}
          onDrop={this.onDrop}
        >
          {loop(this.state.gData)}
        </Tree>
      </div>
    </div>);
  }
}

// ReactDOM.render(<Demo />, document.getElementById('__react-content'));

// TODO 
// Switcher Icon can be customized  
