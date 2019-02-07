// App.jsx
import React from "react";
import '../css/FeedbackContainer.css';
import Toggle from 'react-bootstrap-toggle';
import {Dropdown} from 'react-bootstrap'; 
import ConstraintActions from "./ConstraintActions"; 

class FeedbackItem extends React.Component {
  constructor(props) {
    super(props); 
    this.shape = props.shape;  // The shape associated with this FeedbackItem
    this.property = props.property; 
    this.action = props.action; 
    
    this.state = {
      selected: "Vary", 
      locked: this.action['keep'].type == "undo", 
      prevented: this.action['keep'].type == "undo"
    }; 
  }

  componentDidMount() {
    // let locked = this.action['keep'].type == "undo";

  }

  onSelected = (newValue) => {
    this.setState({
      selected: newValue
    }); 
  }

  onLocked = () => {
    let keepType = this.action['keep'].type; 
    this.action['keep'].action[keepType].updateConstraintsCanvasShape(this.property, this.shape, this.state.selected);

    this.setState({
      locked: !this.state.locked
    });

    // Notify the ConstraintsCanvas tree of the update
    this.props.update();
  }

  onPrevented = () => {
    let preventType = this.action['prevent'].type;
    this.action['prevent'].action[preventType].updateConstraintsCanvasShape(this.property, this.shape, this.state.selected);

    this.setState({
      prevented: !this.state.prevented
    });

    // Notify the ConstraintsCanvas tree of the update
    this.props.update();
  }

  render () {
    // The bind will send the menu trigger (JSON shape object) and selected item (text) back to the canvas to propogate it back to the constraints canvas
    let locked = this.state.locked;
    let keep = this.action['keep'].action;  
    let prevented = this.state.prevented;
    let prevent = this.action['prevent'].action;
    let domain = this.action.domain; 
    let label = locked ? "" : "Vary"; 
    let propertyLabel = this.property.charAt(0).toUpperCase() + this.property.slice(1); 

    // Lock -> 
    return (<div className="feedback-container-toggle">
              <label className="feedback-container-label">{propertyLabel}</label>
              <Dropdown>
                <Dropdown.Toggle id="dropdown-basic">
                  {this.state.selected}
                </Dropdown.Toggle>
                <Dropdown.Menu> 
                  {domain.map((key) => {
                    return (<Dropdown.Item onClick={this.onSelected.bind(this, key)}>{key}</Dropdown.Item>);
                  })} 
                </Dropdown.Menu>
              </Dropdown>
              <div className="feedback-container-locks">
                <span className={"glyphicon glyphicon-lock " + (locked ? "locked" : "unlocked")}
                  onClick={this.onLocked}></span>
                <span className={"glyphicon glyphicon-remove " + (locked ? "locked" : "unlocked")}
                  onClick={this.onPrevented}></span>
              </div> 
            </div>);
  }
}

class ContainerOrderFeedback extends React.Component {
  constructor(props) {
    super(props); 

    this.state = {
      currentOrderValue: props.currentOrderValue
    }
  }

  onToggle = () => {
    let newOrder = this.state.currentOrderValue == "important" ? "unimportant" : "important"; 
    this.setState({
      currentOrderValue: newOrder
    }); 

    this.props.onClick(newOrder);
  }

  render () {
    let checked = this.state.currentOrderValue == "important"; 
    let label = "Order Important";
    return (
        <div className="feedback-container-toggle"> 
          <label className="feedback-container-label">{label}</label>
          <Toggle
            onClick={this.onToggle}
            on={<h2>ON</h2>}
            off={<h2>OFF</h2>}
            size="xs"
            offstyle={"primary"}
            onstyle={"primary"}
            active={checked}
          />
        </div>);  
  }
}

class OrderFeedback extends React.Component {
  constructor(props) {
    super(props); 

    this.state = {
      currentOrder: props.currentOrder
    }; 
  }

  onToggle = () => {
    let newOrder = this.state.currentOrder == -1 ? this.props.index : -1; 
    this.setState({
      currentOrder: newOrder
    })

    this.props.onClick(newOrder);
  }

  render () {
    let orderPosition = this.props.index == 0 ? "first" : "last";  

    let ordered = (this.state.currentOrder != -1); 
    let label = "Keep " + orderPosition + "."; 
    let newOrder = (ordered ? this.props.index : -1); 

    return (
        <div className="feedback-container-toggle"> 
          <label className="feedback-container-label">{label}</label>
          <Toggle
            onClick={this.onToggle}
            on={<h2>ON</h2>}
            off={<h2>OFF</h2>}
            size="xs"
            offstyle={"primary"}
            onstyle={"primary"}
            active={ordered}
          />
        </div>); 
  }
}

class ImportanceFeedback extends React.Component {
  constructor(props) {
    super(props); 
  
    this.state = {
      importanceLevel: props.currentImportance
    }; 
  }

  onClick = (newImportanceLevel) => {
    this.setState({
      importanceLevel: newImportanceLevel
    }); 

    this.props.onClick(newImportanceLevel); 
  }

  render () {
    let label = this.state.importanceLevel.charAt(0).toUpperCase() + this.state.importanceLevel.slice(1); 
    return (<div className="feedback-container-toggle">
              <label className="feedback-container-label">Emphasis</label>
              <Dropdown>
                <Dropdown.Toggle id="dropdown-basic">
                  {label}
                </Dropdown.Toggle>

                <Dropdown.Menu> 
                  <Dropdown.Item onClick={this.onClick.bind(this, "high")}>High</Dropdown.Item>
                  <Dropdown.Item onClick={this.onClick.bind(this, "normal")}>Normal</Dropdown.Item>
                  <Dropdown.Item onClick={this.onClick.bind(this, "low")}>Low</Dropdown.Item>
                </Dropdown.Menu>
              </Dropdown>
            </div>);
      }
}

export default class FeedbackContainer extends React.Component {
  constructor(props) {
  	super(props);
    
    this.getConstraintsCanvasShape = props.getConstraintsCanvasShape; 
  }

  getTreeFeedbackItems = () => {
    let feedbackItems = []; 
    let shape = this.props.selectedElement; 
    let callbacks = this.props.feedbackCallbacks; 

    if(callbacks.setContainerOrder) {
      feedbackItems.push(
        <ContainerOrderFeedback 
          currentOrderValue={shape.containerOrder}
          onClick={callbacks.setContainerOrder} />); 
    }

    if(callbacks.setOrder) {
      let shapeIndex = callbacks.getCurrentShapeIndex(shape.name); 
      let siblings = callbacks.getCurrentShapeSiblings(shape.name);
      let showOrderMenuItem = (!siblings.prev || !siblings.next);  

      if(showOrderMenuItem) {
        feedbackItems.push(<OrderFeedback 
          index={shapeIndex} currentOrder={shape.order} onClick={callbacks.setOrder} />); 
      }
    }


    if(callbacks.setImportanceLevel) {
        feedbackItems.push(
          <ImportanceFeedback
            currentImportance={shape.importance}
            onClick={callbacks.setImportanceLevel} />); 
    }

    return feedbackItems; 
  }

  getAction(constraint, constraintsMenu) {
      let constraintsCanvasShape = this.getConstraintsCanvasShape(this.props.selectedElement.name);
      let action = {}; 

      if(constraintsCanvasShape["locks"]
        && constraintsCanvasShape["locks"].indexOf(constraint) >= 0) {
        if(constraintsCanvasShape[constraint] == this.props.selectedElement[constraint]) {
          // The constraint is active and set to true, show the undo option
          action.keep = { type: "undo", action: constraintsMenu["keep"]};           
        }
        else {
          action.keep = { type: "do", action: constraintsMenu["keep"]};  
        }
      } else {
        action.keep = { type: "do", action: constraintsMenu["keep"]}; 
      } 

      if(constraintsCanvasShape["prevents"]
        && constraintsCanvasShape["prevents"].indexOf(constraint) >= 0) {
        let currValue = this.props.selectedElement[constraint]; 
        if(constraintsCanvasShape[constraint] == currValue) {
          // The constraint is active and set to true, show the undo option
          action.prevent = { type: "undo", action: constraintsMenu["prevent"], value: currValue};           
        }
        else {
          action.prevent = { type: "do", action: constraintsMenu["prevent"]};  
        }
      } else {
        action.prevent = { type: "do", action: constraintsMenu["prevent"]}; 
      } 

      action.domain = constraintsMenu["domains"][constraint]; 
      return action; 
  }

  getDesignFeedbackItems = () => {
    let shape = this.props.selectedElement; 

    let feedbackItems = [];

    // Element --?
    // X, Y, Width (?), Height (?)
    // X, Y - > Vary (?)
    // Width, Height -> Precompute the possible values.
    // Columns -> Should prune the values (within reason?)

    // Container 
    // Arrangement - Values
    // Alignemnt - values
    // Padding - values
    if(shape.type == "group") {
      // Dropdown for each 
      let groupVariableSelectors = ConstraintActions.groupConstraints.values.map((key) => {
        let action = this.getAction(key, ConstraintActions.groupConstraints);
        return (<FeedbackItem onClick={this.props.onClick} 
                  action={action}
                  shape={this.props.selectedElement} 
                  property={key}
                  update={this.props.updateConstraintsCanvas}
                  key={key} />);
      }); 
      
      feedbackItems.push(groupVariableSelectors);
    }

    return feedbackItems; 

    // if(shape.type == "canvas") {
    //   // Dropdown for each 
    //   let canvasVariableSelectors = ConstraintActions.canvasConstraints.values.map((key) => {
    //     let keepAction = this.getKeepAction(key, ConstraintActions.canvasConstraints);
    //     let preventAction = this.getPreventAction(key, ConstraintActions.canvasConstraints);
    //     return (<FeedbackItem onClick={this.props.onClick} 
    //               keepAction={keepAction}
    //               preventAction={preventAction} 
    //               shape={this.props.selectedElement} 
    //               property={key}
    //               key={key} />);
    //   }); 
    // }
  }

  render () {
    let treeFeedbackItems = this.props.selectedElement ? this.getTreeFeedbackItems() : undefined; 
    let designFeedbackItems = this.props.selectedElement ? this.getDesignFeedbackItems() : undefined; 
    return (
        <div className="panel panel-primary feedback-container">
          <div className="panel-heading"> 
            <h3 className="panel-title">Feedback
            </h3>
          </div>
          <div tabIndex="1" className="panel-body"> 
            {treeFeedbackItems}
            {designFeedbackItems}
            {!this.props.selectedElement ? 
              (<div className="card card-body bg-light feedback-container-alert">
                <span className="feedback-container-empty">Select an element in the Outline Panel or in a Design to see feedback options.</span>
              </div>) : undefined}
          </div>  
      </div>); 
  }
}
