// App.jsx
import React from "react";
import '../css/FeedbackContainer.css';
import Toggle from 'react-bootstrap-toggle';
import {Dropdown} from 'react-bootstrap'; 
import ConstraintActions from "./ConstraintActions"; 

class FeedbackItem extends React.Component {
  constructor(props) {
    super(props); 
    
    this.state = {
      selected: "Vary", 
      locked: false,
      prevented: false, 
      shape: props.shape, 
      property: props.property, 
      action: props.action
    }; 
  }

  componentDidMount() {
    // intialize the selector state based on the locked prevented values 
    let selected = FeedbackItem.getInitialSelected(this.state.shape, this.state.property, this.state.action.domain); 
    let locked = FeedbackItem.getInitialLocked(this.state.shape, this.state.property); 
    let prevented = FeedbackItem.getInitialPrevented(this.state.shape, this.state.property); 
    this.setState({
      selected: selected, 
      prevented: prevented, 
      locked: locked
    }); 
  }

  static getDerivedStateFromProps(nextProps, prevState) {
    let shapeChanged = nextProps.shape != prevState.shape; 

    return {
      shape: nextProps.shape, 
      action: nextProps.action, 
      property: nextProps.property, 
      selected: (shapeChanged ? FeedbackItem.getInitialSelected(nextProps.shape, nextProps.property, nextProps.action.domain) : prevState.selected),
      locked: (shapeChanged ? FeedbackItem.getInitialLocked(nextProps.shape, nextProps.property) : prevState.locked), 
      prevented: (shapeChanged ? FeedbackItem.getInitialPrevented(nextProps.shape, nextProps.property) : prevState.prevented)
    };     
  }

  static getInitialPrevented(shape, property) {
    if(shape.prevents && shape.prevents.length && shape.prevents.indexOf(property) > -1) {
      return true;
    }

    return false;
  }

  static getInitialLocked(shape, property) {
    if(shape.locks && shape.locks.length && shape.locks.indexOf(property) > -1) {
      return true; 
    }
  
    return false;
  }

  static getInitialSelected(shape, property, domain) {
    let value = shape[property]; 
    if(value != undefined) {
      return value; 
    }

    return "Vary";
  }

  onSelected = (newValue) => {
    this.setState({
      selected: newValue
    }); 
  }

  onLocked = () => {
    let preventValue = this.state.prevented; 
    if(this.state.prevented) {
      // If the property was already "Kept", remove it and keep the Prevent instead
      this.state.action['prevent']['undo'].updateConstraintsCanvasShape(this.state.property, this.state.shape);
      preventValue = false;
    }

    if(this.state.locked){
      this.state.action['keep']['undo'].updateConstraintsCanvasShape(this.state.property, this.state.shape);    
    }
    else {
      this.state.action['keep']['do'].updateConstraintsCanvasShape(this.state.property, this.state.shape, this.state.selected);     
    }

    this.setState({
      locked: !this.state.locked, 
      prevented: preventValue
    });

    // Notify the ConstraintsCanvas tree of the update
    this.props.update();
  }

  onPrevented = () => {
    let lockedValue = this.state.locked; 
    if(this.state.locked) {
      // If the property was already "Kept", remove it and keep the Prevent instead
      this.state.action['keep']['undo'].updateConstraintsCanvasShape(this.state.property, this.state.shape);
      lockedValue = false;
    }

    if(this.state.prevented) {
      this.state.action['prevent']['undo'].updateConstraintsCanvasShape(this.state.property, this.state.shape);
    } else {
      this.state.action['prevent']['do'].updateConstraintsCanvasShape(this.state.property, this.state.shape, this.state.selected); 
    }

    this.setState({
      prevented: !this.state.prevented, 
      locked: lockedValue
    });

    // Notify the ConstraintsCanvas tree of the update
    this.props.update();
  }

  getPropertyLabel = () => {
    let splits = this.state.property.split("_"); 
    let label = ""; 
    for(let i=0; i<splits.length; i++) {
      let token = splits[i]; 
      label += token.charAt(0).toUpperCase() + token.slice(1);
      if(i < splits.length-1) {
        label += " "; 
      }
    }
    return label; 
  }

  toUpperCase(label) {
    if(typeof label == "string" && label.length > 1) {
      return label.charAt(0).toUpperCase() + label.slice(1);
    }

    return label;
  }

  getDomainValue = (value) => {
    let index = ConstraintActions.index_domains.indexOf(this.state.property); 
    if(index > -1) {
      let indexInDomain = this.state.action.domain.indexOf(value); 
      return indexInDomain; 
    }

    return value;
  }

  getSelectedValue = (value) => {
    if(value != "Vary" && ConstraintActions.index_domains.indexOf(this.state.property) > -1) {
      return this.state.action.domain[value]; 
    }

    return value;
  }

  render () {
    // The bind will send the menu trigger (JSON shape object) and selected item (text) back to the canvas to propogate it back to the constraints canvas
    let locked = this.state.locked;
    let prevented = this.state.prevented;
    let domain = this.state.action.domain; 
    let label = locked ? "" : "Vary"; 
    let propertyLabel = this.getPropertyLabel(); 
    let lockDisabled = this.state.selected == "Vary"; 
    let menuItems = domain.map((key) => {
                    let labelValue = this.toUpperCase(key); 
                    let domainValue = this.getDomainValue(key);
                    return (<Dropdown.Item onClick={this.onSelected.bind(this, domainValue)}>{labelValue}</Dropdown.Item>);
                  }); 
    menuItems.unshift(<Dropdown.Item onClick={this.onSelected.bind(this, "Vary")}>{"Vary"}</Dropdown.Item>); 
    let selectedLabel = this.getSelectedValue(this.state.selected); 
    
    // Lock -> 
    return (<div className="feedback-container-toggle">
              <label className="feedback-container-label">{propertyLabel}</label>
              <Dropdown>
                <Dropdown.Toggle id="dropdown-basic">
                  {this.toUpperCase(selectedLabel)}
                </Dropdown.Toggle>
                <Dropdown.Menu> 
                  {menuItems} 
                </Dropdown.Menu>
              </Dropdown>
              <div className="feedback-container-locks">
                <span className={"glyphicon glyphicon-lock " + (locked ? "locked " : "unlocked ")  + (lockDisabled ? "disabled" : "enabled")}
                  onClick={(!lockDisabled ? this.onLocked : undefined)}></span>
                <span className={"glyphicon glyphicon-remove " + (prevented ? "locked " : "unlocked ") + (lockDisabled ? "disabled" : "enabled")}
                  onClick={(!lockDisabled ? this.onPrevented : undefined)}></span>
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

  getGroupFeedbackItems = () => {
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
        let action = {}; 
        action.keep = ConstraintActions.groupConstraints['keep']; 
        action.prevent = ConstraintActions.groupConstraints['prevent'];
        action.domain = ConstraintActions.groupConstraints.domains[key];
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
  }

  getCanvasFeedbackItems = () => {
    let feedbackItems = []; 
    let shape = this.props.selectedElement; 

    if(shape.type == "canvas") {
      // Dropdown for each 
      let canvasVariableSelectors = ConstraintActions.canvasConstraints.values.map((key) => {
        let action = {}; 
        action.keep = ConstraintActions.canvasConstraints['keep']; 
        action.prevent = ConstraintActions.canvasConstraints['prevent'];
        action.domain = ConstraintActions.canvasConstraints.domains[key];     
        return (<FeedbackItem onClick={this.props.onClick} 
                  action={action}
                  shape={this.props.selectedElement} 
                  property={key}
                  update={this.props.updateConstraintsCanvas}
                  key={key} />);
      }); 

      feedbackItems.push(canvasVariableSelectors); 
    }

    return feedbackItems;
  }

  render () {
    let treeFeedbackItems = this.props.selectedElement ? this.getTreeFeedbackItems() : undefined; 
    let groupFeedbackItems = this.props.selectedElement ? this.getGroupFeedbackItems() : undefined; 
    let canvasFeedbackItems = this.props.selectedElement ? this.getCanvasFeedbackItems() : undefined; 
    return (
        <div className="panel panel-primary feedback-container">
          <div className="panel-heading"> 
            <h3 className="panel-title">Feedback
            </h3>
          </div>
          <div tabIndex="1" className="panel-body"> 
            {treeFeedbackItems}
            {groupFeedbackItems && groupFeedbackItems.length ? <hr className="feedback-container-separator" /> : undefined}
            {groupFeedbackItems}
            {canvasFeedbackItems && canvasFeedbackItems.length ? <hr className="feedback-container-separator" /> : undefined}
            {canvasFeedbackItems}
            {!this.props.selectedElement ? 
              (<div className="card card-body bg-light feedback-container-alert">
                <span className="feedback-container-empty">Select an element in the Outline Panel or in a Design to see feedback options.</span>
              </div>) : undefined}
          </div>  
      </div>); 
  }
}
