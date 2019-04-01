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
      selected: props.selected, 
      locked: false,
      prevented: false, 
      canvasShape: props.canvasShape, 
      primarySelection: props.primarySelection, 
      linkedShapes: props.linkedShapes,
      property: props.property, 
      action: props.action
    }; 
  }

  componentDidMount() {
    // If the canvasShape is defined, this means the design canvas shape should be the primary selection
    let useDesignShapeAsPrimary = this.state.canvasShape ? true : false; 

    let selectedValue = this.state.selected; 
    let locked = FeedbackItem.getInitialLocked(this.state.canvasShape, this.state.property, selectedValue); 
    let prevented = FeedbackItem.getInitialPrevented(this.state.canvasShape, this.state.property, selectedValue); 
    this.setState({
      selected: selectedValue, 
      prevented: prevented, 
      locked: locked
    }); 
  }

  static getDerivedStateFromProps(nextProps, prevState) {
    let canvShape = nextProps.canvasShape ? nextProps.canvasShape : nextProps.primarySelection; 
    let initialLocked = FeedbackItem.getInitialLocked(canvShape, nextProps.property, nextProps.selected); 
    let initialPrevented = FeedbackItem.getInitialPrevented(canvShape, nextProps.property, nextProps.selected);

    return {
      canvasShape: nextProps.canvasShape,
      primarySelection: nextProps.primarySelection,
      linkedShapes: nextProps.linkedShapes, 
      action: nextProps.action, 
      property: nextProps.property, 
      selected: nextProps.selected,
      locked: initialLocked, 
      prevented: initialPrevented
    };     
  }

  static getInitialPrevented(shape, property, value) {
    if(shape.prevents && shape.prevents.length && shape.prevents.indexOf(property) > -1) {
      if(shape["prevented_values"][property] && shape["prevented_values"][property].length 
        && shape["prevented_values"][property].indexOf(value) > -1) {
        return true; 
      }
    }

    return false;
  }

  static getInitialLocked(shape, property, value) {
    if(shape.locks && shape.locks.length && shape.locks.indexOf(property) > -1) {
      if(shape["locked_values"][property] && shape["locked_values"][property].length 
        && shape["locked_values"][property].indexOf(value) > -1) {
        return true; 
      }
    }

    return false;
  }

  onSelected = (newValue) => {
    this.props.setSelectedValue(this.props.id, newValue); 
  }

  onLocked = () => {
    let canvasShape = this.state.canvasShape ? this.state.canvasShape : this.state.primarySelection; 
    let preventValue = this.state.prevented; 
    let keepOrPrevent = ""; 
    if(this.state.prevented) {
      // If the property was already "Kept", remove it and keep the Prevent instead
      this.state.action['prevent']['undo'].updateConstraintsCanvasShape(this.state.property, canvasShape, this.state.selected);
      preventValue = false;

      // If there are any linkedShapes, we should also update their feedback as well 
      for(let i=0; i<this.state.linkedShapes.length; i++) {
        this.state.action['prevent']['undo'].updateConstraintsCanvasShape(this.state.property, this.state.linkedShapes[i], this.state.selected);      
      }
    }

    if(this.state.locked){
      this.state.action['keep']['undo'].updateConstraintsCanvasShape(this.state.property, canvasShape, this.state.selected); 

      // If there are any linkedShapes, we should also update their feedback as well 
      for(let i=0; i<this.state.linkedShapes.length; i++) {
        this.state.action['keep']['undo'].updateConstraintsCanvasShape(this.state.property, this.state.linkedShapes[i], this.state.selected);      
      }   
    }
    else {
      // Notify the PageContainer that a keep was performed so it can reflow the invalid solutions
      keepOrPrevent = "keep"; 

      this.state.action['keep']['do'].updateConstraintsCanvasShape(this.state.property, canvasShape, this.state.selected); 

      // If there are any linkedShapes, we should also update their feedback as well 
      for(let i=0; i<this.state.linkedShapes.length; i++) {
        this.state.action['keep']['do'].updateConstraintsCanvasShape(this.state.property, this.state.linkedShapes[i], this.state.selected);      
      }    
    }

    this.setState({
      locked: !this.state.locked, 
      prevented: preventValue
    });

    // Notify the ConstraintsCanvas tree of the update
    this.props.update(canvasShape, this.state.property, this.state.selected, keepOrPrevent);
    this.props.locksUpdated();
  }

  onPrevented = () => {
    let canvasShape = this.state.canvasShape ? this.state.canvasShape : this.state.primarySelection; 
    let lockedValue = this.state.locked; 
    let keepOrPrevent = ""; 

    if(this.state.locked) {
      // If the property was already "Kept", remove it and keep the Prevent instead
      this.state.action['keep']['undo'].updateConstraintsCanvasShape(this.state.property, canvasShape, this.state.selected);
      lockedValue = false;

      // If there are any linkedShapes, we should also update their feedback as well 
      for(let i=0; i<this.state.linkedShapes.length; i++) {
        this.state.action['keep']['undo'].updateConstraintsCanvasShape(this.state.property, this.state.linkedShapes[i], this.state.selected);      
      }
    }

    if(this.state.prevented) {
      this.state.action['prevent']['undo'].updateConstraintsCanvasShape(this.state.property, canvasShape, this.state.selected);

      // If there are any linkedShapes, we should also update their feedback as well 
      for(let i=0; i<this.state.linkedShapes.length; i++) {
        this.state.action['prevent']['undo'].updateConstraintsCanvasShape(this.state.property, this.state.linkedShapes[i], this.state.selected);      
      }
    } else {
      keepOrPrevent = "prevent"; 

      this.state.action['prevent']['do'].updateConstraintsCanvasShape(this.state.property, canvasShape, this.state.selected); 

      // If there are any linkedShapes, we should also update their feedback as well 
      for(let i=0; i<this.state.linkedShapes.length; i++) {
        this.state.action['prevent']['do'].updateConstraintsCanvasShape(this.state.property, this.state.linkedShapes[i], this.state.selected);      
      }
    }

    this.setState({
      prevented: !this.state.prevented, 
      locked: lockedValue
    });

    // Notify the ConstraintsCanvas tree of the update
    this.props.update(canvasShape, this.state.property, this.state.selected, keepOrPrevent);
    this.props.preventsUpdated();
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
    let preventDisabled = this.state.selected == "Vary" || domain.length == 1; // If there is only one potential value left in the domain, do not allow preventing that value. 
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
                <Dropdown.Toggle disabled={(locked || prevented)} id="dropdown-basic">
                  {this.toUpperCase(selectedLabel)}
                </Dropdown.Toggle>
                <Dropdown.Menu className="scrollable-menu"> 
                  {menuItems} 
                </Dropdown.Menu>
              </Dropdown>
              <div className="feedback-container-locks">
                <span className={"glyphicon glyphicon-lock " + (locked ? "locked " : "unlocked ")  + (lockDisabled ? "disabled" : "enabled")}
                  onClick={(!lockDisabled ? this.onLocked : undefined)}></span>
                <span className={"glyphicon glyphicon-remove " + (prevented ? "locked " : "unlocked ") + (preventDisabled ? "disabled" : "enabled")}
                  onClick={(!preventDisabled ? this.onPrevented : undefined)}></span>
              </div> 
            </div>);
  }
}

class ContainerOrderFeedback extends React.Component {
  constructor(props) {
    super(props); 

    this.state = {
      linkedSiblings: props.siblings, 
      currentOrderValue: props.currentOrderValue
    }
  }

  onToggle = () => {
    let newOrder = this.state.currentOrderValue == "important" ? "unimportant" : "important"; 
    this.setState({
      currentOrderValue: newOrder
    }); 

    this.props.onClick(newOrder, this.state.linkedSiblings);
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
      importanceLevel: props.currentImportance, 
      linkedSiblings: props.siblings
    }; 
  }

  onClick = (newImportanceLevel) => {
    this.setState({
      importanceLevel: newImportanceLevel
    }); 

    // If the shape has corresponding siblings, the importance should be 
    // changed on them as well (Item Groups)
    this.props.onClick(newImportanceLevel, this.state.linkedSiblings); 
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
    
    this.state = {
      activeCanvasShape: props.activeCanvasShape, 
      primarySelection: props.primarySelection, 
      feedbackCallbacks: props.feedbackCallbacks, 
      groupFeedbackItems: [], 
      canvasChildFeedbackItems: [],
      elementFeedbackItems: [],
      canvasFeedbackItems: [],
      feedbackItemMap: {}
    } 
  }

  static getDerivedStateFromProps(nextProps, prevState) {
    let canvasShapeChanged = nextProps.activeCanvasShape != prevState.activeCanvasShape; 
    let primarySelectionChanged = nextProps.primarySelection != prevState.primarySelection; 

    let initializeFeedback = canvasShapeChanged || primarySelectionChanged; 
    let canvasShape = nextProps.activeCanvasShape ? nextProps.activeCanvasShape : nextProps.primarySelection; 
    let designShape = nextProps.activeCanvasShape ? nextProps.primarySelection : undefined; 

    let newGroupFeedback = canvasShape ? FeedbackContainer.getGroupFeedbackItems(canvasShape, designShape, nextProps.feedbackCallbacks) : []; 
    let newCanvasChildFeedback = canvasShape ? FeedbackContainer.getCanvasChildFeedbackItems(canvasShape,  designShape, nextProps.feedbackCallbacks) : [];
    let newElementFeedback = canvasShape ? FeedbackContainer.getElementFeedbackItems(canvasShape,  designShape, nextProps.feedbackCallbacks) : [];
    let newCanvasFeedback = canvasShape ? FeedbackContainer.getCanvasFeedbackItems(canvasShape,  designShape) : [];  
    return {
      activeCanvasShape: nextProps.activeCanvasShape, 
      primarySelection: nextProps.primarySelection, 
      feedbackCallbacks: nextProps.feedbackCallbacks, 
      groupFeedbackItems:  initializeFeedback || newGroupFeedback.length != prevState.groupFeedbackItems.length ? newGroupFeedback : prevState.groupFeedbackItems, 
      canvasChildFeedbackItems: initializeFeedback  || newCanvasChildFeedback.length != prevState.canvasChildFeedbackItems.length ? newCanvasChildFeedback : prevState.canvasChildFeedbackItems,
      elementFeedbackItems: initializeFeedback || newElementFeedback.length != prevState.elementFeedbackItems.length ? newElementFeedback : prevState.elementFeedbackItems,
      canvasFeedbackItems: initializeFeedback || newCanvasFeedback.length != prevState.canvasFeedbackItems.length ? newCanvasFeedback : prevState.canvasFeedbackItems,
      feedbackItemMap: prevState.feedbackItemMap
    };     
  }

  static getDesignSelected(shape, property) {
    let value = shape[property]; 
    if(value != undefined) {
      return value; 
    }

    return "Vary";
  }

  static getFeedbackItemsFromShape(canvasShape, designShape, key, linkedShapes=[]) {
    let feedbackItems = []; 

    // Display another selector for the Vary option 
    let selectedValue = "Vary";
    let useDesignShape = false;
    let addVaryOption = true; 
    if(designShape) {
      useDesignShape = true;
      selectedValue = FeedbackContainer.getDesignSelected(designShape, key); 
    }

    if(canvasShape.locks && canvasShape.locks.length) {
      let lockedIndex = canvasShape.locks.indexOf(key); 
      if(lockedIndex > -1) {
        let lockedValues = canvasShape["locked_values"][key]; 

        if(useDesignShape && lockedValues.indexOf(selectedValue) > -1) {
          addVaryOption = false;
        }

        for(let k=0; k<lockedValues.length; k++) {
          let value = lockedValues[k]; 
          let feedbackItem = {
            id: _.uniqueId(), 
            key: key, 
            selectedValue: value, 
            linkedShapes: linkedShapes
          }; 
          feedbackItems.push(feedbackItem); 
        }
      }
    }

    if(canvasShape.prevents && canvasShape.prevents.length) {
      let preventedIndex = canvasShape.prevents.indexOf(key); 
      if(preventedIndex > -1) {
        let preventedValues = canvasShape["prevented_values"][key]; 

        if(useDesignShape && preventedValues.indexOf(selectedValue) > -1) {
          addVaryOption = false;
        }

        for(let k=0; k<preventedValues.length; k++) {
          let value = preventedValues[k]; 
          let feedbackItem = {
            id: _.uniqueId(), 
            key: key, 
            selectedValue: value, 
            linkedShapes: linkedShapes                                  
          };                                              

          feedbackItems.push(feedbackItem); 
        }
      }
    } 

    if(addVaryOption) {
      let feedbackItem = {
        id: _.uniqueId(), 
        key: key, 
        selectedValue: selectedValue, 
        linkedShapes: linkedShapes
      }; 

      feedbackItems.push(feedbackItem); 
    }

    return feedbackItems; 
  }

  static getCanvasChildFeedbackItems(canvasShape, designShape, callbacks) {
    let feedbackItems = []; 
    if(callbacks && callbacks.getCurrentParentNode) {
      let parentNode = callbacks.getCurrentParentNode(canvasShape.name); 
      let isCanvasChild = parentNode.type == "canvas"; 
      if(isCanvasChild){    // Dropdown for each 
        for(let i=0; i<ConstraintActions.canvasChildConstraints.values.length; i++) {
          let key = ConstraintActions.canvasChildConstraints.values[i]; 
          let items = FeedbackContainer.getFeedbackItemsFromShape(canvasShape, designShape, key); 
          feedbackItems.push(...items);
        }
      }
    }

    return feedbackItems; 
  }

  static getGroupFeedbackItems(canvasShape, designShape, callbacks) {
    let feedbackItems = []
    if(canvasShape && canvasShape.type == "group" && !canvasShape.alternate) {
      let linkedSiblings = []
      if(callbacks && callbacks.getCurrentShapeSiblings) {
        if(canvasShape.item) {
          // Gets the siblings of this shape so that we 
          // can also apply the feedback to them
          linkedSiblings = callbacks.getCurrentShapeSiblings(canvasShape.name); 
        }
      }

      // Dropdown for each 
      for(let i=0; i<ConstraintActions.groupConstraints.values.length; i++) {
        let key = ConstraintActions.groupConstraints.values[i]; 
        let items = FeedbackContainer.getFeedbackItemsFromShape(canvasShape, designShape, key, linkedSiblings); 
        feedbackItems.push(...items);
      }      
    }

    return feedbackItems;
  }

  static getElementFeedbackItems(canvasShape, designShape, callbacks) {
    let feedbackItems = []; 

    if(callbacks && callbacks.getCurrentParentNode) {
      let parentNode = callbacks.getCurrentParentNode(canvasShape.name); 
      let isCanvasChild = parentNode.type == "canvas"; 
      let isAlternateChild = parentNode.alternate; // For alternate group children, we won't let the position be fixed on the sub elements. 
      if(!isAlternateChild) {
        // Dropdown for each 
        for(let i=0; i<ConstraintActions.elementConstraints.values.length; i++) {
          let key = ConstraintActions.elementConstraints.values[i]; 
          let items = FeedbackContainer.getFeedbackItemsFromShape(canvasShape, designShape, key);

          for(let j=0; j<items.length; j++) {
            let item = items[j]; 
            let pushItem = (item.key == "x" || item.key == "y") && isCanvasChild ? false : true; 
            if(pushItem) {
              feedbackItems.push(item); 
            }
          }
        } 
      }
    }

    return feedbackItems;
  }

  static getCanvasFeedbackItems(canvasShape, designShape) {
    let feedbackItems = []; 
    if(canvasShape && canvasShape.type == "canvas") {
      // Dropdown for each 
      for(let i=0; i<ConstraintActions.canvasConstraints.values.length; i++) {
        let key = ConstraintActions.canvasConstraints.values[i]; 
        let items = FeedbackContainer.getFeedbackItemsFromShape(canvasShape, designShape, key); 
        feedbackItems.push(...items);
      }   
    }

    return feedbackItems;
  }

  getTreeFeedbackItems = () => {
    let feedbackItems = []; 
    let shape = this.state.activeCanvasShape ? this.state.activeCanvasShape : this.state.primarySelection; 
    let callbacks = this.state.feedbackCallbacks; 

    let linkedSiblings = []; 
    if(shape.item) {
      linkedSiblings = callbacks.getCurrentShapeSiblings(shape.name); 
    }

    if(callbacks && callbacks.setContainerOrder) {
      feedbackItems.push(
        <ContainerOrderFeedback 
          siblings={linkedSiblings}
          currentOrderValue={shape.containerOrder}
          onClick={callbacks.setContainerOrder} />); 
    }

    if(callbacks && callbacks.setOrder) {
      let shapeIndex = callbacks.getCurrentShapeIndex(shape.name); 
      let siblings = callbacks.getCurrentShapeSiblings(shape.name); 
      let numChildren = siblings.length + 1; 
      let showOrderMenuItem = shapeIndex == 0 || shapeIndex == numChildren - 1; 
      if(showOrderMenuItem) {
        feedbackItems.push(<OrderFeedback 
          index={shapeIndex} currentOrder={shape.order} onClick={callbacks.setOrder} />); 
      }
    }

    if(callbacks && callbacks.setImportanceLevel) {
        feedbackItems.push(
          <ImportanceFeedback
            siblings={linkedSiblings}
            currentImportance={shape.importance}
            onClick={callbacks.setImportanceLevel} />); 
    }

    return feedbackItems; 
  }

  getFeedbackItem = (id, key, value, action, linkedShapes=[]) => {    
    let itemKey = _.uniqueId();  
    let canvasShape = this.state.activeCanvasShape ? this.state.activeCanvasShape : this.state.primarySelection; 
    let designShape = this.state.activeCanvasShape ? this.state.primarySelection : undefined;    
    return <FeedbackItem onClick={this.props.onClick} 
              action={action}
              canvasShape={canvasShape} 
              designShape={designShape}
              linkedShapes={linkedShapes}
              setSelectedValue={this.setSelectedValue}
              locksUpdated={this.locksUpdated}
              preventsUpdated={this.preventsUpdated}
              property={key}
              update={this.props.updateConstraintsCanvas}
              selected={value}
              id={id}
              key={itemKey} />;  
  }

  onClick = (evt) => {
    // prevent the event from escaping the FeedbackContaer
    // so that the active selections will not be deactivated 
    evt.stopPropagation();
  }

  setSelectedValue = (id, value) => {
    let feedbackItem = this.state.feedbackItemMap[id]; 
    feedbackItem.selectedValue = value; 

    this.setState({
      groupFeedbackItems: this.state.groupFeedbackItems, 
      canvasChildFeedbackItems: this.state.canvasChildFeedbackItems, 
      elementFeedbackItems: this.state.elementFeedbackItems, 
      canvasFeedbackItems: this.state.canvasFeedbackItems
    }); 
  }

  reininitializeFeedbackItems = () => {
    let canvasShape = this.state.activeCanvasShape ? this.state.activeCanvasShape : this.state.primarySelection;
    let designShape = this.state.activeCanvasShape ? this.state.primarySelection : undefined;  
    let groupFeedbackItems = FeedbackContainer.getGroupFeedbackItems(canvasShape, designShape, this.state.feedbackCallbacks); 
    let canvasChildFeedbackItems = FeedbackContainer.getCanvasChildFeedbackItems(canvasShape, designShape, this.state.feedbackCallbacks);
    let elementFeedbackItems = FeedbackContainer.getElementFeedbackItems(canvasShape, designShape, this.state.feedbackCallbacks);
    let canvasFeedbackItems = FeedbackContainer.getCanvasFeedbackItems(canvasShape, designShape); 
    this.setState({
      groupFeedbackItems: groupFeedbackItems, 
      canvasChildFeedbackItems: canvasChildFeedbackItems, 
      elementFeedbackItems: elementFeedbackItems, 
      canvasFeedbackItems: canvasFeedbackItems
    }); 
  }

  locksUpdated = () => {
    this.reininitializeFeedbackItems();
  }

  preventsUpdated = () => {
    this.reininitializeFeedbackItems();
  }

  render () {
    let treeFeedbackItems = this.props.primarySelection && this.state.feedbackCallbacks ? this.getTreeFeedbackItems() : undefined; 
    let canvasShape = this.state.activeCanvasShape ? this.state.activeCanvasShape : this.state.primarySelection; 
    let designShape = this.state.activeCanvasShape ? this.state.primarySelection : undefined; 

    let canvasFeedbackItems = canvasShape ? this.state.canvasFeedbackItems.map((item) => {
      let action = {}; 
      action.keep = ConstraintActions.canvasConstraints['keep']; 
      action.prevent = ConstraintActions.canvasConstraints['prevent'];
      action.domain = ConstraintActions.canvasConstraints.domains[item.key];

      if(typeof action.domain == "function") {
        action.domain = action.domain(canvasShape); 
      }

      let fbItem = this.getFeedbackItem(item.id, item.key, item.selectedValue, action); 

      this.state.feedbackItemMap[item.id] = item; 
      return fbItem; 
    }) : undefined; 

    let groupFeedbackItems = canvasShape ? this.state.groupFeedbackItems.map((item) => {
      let action = {}; 
      action.keep = ConstraintActions.groupConstraints['keep']; 
      action.prevent = ConstraintActions.groupConstraints['prevent'];
      action.domain = ConstraintActions.groupConstraints.domains[item.key];

      if(typeof action.domain == "function") {
        action.domain = action.domain(canvasShape); 
      }

      let fbItem = this.getFeedbackItem(item.id, item.key, item.selectedValue, action, item.linkedShapes); 

      this.state.feedbackItemMap[item.id] = item; 
      return fbItem; 
    }) : undefined; 

    let canvasChildItems = canvasShape ? this.state.canvasChildFeedbackItems.map((item) => {
      let action = {}; 
      action.keep = ConstraintActions.canvasChildConstraints['keep']; 
      action.prevent = ConstraintActions.canvasChildConstraints['prevent'];
      action.domain = ConstraintActions.canvasChildConstraints.domains[item.key];

      let fbItem = this.getFeedbackItem(item.id, item.key, item.selectedValue, action); 
      this.state.feedbackItemMap[item.id] = item; 
      return fbItem; 
    }) : undefined; 

    let elementFeedbackItems = canvasShape ? this.state.elementFeedbackItems.map((item) => {
      let action = {}; 
      action.keep = ConstraintActions.elementConstraints['keep']; 
      action.prevent = ConstraintActions.elementConstraints['prevent'];

      if(item.key == "height" || item.key == "width") {
        action.domain = ConstraintActions.elementConstraints.domains["size"](canvasShape)[item.key]; 
      }
      else {
        // For X, Y, if activated by a design shape, the computed value should be in the dropdown
        // Otherwise, only show the "Vary" as it doesn't make sense to give htem 
        // A selction for absolute x,y from the canvas node. 
        if(designShape) {
          action.domain = [designShape[item.key]]; 
        }
        else {
          action.domain = []; 
        }
      }

      let fbItem = this.getFeedbackItem(item.id, item.key, item.selectedValue, action); 
      this.state.feedbackItemMap[item.id] = item; 
      return fbItem; 
    }) : undefined; 

    return (
        <div className="panel panel-primary feedback-container">
          <div className="panel-heading"> 
            <h3 className="panel-title">Feedback
            </h3>
          </div>
          <div tabIndex="1" className="panel-body feedback-container-body"
            onClick={this.onClick}> 
            {treeFeedbackItems}
            {elementFeedbackItems && elementFeedbackItems.length ? <hr className="feedback-container-separator" /> : undefined}
            {elementFeedbackItems}
            {canvasChildItems && canvasChildItems.length ? <hr className="feedback-container-separator" /> : undefined}
            {canvasChildItems}
            {groupFeedbackItems && groupFeedbackItems.length ? <hr className="feedback-container-separator" /> : undefined}
            {groupFeedbackItems}
            {canvasFeedbackItems && canvasFeedbackItems.length ? <hr className="feedback-container-separator" /> : undefined}
            {canvasFeedbackItems}
            {!canvasShape || !this.state.feedbackCallbacks ? 
              (<div className="card card-body bg-light feedback-container-alert">
                <span className="feedback-container-empty">Select an element in the Outline Panel or in a layout idea canvas to the right to see feedback options.</span>
              </div>) : undefined}
          </div>  
      </div>); 
  }
}
