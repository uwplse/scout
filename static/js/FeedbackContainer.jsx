// App.jsx
import React from "react";
import '../css/FeedbackContainer.css';

class ContainerOrderFeedback extends React.Component {
  constructor(props) {
    super(props); 

    this.state = {
      currentOrderValue: props.currentOrderValue
    }
  }

  onClick = () => {
    let newOrder = this.state.currentOrderValue == "important" ? "unimportant" : "important"; 
    this.setState({
      currentOrderValue: newOrder
    }); 

    this.props.onClick(newOrder);
  }

  render () {
    let checked = this.state.currentOrderValue == "important"; 
    let label = "Order " + (this.state.currentOrderValue == "important" ? "Important." : "Unimportant."); 
    return (<div class="custom-control custom-switch">
                <input type="checkbox" class="custom-control-input" id="customSwitch1" 
                  checked={checked} onClick={this.onClick} />
                <label class="custom-control-label" for="customSwitch1">{label}</label>
            </div>);   
  }
}

class OrderFeedback extends React.Component {
  constructor(props) {
    super(props); 
  }

  // static getDerivedStateFromProps(nextProps, prevState) {
  //   return {
  //     height: nextProps.index,  
  //   }    
  // }
  render () {
    let orderPosition = this.props.index == 0 ? "first" : "last"; 

    let ordered = (this.props.currentOrder != -1 || this.props.currentOrder != undefined); 
    let label = "Keep " + orderPosition + "."; 
    let newOrder = (ordered ? this.props.index : -1); 

    return (<div class="custom-control custom-switch">
              <input type="checkbox" class="custom-control-input" 
                id="customSwitch1" checked={ordered} 
                onClick={() => this.props.onClick(newOrder)} />
              <label class="custom-control-label" for="customSwitch1">{label}</label>
            </div>); 
  }
}

class ImportanceFeedback extends React.Component {
  constructor(props) {
    super(props); 
    this.onClick = props.onClick; 
    this.importanceLevel = props.importanceLevel; 
    this.label = (this.importanceLevel == "most" ? "Add more emphasis." : (this.importanceLevel == "least" ? "Add less emphasis." : "Add normal emphasis.")); 
  }

  render () {
    let self = this; 
    return (<div class="custom-control custom-switch">
              <input type="checkbox" class="custom-control-input" 
                id="customSwitch1" checked={ordered} 
                onClick={this.onClick.bind(this, newOrder)} />
              <label class="custom-control-label" for="customSwitch1">{label}</label>
            </div>); 
  }
}

export default class FeedbackContainer extends React.Component {
  constructor(props) {
  	super(props);
  }

  getFeedbackItems = () => {
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

      feedbackItems.push(<OrderFeedback 
        index={shapeIndex} currentOrder={shape.order} onClick={callbacks.setOrder} />); 
    }

    return feedbackItems; 

    // if(callbacks.setImportanceLevel) {

    // }
  }

  render () {
    let feedbackItems = this.getFeedbackItems(); 
    return (
        <div className="panel panel-primary feedback-container">
          <div className="panel-heading"> 
            <h3 className="panel-title">Feedback
            </h3>
          </div>
          <div tabIndex="1" className="panel-body"> 
            {feedbackItems}
          </div>  
      </div>); 
  }
}
