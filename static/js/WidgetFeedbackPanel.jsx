// App.jsx
import React from "react";

export default class WidgetFeedbackPanel extends React.Component {
  constructor(props) {
  	super(props);

    this.state = {
      selectedElement: props.selectedElement, 
      selectedElementY: props.selectedElementY, 
      containerY: 0
    }
  }

  static getDerivedStateFromProps(nextProps, prevState) {
    return {
      selectedElement: nextProps.selectedElement, 
      selectedElementY: nextProps.selectedElementY
    }    
  }

  componentDidMount() {
    // Measure the top of the container to place the selected feedback panel in relation to 
    let container = document.getElementsByClassName('constraints-canvas-feedback-container'); 
    if(container && container.length) {
      container = container[0]; 
      let containerRect = container.getBoundingClientRect();
      this.setState({
        containerY: containerRect.top
      }); 
    }
  }

  setImportanceLevel(evt, level) {
    evt.stopPropagation(); 

    // Update the object
    this.state.selectedElement.importance = level; 

    this.setState({
      selectedElement: this.state.selectedElement
    }); 

    this.props.updateTreeAndCheckValidity();
  }

  setOrder(evt, value) {
    evt.stopPropagation(); 

    this.state.selectedElement.order = value; 

    this.setState({
      selectedElement: this.state.selectedElement
    }); 

    this.props.checkSolutionValidity();      
  }

  setContainerOrder(evt, orderValue) {
    evt.stopPropagation(); 

    this.state.selectedElement.containerOrder = orderValue; 

    this.setState({
      selectedElement: this.state.selectedElement
    }); 

    this.props.checkSolutionValidity();
  }


  getFeedbackSettings = () => {
    let feedbackSettings = []; 
    if(this.state.selectedElement.type == "text") {
      this.displayRightClickMenu(evt, this.id, {
        setImportanceLevel: this.setImportanceLevel, 
        setOrder: this.setOrder
      }); 


    }
    else if(this.state.selectedElement.type == "group"){
      this.displayRightClickMenu(evt, this.id, {
        setImportanceLevel: this.setImportanceLevel, 
        setOrder: this.setOrder,
        setContainerOrder: this.setContainerOrder
      });     
    }
    else if(this.state.selectedElement.type == "canvas") {
      this.displayRightClickMenu(evt, this.id, {
        setContainerOrder: this.setContainerOrder
      }); 
    }
    else {
      this.displayRightClickMenu(evt, this.id, {
        setImportanceLevel: this.setImportanceLevel, 
        setOrder: this.setOrder
      }); 
    }
  }

  render () {
    return (
      <div 
        style={{
          display: (this.state.selectedElement ? "" : "none"), 
          top: (this.state.selectedElementY - this.state.containerY) + "px"}} 
        className="widget-feedback-panel">
        <div className="checkbox">
          <label>
           <span>Order Important</span> <input type="checkbox" data-on="Yes" data-off="No" checked data-toggle="toggle" />
          </label>
        </div>
        <div className="checkbox">
          <label>
           <span>Keep First</span> <input type="checkbox" data-on="Yes" data-off="No" checked data-toggle="toggle" />
          </label>
        </div>
      </div>); 
  }
}
