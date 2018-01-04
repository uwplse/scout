// App.jsx
import React from "react";
export default class App extends React.Component {

  componentDidMount() {
	$.get('/get_elements', 
		function (data) {
			console.log(data); 
		}
	);
  }

  render () {
    return <p> Hello React!</p>;
  }
}
