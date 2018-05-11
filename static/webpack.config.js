const webpack = require('webpack');
const ExtractTextPlugin = require("extract-text-webpack-plugin");

const config = {
    entry:  {
      app:  __dirname + '/js/index.jsx', 
      import: __dirname + '/js/import.jsx'
    },
    output: {
        path: __dirname + '/dist',
        filename: "[name].js"
    },
    resolve: {
        extensions: ['.js', '.jsx', '.css']
    },
    module: {
	  rules: [
	    {
	      test: /\.jsx?/,
	      exclude: /node_modules/,
	      use: 'babel-loader'
	    }, 
        {
          test: /\.css$/, 
          loader: "style-loader!css-loader" 
        }
	  ]
	}
};

module.exports = config;