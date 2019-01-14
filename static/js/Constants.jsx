class Constants {
	static designCanvasScalingFactor() {
		return 0.5; 
	}

  static controlWidths(controlType) {
    let values = {
      'group': 238, 
      'labelGroup': 238, 
      'page': 239,
      'labelGroup': 238, 
    }

    if(controlType in values) {
      return values[controlType]; 
    }

    return 0; 
  }

  static controlHeights(controlType) {
    let values = {
      'group': 50, 
      'labelGroup': 50,
      'page': 46.5,
      'labelGroup': 50, 
    }

    if(controlType in values) {
      return values[controlType]; 
    }

    return 0; 
  }

  static controlFontSizes(controlType) {
    let values = {
      'text': 36
    }
    return values[controlType];
  }
}

export default Constants; 

