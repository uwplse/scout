class Constants {
	static designCanvasScalingFactor() {
		return 0.5; 
	}

  static controlWidths(controlType) {
    let values = {
      'page': 239,
    }

    if(controlType in values) {
      return values[controlType]; 
    }

    return 0; 
  }

  static controlHeights(controlType) {
    let values = {
      'page': 46.5,
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

