class Constants {
	static designCanvasScalingFactor() {
		return 0.5; 
	}

  static controlWidths(controlType) {
    let values = {
      'button': 288,
      'orangeButton': 288, 
      'field': 288, 
      'search': 288, 
      'group': 238, 
      'page': 238,
      'labelGroup': 238, 
      'label': 84, 
      'orangeLabel': 83,
      'smallLabel': 50, 
      'multilineLabel': 130, 
      'image': 80, 
      'image2': 80,
      'image3': 80,
      'logo': 80,
      'logo2': 80,
      'placeholder': 80
    }

    if(controlType in values) {
      return values[controlType]; 
    }

    return 0; 
  }

  static controlHeights(controlType) {
    let values = {
      'button':40,
      'orangeButton': 40, 
      'orderLabel': 43,
      'field': 34, 
      'search': 34, 
      'group': 50, 
      'page': 50,
      'labelGroup': 50, 
      'label': 30,
      'orangeLabel': 30, 
      'smallLabel': 18, 
      'image': 80, 
      'image2': 80,
      'image3': 80,
      'logo': 80,
      'logo2': 80,
      'placeholder': 80, 
      'multilineLabel': 40
    }

    if(controlType in values) {
      return values[controlType]; 
    }

    return 0; 
  }

  static controlLabels(controlType) {
    let values = {
      'button': 'Button', 
      'label': 'Label', 
      'orangeLabel': 'Label',
      'field': 'Field', 
      'search': 'Search', 
      'group': 'Group', 
      'labelGroup': 'Label', 
      'smallLabel': 'Label', 
      'image': 'image'
    }
    return values[controlType]; 
  }; 

  static controlFontSizes(controlType) {
    let values = {
      'label': 36, 
      'orangeLabel': 36,
      'multilineLabel': 14, 
      'smallLabel': 20
    }
    return values[controlType];
  }
}

export default Constants; 

