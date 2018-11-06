class Constants {
	static designCanvasScalingFactor() {
		return 0.5; 
	}

  static controlWidths(controlType) {
    let values = {
      'group': 238, 
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
      'page': 46.5,
      'labelGroup': 50, 
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
      'smallLabel': 20, 
      'smallLabel2': 20 
    }
    return values[controlType];
  }
}

export default Constants; 

