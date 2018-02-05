# Finding the 64-dimensional vector for a UI

First find the index of UI's name in the "ui_names" array in the ui_names.json file. Then, load the 2-D array in ui_vectors.npy and take the slice at that index along the first dimension. For example the UI "20353.png" is at index 2. Therefore, its 64-dimensional vector can be obtained by "ui_vectors[2,:]" in Python.