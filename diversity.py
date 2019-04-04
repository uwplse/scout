import numpy as np
import matplotlib 
matplotlib.use('TkAgg')
from PIL import Image
import imagehash
import matplotlib.pyplot as plt

from skimage import data, img_as_float, io
from skimage.measure import compare_ssim as ssim
from skimage.color import rgb2gray
import sys 

def mse(x, y):
    return np.linalg.norm(x - y)

def compute_diversity(): 
	arg1 = sys.argv[1] 
	arg2 = sys.argv[2]
	arg3 = sys.argv [3] 

	img1 = io.imread(arg1)
	img2 = io.imread(arg2)
	img3 = io.imread(arg3)

	img1 = rgb2gray(img1)
	img2 = rgb2gray(img2)
	img3 = rgb2gray(img3)

	img1 = img_as_float(img1)
	img2 = img_as_float(img2)
	img3 = img_as_float(img3)

	fig, axes = plt.subplots(nrows=1, ncols=3, figsize=(10, 4),
	                         sharex=True, sharey=True)
	ax = axes.ravel()

	mse_p1 = mse(img1, img2)
	ssim_p1 = ssim(img1, img2, data_range=img3.max() - img3.min())

	mse_p2 = mse(img1, img3)
	ssim_p2 = ssim(img1, img3, data_range=img2.max() - img2.min())

	mse_p3 = mse(img3, img2)
	ssim_p3 = ssim(img3, img2, data_range=img2.max() - img2.min())

	label = 'MSE: {:.2f}, SSIM: {:.2f}'

	ax[0].imshow(img1, cmap=plt.cm.gray, vmin=0, vmax=1)
	ax[0].set_xlabel(label.format(mse_p1, ssim_p1))
	ax[0].set_title('1,2')

	ax[1].imshow(img2, cmap=plt.cm.gray, vmin=0, vmax=1)
	ax[1].set_xlabel(label.format(mse_p3, ssim_p3))
	ax[1].set_title('2,3')

	ax[2].imshow(img3, cmap=plt.cm.gray, vmin=0, vmax=1)
	ax[2].set_xlabel(label.format(mse_p2, ssim_p2))
	ax[2].set_title('1,3')

	plt.tight_layout()
	plt.show()

def compute_image_hashes(): 
	arg1 = sys.argv[1] 
	arg2 = sys.argv[2]
	arg3 = sys.argv [3] 

	img1 = Image.open(arg1)
	img2 = Image.open(arg2)
	img3 = Image.open(arg3)

	hash1 = imagehash.average_hash(img1)
	hash2 = imagehash.average_hash(img2)
	hash3 = imagehash.average_hash(img3)

	print('1:3')
	print(hash1 - hash3)

	print('2:3')
	print(hash2 - hash3)

	print('1:2')
	print(hash1 - hash2)



if __name__ == "__main__":
	compute_image_hashes()