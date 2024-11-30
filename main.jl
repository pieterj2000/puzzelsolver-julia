using Images, FileIO, ImageTransformations, ImageEdgeDetection, TestImages
using ImageEdgeDetection: Percentile

# specify the path to your local image file
img_path = "./1.jpg"
img = load(img_path)
img_grey = Gray.(img)
#imresize(img, 256,256)
alg = Canny(spatial_scale=1, high=Percentile(80), low=Percentile(20))
img_edge = detect_edges(img, alg)
mosaicview(img,img_grey, img_edge,nrow = 1)