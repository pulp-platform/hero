############################ OpenMP Sources ############################
ROOT := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

# Add new library for DMA calls
INCPATHS += -I$(HERO_INSTALL)/../openmp-examples/polybench-acc/common
LIBPATHS += -L$(HERO_INSTALL)/../openmp-examples/polybench-acc/common

CSRCS :=  activation_layer.c  cuda.c  layer.c  region_layer.c  activations.c  data.c  list.c  reorg_layer.c  avgpool_layer.c  deconvolutional_layer.c  local_layer.c  rnn_layer.c  batchnorm_layer.c  demo.c  logistic_layer.c  route_layer.c  blas.c  detection_layer.c  lstm_layer.c  shortcut_layer.c  box.c  dropout_layer.c  main.c  softmax_layer.c  col2im.c  gemm.c  matrix.c  tree.c  connected_layer.c  gru_layer.c  maxpool_layer.c  upsample_layer.c  convolutional_layer.c  im2col.c  network.c  utils.c  cost_layer.c  image.c  normalization_layer.c  yolo_layer.c  crnn_layer.c  iseg_layer.c  option_list.c  crop_layer.c  l2norm_layer.c  parser.c
EXE=darknet
LDFLAGS=-lm -ldmatransfer
CFLAGS+= -fopenmp -fintegrated-as

clean::
	-rm -vf darknet __hmpp* $(EXE) *~ *.dis *.ll *.slm
	-rm -rvf $(DEPDIR)

-include $(ROOT)/../common/default.mk

