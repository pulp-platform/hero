ROOT := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

CSRCS := \
  activation_layer.c \
  activations.c \
  avgpool_layer.c \
  batchnorm_layer.c \
  blas.c \
  box.c \
  col2im.c \
  connected_layer.c \
  convolutional_layer.c \
  cost_layer.c \
  crnn_layer.c \
  crop_layer.c \
  cuda.c \
  data.c \
  deconvolutional_layer.c \
  demo.c \
  detection_layer.c \
  dropout_layer.c \
  gemm.c \
  gru_layer.c \
  hero_perf.c \
  im2col.c \
  image.c \
  iseg_layer.c \
  l2norm_layer.c \
  layer.c \
  list.c \
  local_layer.c \
  logistic_layer.c \
  lstm_layer.c \
  main.c \
  matrix.c \
  maxpool_layer.c \
  network.c \
  normalization_layer.c \
  option_list.c \
  parser.c \
  region_layer.c \
  reorg_layer.c \
  rnn_layer.c \
  route_layer.c \
  shortcut_layer.c \
  softmax_layer.c \
  tree.c \
  upsample_layer.c \
  utils.c \
  yolo_layer.c
EXE = darknet
LDFLAGS = -lm
CFLAGS += -fintegrated-as

-include $(ROOT)/../common/default.mk
