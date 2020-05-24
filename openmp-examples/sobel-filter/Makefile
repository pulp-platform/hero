# Copyright 2018 (C) ETH Zurich and University of Bologna
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

ROOT := $(patsubst %/,%, $(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

CSRCS=main.c sobel.c file_operations.c
EXE=sobel
#CFLAGS=-foffload="-lm"
LDFLAGS=-lm

IMG_DIR      = imgs
IMG_DIR_OUT  = imgs_out
IMAGE_NAME   = img

RUN_ARGS=$(IMG_DIR)/$(IMAGE_NAME).rgb $(IMG_DIR)/$(IMAGE_NAME).gray 512x512 -g $(IMG_DIR)/$(IMAGE_NAME)_gray.gray -i $(IMG_DIR)/$(IMAGE_NAME)_h.gray $(IMG_DIR)/$(IMAGE_NAME)_v.gray

copyout:
	convert $(IMG_DIR)/$(IMAGE_NAME).png $(IMG_DIR)/$(IMAGE_NAME).rgb	
ifeq ($(call ifndef_any_of,HERO_TARGET_HOST HERO_TARGET_PATH_APPS),)
	scp -r ${IMG_DIR} $(HERO_TARGET_HOST):${HERO_TARGET_PATH_APPS}
else
$(error HERO_TARGET_HOST and/or HERO_TARGET_PATH_APPS is not set)
endif

copyin:
	mkdir -p ${IMG_DIR_OUT}
ifeq ($(call ifndef_any_of,HERO_TARGET_HOST HERO_TARGET_PATH_APPS),)
	scp -r $(HERO_TARGET_HOST):${HERO_TARGET_PATH_APPS}/${IMG_DIR}/* ${IMG_DIR_OUT}/.
	convert -size 512x512 -depth 8 $(IMG_DIR_OUT)/$(IMAGE_NAME).gray $(IMG_DIR_OUT)/$(IMAGE_NAME).png
	convert -size 512x512 -depth 8 $(IMG_DIR_OUT)/$(IMAGE_NAME)_gray.gray $(IMG_DIR_OUT)/$(IMAGE_NAME)_gray.png
	convert -size 512x512 -depth 8 $(IMG_DIR_OUT)/$(IMAGE_NAME)_h.gray $(IMG_DIR_OUT)/$(IMAGE_NAME)_h.png
	convert -size 512x512 -depth 8 $(IMG_DIR_OUT)/$(IMAGE_NAME)_v.gray $(IMG_DIR_OUT)/$(IMAGE_NAME)_v.png
else
$(error HERO_TARGET_HOST and/or HERO_TARGET_PATH_APPS is not set)
endif

clean::
	rm -rf $(IMG_DIR_OUT)

run:: copyout

-include $(ROOT)/../common/default.mk
