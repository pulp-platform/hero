// Copyright (c) 2020 ETH Zurich and University of Bologna
// Licensed under the Apache License, Version 2.0; see LICENSE.Apache-2.0 for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <hero-target.h> // BIGPULP_MEMCPY
#include <math.h>  // fabs()
#include <stdbool.h>
#include <stdio.h> // printf()

#include "darknet.h"

//#define TIMECOMP
#ifdef TIMECOMP
#include <time.h>
#define CLOCK_PRECISION 1E9
struct timespec tic, toc;

void compute_delta(char* message) {
  clock_gettime(CLOCK_REALTIME, &toc);
  double accum = (toc.tv_sec - tic.tv_sec) + (toc.tv_nsec - tic.tv_nsec) / CLOCK_PRECISION;

  printf("%s, %lf\n", message, accum);
  clock_gettime(CLOCK_REALTIME, &tic);
}
#endif  // TIMECOMP

int LAYER_COUNTER = 0;

int main() {
#ifdef TIMECOMP
  clock_gettime(CLOCK_REALTIME, &tic);
#endif  // TIMECOMP

  // Initialize accelerator with a first "dummy" offload.  This ensures that the slight runtime
  // overhead of initializing the accelerator offload manager does not incur on the first measured
  // offload.
  printf("Initializing accelerator with a \"dummy\" offload.\n");
  uint32_t dummy = 0;
#pragma omp target device(BIGPULP_MEMCPY) map(tofrom: dummy)
  {
    dummy = 1;
  }
  assert(dummy == 1);
  printf("\n");

  // Load the network
  char* cfg = "cfg/yolov3-tiny.cfg";
  char* weights = "yolov3-tiny.weights";
  network* net = load_network(cfg, weights, 0);

#ifdef TIMECOMP
  compute_delta("loading the network");
#endif  // TIMECOMP

  // Load the classes

  char* meta_name = "cfg/coco.data";
  metadata meta = get_metadata(meta_name);

#ifdef TIMECOMP
  compute_delta("loading the classes");
#endif  // TIMECOMP

  // Load frame

  char* frame_name = "data/dog.jpg";
  image frame = load_image_color(frame_name, 0, 0);

#ifdef TIMECOMP
  compute_delta("loading the frame");
#endif  // TIMECOMP

  // Forward propagation through the network

  float* output = network_predict_image(net, frame);

#ifdef TIMECOMP
  compute_delta("forward propagation");
#endif  // TIMECOMP

  // Set detection parameters and detect objects

  float thresh = 0.5;
  float hier_thresh = 0.5;
  float nms = 0.45;

  int num;
  int* pnum = &num;
  detection* dets = get_network_boxes(net, frame.w, frame.h, thresh, hier_thresh, NULL, 0, pnum);

#ifdef TIMECOMP
  compute_delta("object detection");
#endif  // TIMECOMP

  // Non-max suppression (nms) to get rid of overlapping boxes
  do_nms_obj(dets, num, meta.classes, nms);

#ifdef TIMECOMP
  compute_delta("non-max suppression");
#endif  // TIMECOMP

  typedef struct {
    char name[16];
    float prob;
  } result_t;
  result_t expected_results[] = {{.name = "car", .prob = 0.615291},
                                 {.name = "car", .prob = 0.517267},
                                 {.name = "truck", .prob = 0.557827},
                                 {.name = "bicycle", .prob = 0.585022},
                                 {.name = "dog", .prob = 0.570732}};
  const unsigned num_expected_results = sizeof(expected_results) / sizeof(result_t);

  // Loop over results
  bool output_correct = true;
  unsigned num_correct = 0;
  printf("\nDETECTED OBJECTS:\n");
  for (int j = 0; j < num; j++) {
    for (int i = 0; i < meta.classes; i++) {
      if (dets[j].prob[i] > 0) {
        printf("%s: %f = ", meta.names[i], dets[j].prob[i]);
        if (num_correct < num_expected_results && strncmp(expected_results[num_correct].name, meta.names[i], 16) == 0 &&
            fabs(expected_results[num_correct].prob - dets[j].prob[i]) < 0.01) {
          printf("correct!\n");
          num_correct++;
        } else {
          printf("wrong!\n");
          output_correct = false;
        }
      }
    }
  }
  if (num_correct != num_expected_results) {
    printf("%d detections missing or wrong!\n", num_expected_results - num_correct);
    output_correct = false;
  }

#ifdef TIMECOMP
  compute_delta("result evaluation");
#endif  // TIMECOMP

  // Clean up

  free_image(frame);
  free_detections(dets, num);

#ifdef TIMECOMP
  compute_delta("freeing memory");
#endif  // TIMECOMP

  if (output_correct) {
    return 0;
  } else {
    return 1;
  }
}
