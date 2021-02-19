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

int main() {
#ifdef TIMECOMP
  clock_gettime(CLOCK_REALTIME, &tic);
#endif  // TIMECOMP

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

  // Loop over results
  printf("\nDETECTED OBJECTS:\n");
  for (int j = 0; j < num; j++) {
    for (int i = 0; i < meta.classes; i++) {
      if (dets[j].prob[i] > 0) {
        printf("%s: %f\n", meta.names[i], dets[j].prob[i]);
      }
    }
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

  return 0;
}
