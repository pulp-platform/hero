Darknet
=======
Running tinyYOLO using the Darknet backbone by [Joseph Redmon](https://pjreddie.com/darknet/yolo/).

Compiling
---------
Either do it like for all other examples or change the settings in [`compile_and_send`](https://iis-git.ee.ethz.ch/hero/hero/blob/darknet/openmp-examples/darknet/compile_and_send) to your liking and run the script. I left my config in there for reference.

Known Issues
------------
The current code does not work. Comment out the performance counter accesses in [`gemm.c`](https://iis-git.ee.ethz.ch/hero/hero/blob/darknet/openmp-examples/darknet/gemm.c#L134) for correct behaviour.
