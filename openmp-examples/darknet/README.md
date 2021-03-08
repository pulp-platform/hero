# Darknet / TinyYOLOv3

This is a port of [`darknet` / TinyYOLOv3 by Joseph Redmon](https://pjreddie.com/darknet/yolo/) to
HERO.


## Compiling

Simply execute `make all` (with the proper environment sourced).

## Running on a Board

First copy the input data of the neural network to the board:
```sh
scp -r inputs/* board-hostname:.
```

Next, and whenever you recompile the application, copy it to the board as well:
```sh
scp darknet board-hostname:.
```

Then SSH to the board and run `darknet` as you run any other application.
