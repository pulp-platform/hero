#!/bin/bash


cd tests/pulp-training/hello
make clean all
make run gui=1 &
