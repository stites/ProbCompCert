#!/bin/bash

../ccomp -c tests/simple/simple.stan
../ccomp -c stanlib.c
../ccomp -c Runtime.c
../ccomp stanlib.o Runtime.o simple.s -o simple

