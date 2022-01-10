#!/bin/bash

prog=${1##*/}
name=${prog%.*}

../ccomp -c $1
../ccomp -c stanlib.c
../ccomp -c Runtime.c
../ccomp stanlib.o Runtime.o $name.s -o $name

