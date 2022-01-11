#!/bin/bash

prog=${1##*/}
name=${prog%.*}
data=./`dirname $1`/${name}_data.c

../ccomp -c $1
../ccomp -c stanlib.c
../ccomp -c Runtime.c
../ccomp -c $data
../ccomp stanlib.o ${name}_data.o Runtime.o $name.s -o $name

