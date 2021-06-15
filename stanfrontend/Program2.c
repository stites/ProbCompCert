#include <stdlib.h>
#include <math.h>
#include <stdio.h>
#include "stanlib.h"

struct Data {
  int flip;
};

struct Data observed;

void data() {
  observed.flip = 1;
}

void transformed_data() {
}

struct Params {
  double mu;
};

struct Params state;

void parameters() {
  // state.mu = 0.5;
  state.mu = 0.5;
}

void transformed_parameters(void *p) {
}

void* get_state() {
  return &state; 
}

void map_state(void (*f)(char * k, double v)) {
  struct Params* s = (struct Params*) get_state();
  f("mu", s->mu);
}

void set_state(void* pi) {
  struct Params* p = (struct Params*) pi;
  state = *p;
}

double model(void *pi) {

  double target = 0.0;

  struct Params* p = (struct Params*) pi;
  
  // uniform_sample(p->mu, 0, 1); // but also need to check the data block?
  target += uniform_lpdf(p->mu, 0, 1);
  target += bernoulli_lpmf(observed.flip, p->mu);

  return target;  
  
}

void generated_quantities() {

}

struct Params candidate;

void* propose() {

  candidate.mu = state.mu + randn(0,1);

  return &candidate;
  
}



