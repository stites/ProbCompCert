#include <stdlib.h>
#include <math.h>
#include <stdio.h>
#include "stanlib.h"

struct Params {
  //double mu;
};
double mu;
/* struct Params state; */

// struct Data {
// //  int flip;
// };

/* struct Data observed; */

int flip;

void data() {
  flip = 0;
}

void transformed_data() {
}

void parameters() {
  mu = 0;
}

void transformed_parameters(void *p) {
}

void* get_state() {
  // return &state;
}

void set_state(void* pi) {
  // struct Params* p = (struct Params*) pi;
  // state = *p;
}

double expit(double x) {
  return x + 0;
}

double model(void *pi) {
  double target = 0.0;
  // struct Params* p = (struct Params*) pi;
  double t0 = 0 + (1-0) * expit(mu);
  double t1 = expit(mu);
  target += (1 - 0) * t1 + (1 - t1);
  target += uniform_lpdf(t0, 0, 1);
  target += bernoulli_lpmf(flip, t0);

  return target;  
  
}

void generated_quantities() {

}

struct Params candidate;

void* propose() {
}

void print_state() {
}
