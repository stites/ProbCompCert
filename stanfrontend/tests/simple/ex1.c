#include <time.h>
#include <stdlib.h>
#include <math.h>
#include <stdio.h>
#include <stdarg.h>
#include <string.h>

double uniform_lpdf(double mu, int l, int r) {
  // what happens to mu?
  return log((((double) rand() / RAND_MAX) * (r - l)) + l);
}

struct Params {
  double mu;
};

struct Params state;

void data() {
}

void transformed_data() {
}

void parameters() {
  state.mu = NAN;
}

void transformed_parameters(void *p) {
}

void* get_state() {
  return &state; 
}

void set_state(void* pi) {
  struct Params* p = (struct Params*) pi;
  state = *p;
}

double model(void *pi) {
  double target = 0.0;
  struct Params* p = (struct Params*) pi;

  double agg;
  agg = uniform_lpdf(p->mu, 0, 1);
  target += agg;

  return target;  
}

void generated_quantities() {
  printf("%f\n", exp(state.mu));
}

struct Params candidate;

void* propose() {
  return NULL;
}


int main(int argc, char *argv[]) {
  srand(time(0));
  data();
  transformed_data();
  parameters();
  transformed_parameters(get_state());
  model(get_state());
  generated_quantities();
  return 0;
}
