#include <stdlib.h>
#include <math.h>
#include <stdio.h>
#include "stanlib.h"

struct Params {
  double mu;
};
struct Params state;

struct Data {
  int flips[3];
};
struct Data observed;

void data() {
  for (int i = 0; i < 3; i++)
  {
    observed.flips[i] = 0;
  }
}

void transformed_data() {
}

void parameters() {
  state.mu = 0.5;
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
  return target;
}

void generated_quantities() {

}

struct Params candidate;

void* propose() {
  candidate.mu = state.mu + uniform_sample(0,1);

  return &candidate;
}

void print_state() {
  struct Params* s = (struct Params*) get_state();
  printf("{");
  printf("mu: %f", s->mu);
  printf("}\n");
}
