#include <time.h>
#include <stdlib.h>
#include <math.h>
#include <stdio.h>
#include <stdarg.h>
#include <string.h>

void uniform_lpdf(void* rp, va_list argptr) {
  double * retp = (double *) rp;
  int l, r;
  l = va_arg(argptr, int);
  r = va_arg(argptr, int);
  *retp = log((((double) rand() / RAND_MAX) * (r - l)) + l);
}

void call_dist(char* symb, void* ret, int nargs, ...) {
  va_list varargp;
  va_start(varargp, nargs);
  if (strcmp("uniform_lpdf", symb) == 0) {
    uniform_lpdf(ret, varargp);
  } else {
    printf("unknown distribution function!\n");
  }
  va_end(varargp);
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

  call_dist("uniform_lpdf", &p->mu, 2, 0, 1);
  target += p->mu;

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
  double target;
  data();
  transformed_data();
  parameters();
  transformed_parameters(get_state());
  model(get_state());
  generated_quantities();
  return 0;
}
