#include <stdlib.h>
#include <math.h>
#include <stdio.h>

double randn (double mu, double sigma)
{
  double U1, U2, W, mult;
  static double X1, X2;
  static int call = 0;
 
  if (call == 1)
    {
      call = !call;
      return (mu + sigma * (double) X2);
    }
 
  do
    {
      U1 = -1 + ((double) rand () / RAND_MAX) * 2;
      U2 = -1 + ((double) rand () / RAND_MAX) * 2;
      W = pow (U1, 2) + pow (U2, 2);
    }
  while (W >= 1 || W == 0);
 
  mult = sqrt ((-2 * log (W)) / W);
  X1 = U1 * mult;
  X2 = U2 * mult;
 
  call = !call;
 
  return (mu + sigma * (double) X1);
}

int d_size = 10;
int flips[10] = {0,1,1,1,1,1,0,1,1,0}; 

struct Params {
  double mu;
};

struct Params state;

void data() {
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
  
  if (p->mu < 0 || p->mu > 1) {

    return -INFINITY;

  }
  
  for (int i = 0; i < d_size; ++i) {

    target += flips[i] * log(p->mu) + (1 - flips[i]) * log (1 - p->mu);
    
  }

  return target;  
  
}

void generated_quantities() {

  printf("%f\n",state.mu);
      
}

struct Params candidate;

void* propose() {

  candidate.mu = state.mu + randn(0,1);

  return &candidate;
  
}



