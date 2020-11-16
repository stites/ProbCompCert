#include <math.h>

int d_size = 10;
int data[10] = {0,1,1,1,1,1,0,1,1,0}; 

double logdensity(double parameters[], int p_size) {

  double target = 0.0;

  if (parameters[0] < 0 || parameters[0] > 1) {

    return -INFINITY;

  }
  
  for (int i = 0; i < d_size; ++i) {

    target += data[i] * log(parameters[0]) + (1 - data[i]) * log (1 - parameters[0]);
    
  }

  return target;
  
}

int get_parameters_size() {

  return 1;

}



