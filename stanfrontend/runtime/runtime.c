#include <stdlib.h>
#include <math.h>
#include <stdio.h>

double logdensity(double parameters[], int p_size);
int get_parameters_size();

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

void runtime(int n, int p_size) {

  double* parameters = malloc(p_size * sizeof(double));

  for (int j = 0; j < p_size; ++j) {

    parameters[j] = 0.5;

  }
  
  double* candidate = malloc(p_size * sizeof(double));;
  
  for (int i = 0; i < n; ++i) {

    for (int j = 0; j < p_size; ++j) {

      candidate[j] = parameters[j] + randn(0,1);

    }

    double lp_parameters = logdensity(parameters,p_size);
    double lp_candidate = logdensity(candidate,p_size);
    
    double u = ((double) rand() / RAND_MAX);
    
    if (u <= lp_candidate - lp_parameters) {

      for (int j = 0; j < p_size; ++j) {

	parameters[j] = candidate[j];

      }
      
    }

    for (int j = 0; j < p_size; ++j) {

      printf("%f",parameters[j]);
      
    }

    printf("\n");
    
  }

}



int main(int argc, char* argv[]) {

  if (argc != 2) {

    printf("One argument required: number of iterations\n");
    exit(1);
    
  }

  int p_size = get_parameters_size();
  
  runtime(atoi(argv[1]),p_size);

  return 0;
  
}
