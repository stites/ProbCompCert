#include <stdlib.h>
#include <stdio.h>
#include <math.h>

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

double uniform_lpdf(double x, double a, double b)
{
    /* printf("uniform_lpdf(%f, %f, %f)\n", x, a, b); */
    return (x < a || x > b) ? INFINITY : 0;
}

double uniform_lpmf(int x, double a, double b)
{
    double k = (double) x;
    return (k < a || k > b) ? INFINITY : (-log(b - a));
}


double bernoulli_lpmf(int x, double p)
{
    /* printf("bernoulli_lpmf(%d, %f)\n", x, p); */
    double k = (double) x;
    return k * log(p) + (1-k) * log(1-p);
}

double uniform_sample(double l, double r)
{
  if (l > r) {
    return NAN;
  } else {
	  return l + (rand() / (RAND_MAX / (r - l)));
  }
}

double normal_sample(double mu, double sigma)
{
  return randn(mu, sigma);
}

double bernoulli_sample(double p)
{
  return (((double) rand () / RAND_MAX) > p) ? 0 : 1;
}

double logit(double p)
{
  return (p <= 0 || p >= 1) ? INFINITY : log(p) - log(1-p);
}

double expit(double a)
{
  return 1 / (1 + exp(-a));
}

double init_unconstrained()
{
  return uniform_sample(-2, 2);
}

double print_start()
{
  printf("state { ");
}
double print_double(double x)
{
  printf("%f ", x);
}
double print_int(int x)
{
  printf("%i ", x);
}
double print_end()
{
  printf("}\n");
}
