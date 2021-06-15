#ifndef STANLIB_H_
#define STANLIB_H_

double randn (double mu, double sigma);
double uniform_lpdf(double x, double a, double b);
double uniform_lpmf(int x, double a, double b);
double bernoulli_lpmf(int x, double p);

#endif // STANLIB_H_
