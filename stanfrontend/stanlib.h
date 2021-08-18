#ifndef STANLIB_H_
#define STANLIB_H_

double uniform_sample(double l, double r);
double uniform_lpdf(double x, double a, double b);
double uniform_lpmf(int x, double a, double b);

double bernoulli_sample(double p);
double bernoulli_lpmf(int x, double p);

double normal_sample(double mu, double sigma);

double logit(double p);
double expit(double a);

double init_unconstrained();
#endif // STANLIB_H_
