#ifndef STANLIB_H_
#define STANLIB_H_

double uniform_lpdf(double x, double a, double b);
double uniform_lpmf(int x, double a, double b);
double bernoulli_lpmf(int x, double p);

double uniform_sample(double mu, double sigma);
double bernoulli_sample(double p);

double logit(double p);
double expit(double a);
#endif // STANLIB_H_
