#ifndef STANLIB_H_
#define STANLIB_H_

double uniform_sample(double l, double r);
double uniform_lpdf(double x, double a, double b);
double uniform_lpmf(int x, double a, double b);

double bernoulli_sample(double p);
double bernoulli_lpmf(int x, double p);

double normal_sample(double mu, double sigma);
double randn(double mu, double sigma);

double logit(double p);
double expit(double a);

double init_unconstrained();

// temporary until printing is supported
void print_start();
void print_double(double x);
void print_int(int x);
void print_long(long x);
void print_end();

void print_array_int(int len, int* arrp);

#endif // STANLIB_H_
