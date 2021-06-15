data {
  int flip=1;
}
parameters {
  real mu;
}
model {
  mu ~ uniform(0,1);
  flip ~ bernoulli(mu);
}
