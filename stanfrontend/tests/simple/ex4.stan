data {
  int flips[3];
}
parameters {
  real mu;
}
model {
  mu ~ uniform(0,1);
  for (i in 1:3) {
    flips[i] ~ bernoulli(mu);
  }
}
