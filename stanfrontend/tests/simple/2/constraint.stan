parameters {
  real<lower=0.0,upper=1.0> mu;
}
model {
  mu ~ uniform(0,1);
}
