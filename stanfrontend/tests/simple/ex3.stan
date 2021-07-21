data {
  int flip; // initialize to 1
}
// transformed data {
//   int flipped = 1;
// }
parameters {
  real <lower=0,upper=1> mu;
}
model {
  mu ~ uniform(0,1);
  flip ~ bernoulli(mu);
}
