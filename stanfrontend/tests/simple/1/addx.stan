parameters {
  real x;
}
model {
  target += -5 * square(x);
}
