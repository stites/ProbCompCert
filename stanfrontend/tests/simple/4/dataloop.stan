data {
  int flips[100];
}
model {
  for (i in 1:100) {
    target += flips[i];
  }
}
