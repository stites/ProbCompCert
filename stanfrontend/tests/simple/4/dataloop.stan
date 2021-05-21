data {
  int flips[100];
}
model {
  for (i in 1:100) {
    print(flips[i]);
  }
}
