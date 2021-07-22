#include <stdlib.h>
#include <math.h>
#include <stdio.h>
#include <stanlib.h>

void print_state();

void* get_state();
void set_state(void*);

void data();
void transformed_data();
void parameters();
void transformed_parameters(void* p);
double model(void* p);
void generated_quantities();

void* propose();

double expit(double x) {
  return exp(x) / (1 + exp(x));
}
double inv_upper_lower(double a, double b, double y) {
  return a + (b-a) * expit(y);
}

double mu;
void print_state() {
  printf("{ mu: %f }\n", inv_upper_lower(0, 1, mu));
};

int flips[100];
void init_data() {
  int num_elements = sizeof(flips) / sizeof(int);
  int mod = 6;
  printf("num_items: %d\n", num_elements);
  for (int i = 0; i <= num_elements; ++i) {
    *( flips+i ) = (i % mod == 0) ? 1 : 0;
  }
  printf("%% 1s: %f\n", (double) ceil((double) num_elements / (double) mod) / 100);
}
void print_data() {
  int num_elements = sizeof(flips) / sizeof(int);
  printf("flips: [");
  for (int i = 0; i < num_elements; ++i) {
    printf("%i, ", *(flips+i));
  }
  printf("\b\b]\n");
}
double candidate_mu;
void* temp_propose() {
  candidate_mu = mu + uniform_sample(0,1);
  return &candidate_mu;
}


double proposal_model(void *pi) {
  double target = 0.0;
  double mu_transformed = 0 + (1-0) * expit(candidate_mu);
  double t1 = expit(mu_transformed);
  target += (1 - 0) * t1 + (1 - t1);
  target += uniform_lpdf(mu_transformed, 0, 1);
  int d_size = sizeof(flips) / sizeof(int);
  for (int i = 0; i < d_size; ++i) {
    target += bernoulli_lpmf(flips[i], mu_transformed);
  }
  return target;
}


int main(int argc, char* argv[]) {

  if (argc != 2) {

    printf("One argument required: number of iterations\n");
    exit(1);
    
  }

  int n = atoi(argv[1]);
  data();
  transformed_data();

  init_data();
  print_data();

  parameters();

  printf("initial state: ");

  print_state();
  for (int i = 0; i < n; ++i) {

    void* parameters = get_state();
    transformed_parameters(parameters);
    double lp_parameters = model(parameters);
    
    /* void* candidate = propose(); */
    void* candidate = temp_propose();
    transformed_parameters(candidate);
    // double lp_candidate = model(candidate);
    double lp_candidate = proposal_model(candidate);

    double u = ((double) rand() / RAND_MAX);
    /* printf("%f %f\n", lp_parameters, mu); */

    if (u <= lp_candidate - lp_parameters) {
      // printf("\b... setting state!! curr: %d, candidate: %d\n", lp_parameters, lp_candidate);
      mu = candidate_mu;
      set_state(candidate);
      printf("setting state in iteration %d: ", i+1); // 1-index iterations
      print_state();
    }

    generated_quantities();

    // print_state();
  }

  printf("\t...completed execution!\n\nSummary:\n\t");
  print_state();
  return 0;
  
}
