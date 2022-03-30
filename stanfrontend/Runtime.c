#include <stdlib.h>
#include <math.h>
#include <stdio.h>
#include "stanlib.h"

void* observation;
void print_data(void *);

void* state;
void* candidate;
void print_params(void*);

void* get_state();
void set_state(void*);

void load_from_cli(void* opaque, char *files[]);
void data();
void transformed_data();
void parameters();
void* init_parameters(void* p);
void transformed_parameters(void* p);
double model(void* p);
void generated_quantities();

void* propose(void * state);

int main(int argc, char* argv[]) {
  if (argc == 1) {
    printf("One argument required: number of iterations\n");
    printf("optionally, csv files of data in order of declaration\n");
    exit(1);
  }
  int n = atoi(argv[1]);

  //data();
  load_from_cli(&observation, argv+2);
  transformed_data();
  print_data(&observation);

  // parameters();
  state = init_parameters(&state);

  void* pi = get_state();
  printf("initial state    : ");
  print_params(pi);


  for (int i = 0; i < n; ++i) {

    void* pi = get_state();
    printf("get pi           : "); print_params(pi);
    transformed_parameters(pi);
    printf("transformed      : "); print_params(pi);
    double lp_parameters = model(pi);

    void* newpi = propose(pi);
    printf("proposed    newpi: "); print_params(newpi);
    transformed_parameters(newpi);
    printf("transformed newpi: "); print_params(newpi);
    double lp_candidate = model(newpi);
    double lu = log((double) rand() / RAND_MAX);

    printf("lu <= lp_candidate - lp_parameters: %i = %f <= %f - %f \n", lu <= lp_candidate - lp_parameters, lu, lp_candidate, lp_parameters);
    if (lu <= lp_candidate - lp_parameters) {
      printf("--------------------------\n");
      printf("setting state... newpi is: "); print_params(newpi);
      set_state(newpi);
      printf("setting state in iteration %d. target log_prob: %f\n", i+1, lp_candidate); // 1-index iterations
      print_params(&state);
    }

    generated_quantities();
  }

  printf("\n...completed execution!");
  printf("\n\nSummary:\n\t");
  print_params(&state);
  printf("\n");
  return 0;
  
}
