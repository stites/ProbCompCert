#include <stdlib.h>
#include <math.h>
#include <stdio.h>
#include <stanlib.h>
#include <staninput.h>

// see staninput.c
void initialize_data_from_cli(void *, int, char* []);

void* observation;
void print_data(void *);

void* state;
void print_state(void*);

void* get_state();
void set_state(void*);

void data();
void transformed_data();
void parameters();
void transformed_parameters(void* p);
double model(void* p);
void generated_quantities();

void* propose();

int main(int argc, char* argv[]) {
  if (argc == 1) {
    printf("At least one argument required: number of iterations\n");
    printf("Optionally, add data fields as *.csv files in order of appearance\n");
    exit(1);
  }
  int n = atoi(argv[1]);

  data();
  initialize_data_from_cli(&observation, argc, argv);
  transformed_data();
  print_data(&observation);

  parameters();

  print_state(&state);
  for (int i = 0; i < n; ++i) {

    void* pi = get_state();

    transformed_parameters(pi);
    double lp_parameters = model(pi);

    void* newpi = propose();

    struct Params* ca = (struct Params*) newpi;

    transformed_parameters(newpi);
    double lp_candidate = model(newpi);

    double u = ((double) rand() / RAND_MAX);

    if (u <= lp_candidate - lp_parameters) {
      set_state(newpi);
      printf("setting state in iteration %d: ", i+1); // 1-index iterations
      print_state(&state);
    }

    generated_quantities();
  }

  printf("\t...completed execution!\n\nSummary:\n\t");
  print_state(&state);
  return 0;
  
}
