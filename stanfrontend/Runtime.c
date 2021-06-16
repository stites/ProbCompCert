#include <stdlib.h>
#include <math.h>
#include <stdio.h>

void* get_state();
void set_state(void*);
void map_state(void (*f)(char* k, double v));

void data();
void transformed_data();
void parameters();
void transformed_parameters(void* p);
double model(void* p);
void generated_quantities();

void* propose();

void print_state_element(char* k, double v) {
  printf("%s: %f, ", k, v);
};

void print_state(int i) {
  if (i != NULL) {
    printf("iteration %d: ", i);
  }
  printf("{");
  map_state(print_state_element);
  printf("\b\b}");
  printf("\n");
};

void write() {
  printf("\t...completed execution!\n\nSummary:\n\t");
  print_state(NULL);
};

int main(int argc, char* argv[]) {

  if (argc != 2) {

    printf("One argument required: number of iterations\n");
    exit(1);
    
  }

  int n = atoi(argv[1]);
  
  data();
  transformed_data();

  parameters();
  
  for (int i = 0; i < n; ++i) {

    void* parameters = get_state();
    transformed_parameters(parameters);
    double lp_parameters = model(parameters);
    
    void* candidate = propose();
    transformed_parameters(candidate);
    double lp_candidate = model(candidate);

    double u = ((double) rand() / RAND_MAX);
    
    if (u <= lp_candidate - lp_parameters) {

      set_state(candidate);

    }

    generated_quantities();

    print_state(i+1); // offset from NULL
  }

  write();
  return 0;
  
}
