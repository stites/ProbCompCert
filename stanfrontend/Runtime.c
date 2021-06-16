#include <stdlib.h>
#include <math.h>
#include <stdio.h>
#include "MuParams.h"

#define PRINT_OPAQUE_STRUCT(p)  print_mem((p), sizeof(*(p)))

void print_mem(void const *vp, size_t n)
{
    unsigned char const *p = vp;
    for (size_t i=0; i<n; i++)
    {
        printf("%02x; ", p[i]);
    }
    printf("\b\b}");
};

void* get_state();
void set_state(void*);

void data();
void transformed_data();
void parameters();
void transformed_parameters(void* p);
double model(void* p);
void generated_quantities();

void* propose();

void print_state(int i) {
  if (i != NULL) {
    printf("iteration %d: ", i);
  }
  struct Params* s = (struct Params*) get_state();
  printf("{");
  printf("mu: %f", s->mu);
  printf("}\n");

  // print_mem(s, 1);
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
