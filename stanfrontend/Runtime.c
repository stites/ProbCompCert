#include <stdlib.h>
#include <math.h>
#include <stdio.h>

void* get_state();
void set_state(void*);

void data();
void transformed_data();
void parameters();
void transformed_parameters(void* p);
double model(void* p);
void generated_quantities();

void* propose();

void runtime(int n) {

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
    
  }

}

int main(int argc, char* argv[]) {

  if (argc != 2) {

    printf("One argument required: number of iterations\n");
    exit(1);
    
  }

  data();
  transformed_data();
  
  runtime(atoi(argv[1]));
  
  return 0;
  
}
