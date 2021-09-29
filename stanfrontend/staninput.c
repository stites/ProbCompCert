#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdio.h>

void print_data(void *);
void set_data(void *);

int read_one_csv_row_len(char *filename) {
	FILE *file;
	file = fopen(filename, "r");
    char line[4098];
    int i = 0;
	while (fgets(line, 4098, file))
    {
	    char* tok;
        tok = strtok(line, ",");
        while (tok != NULL)
        {
            tok = strtok(NULL, ",");
            i++;
        }
    }
	fclose(file);
    return i;
}

void read_one_csv_row_int(char *filename, int arr []) {
	FILE *file;
	file = fopen(filename, "r");
    char line[4098];
    int i = 0;
	while (fgets(line, 4098, file))
    {
	    char* tok;
        tok = strtok(line, ",");
        int cell;
        while (tok != NULL)
        {
            cell = atoi(tok);
            tok = strtok(NULL, ",");
            arr[i] = cell;
            i++;
        }
        printf("added %i int elements to array\n", i);
    }
	fclose(file);
    // shorten the array
    arr[i] = NULL;
}

int* read_one_csv_row_fast(int len, char *filename) {
	FILE *file;
	file = fopen(filename, "r");
    int * arr = (int *) malloc(sizeof(int) * len);
    fread(arr, sizeof(int), len, file);
    return arr;
}

void print_int_array(int len, int *arr) {
    for (int i = 0; i < len; i++)
    {
        printf("%i, ", *(arr++));
    }
    printf("\b\b  \n");
}


void * observation;
void initialize_data_from_cli(void * obs, int argc, char* argv[])
{
    int* tmp = (int*) observation;
    for (int i = 2; i < argc; i++)
    {
        int len = read_one_csv_row_len(argv[i]);
        printf("Argument %d (length: %i): %s\n", i, len, argv[i]);

        // int * arr = (int *) malloc(sizeof(int) * len);
        read_one_csv_row_int(argv[i], ((int*) observation));
        print_int_array(len, (int*) ((int*) observation));
        tmp++;
    }
}
