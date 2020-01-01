#include <stdlib.h>

void FailAvRule206() {
  char* a = (char*)malloc(5 * sizeof(*a));
  a = (char*)realloc(a, 10);
  free(a);
  a = (char*)calloc(5, sizeof(float));
  free(a);
  a = new char[5];
  delete a;
  a = new char;
  delete a;
  return;
}