
#include <stdio.h>
#include <stdlib.h>

int main() {
  float value = 0;
  printf("- sizeof(float) %lu bytes \n", sizeof(value));
  printf("- value %.0f \n", value);

  float f01 = 0.1;
  float f01str = atof("0.1");
  printf("- 0.1 from code   %.50f \n", f01);
  printf("- 0.1 from string %.50f \n", f01str);

  puts("");
  return 0;
}
