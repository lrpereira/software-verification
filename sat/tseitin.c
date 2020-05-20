#include <stdio.h>
#include <stdlib.h>

int main(int argc, char *argv[])
{
  if(argc != 5) {
    printf("Número errado de argumentos.");
    exit(0);
  }

  int n = atoi(argv[1]);

  /* arg2->x  arg3->y  arg4->z */
  switch(n) {
  case 1:
    printf("(-%s %s) && (-%s %s) && (-%s %s %s) 0\n",
           argv[3], argv[2], argv[4], argv[2], argv[2], argv[3], argv[4]);
    break;
  case 2:
    printf("(-%s %s) && (-%s %s) && (-%s -%s %s) 0\n",
           argv[2], argv[3], argv[2], argv[4], argv[3], argv[4], argv[2]);
  }

  return 0;
}
