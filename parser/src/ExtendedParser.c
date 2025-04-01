#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "Parser.h"
#include "Printer.h"
#include "Absyn.h"

void usage(void) {
  printf("usage: Call with one of the following argument combinations:\n");
  printf("\t--help\t\tDisplay this help message.\n");
  printf("\t(no arguments)\tParse stdin verbosely.\n");
  printf("\t(files)\t\tParse content of files verbosely.\n");
  printf("\t-s (files)\tSilent mode. Parse content of files silently.\n");
}

int main(int argc, char ** argv)
{
  FILE *input;
  Query parse_tree;
  int quiet = 0;
  char *filename = NULL;

  if (argc > 1) {
    if (strcmp(argv[1], "-s") == 0) {
      quiet = 1;
      if (argc > 2) {
        filename = argv[2];
      } else {
        input = stdin;
      }
    } else {
      filename = argv[1];
    }
  }

  if (filename) {
    input = fopen(filename, "r");
    if (!input) {
      usage();
      exit(1);
    }
  }
  else input = stdin;
  /* The default entry point is used. For other options see Parser.h */
  parse_tree = pQuery(input);
  if (parse_tree)
  {
    printf("\nParse Successful!\n");
    if (!quiet) {
      printf("\n[Abstract Syntax]\n");
      printf("%s\n\n", showQuery(parse_tree));
      printf("[Linearized Tree]\n");
      printf("%s\n\n", printQuery(parse_tree));
    }
    free_Query(parse_tree);
    return 0;
  }
  return 1;
}