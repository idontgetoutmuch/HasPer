#include <stdio.h> /* for stdout */ 
#include <stdlib.h> /* for malloc() */ 
#include <assert.h> /* for run-time control */ 
#include "T1.h" /* Include T1 definition */ 

int main() { 

  /* Declare a pointer to a T1 type */ 
  T1_t *t1; 

  /* Temporary return value */ 
  int ret; 

  /* Allocate an instance of T1 */ 
  t1 = calloc(1, sizeof *t1); 
  assert(t1); /* Assume infinite memory */ 

  /* Prepare a BIT STRING */ 
  t1->first.buf = calloc(1, 1); 
  assert(t1->first.buf);
  t1->first.size = 1;        /* 1 byte */ 
  t1->first.buf[0] = 0xc0;   /* Set BIT STRING value */ 
  t1->first.bits_unused = 5; /* Trim unused bits */ 

  /* 
   * Print the resulting structure as XER (XML) 
   */ 
  xer_fprint(stdout, &asn_DEF_T1, t1); 
  
  return 0; 
}
