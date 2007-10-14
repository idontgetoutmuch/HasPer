#include <stdio.h> /* for stdout */ 
#include <stdlib.h> /* for malloc() */ 
#include <assert.h> /* for run-time control */ 
#include "T1.h" /* Include T1 definition */ 

/*
 * This is a custom function which writes the
 * encoded output into some FILE stream.
 */

static int
write_out(const void *buffer, size_t size, void *app_key) {
     FILE *out_fp = app_key;
     size_t wrote;
     wrote = fwrite(buffer, 1, size, out_fp);
     return (wrote == size) ? 0 : -1;
}

int main(int ac, char **av) {

  /* Declare a pointer to a T1 type */ 
  T1_t *t1; 

  /* Encoder return value */ 
  asn_enc_rval_t ec;

  /* Allocate an instance of T1 */ 
  t1 = calloc(1, sizeof *t1); 
  assert(t1); /* Assume infinite memory */ 

  /* Prepare a BIT STRING */ 
  t1->first.buf = calloc(2, 1); 
  assert(t1->first.buf);
  t1->first.size = 2;        /* 2 bytes */ 
  t1->first.buf[0] = 0xc0;   /* Set BIT STRING value */ 
  t1->first.buf[1] = 0xc0;   /* Set BIT STRING value */ 
  t1->first.bits_unused = 4; /* Trim unused bits */ 

  /* 
   * Output the resulting structure as PER 
   */ 


  if(ac < 2) {
       fprintf(stderr,"Specify filename for PER output\n");
  } else {
       const char *filename = av[1];
       FILE *fp = fopen(filename,"wb");    /* for PER output */
       if(!fp) {
            perror(filename);
            exit(71); /* better, EX_OSERR */
       }
       /* Encode T1 as PER */
       ec = uper_encode(&asn_DEF_T1,t1,write_out,fp);
       fclose(fp);
       if(ec.encoded == -1) {
            fprintf(stderr,"Could not encode T1 (at %s)\n",
            ec.failed_type ? ec.failed_type->name : "unknown");
       exit(65); /* better, EX_DATAERR */
       } else {
       fprintf(stderr,"Created %s with PER encoded T1\n",filename);
       }
  }

  /* 
   * And print it as XER (XML) 
   */ 
  xer_fprint(stdout, &asn_DEF_T1, t1); 
  
  return 0; 
}
