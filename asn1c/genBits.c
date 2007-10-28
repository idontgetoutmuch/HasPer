#include <stdio.h>   /* for stdout */
#include  <stdlib.h> /* for malloc () */
#include  <assert.h> /* for run-time control */
#include <T4.h> /* T4 ASN.1 type */

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

  /* Declare a pointer to a T4 type */
  T4_t *t4;

  /* Encoder return value */
  asn_enc_rval_t ec;

  /* Allocate an instance of  T4 */
  t4 = calloc(1, sizeof(T4_t)); /* not malloc! */
  assert(t4); /* Assume infinite memory */

  /* Prepare a BIT STRING */
  (*t4).first.buf = calloc(2, 1);
  assert((*t4).first.buf);
  (*t4).first.size = 2;        /* 2 bytes */ 
  (*t4).first.buf[0] = 0xc0;   /* Set BIT STRING value */ 
  (*t4).first.buf[1] = 0xc0;   /* Set BIT STRING value */ 
  (*t4).first.bits_unused = 4; /* Trim unused bits */ 

  /* And another BIT STRING */
  (*t4).second.buf = calloc(3, 1);
  assert((*t4).second.buf);
  (*t4).second.size = 3;        /* 3 bytes */ 
  (*t4).second.buf[0] = 0xc0;   /* Set BIT STRING value */ 
  (*t4).second.buf[1] = 0xc0;   /* Set BIT STRING value */ 
  (*t4).second.buf[2] = 0xc0;   /* Set BIT STRING value */ 
  (*t4).second.bits_unused = 4; /* Trim unused bits */ 

  /* And another BIT STRING */
  (*t4).nest1.third.buf = calloc(5, 1);
  assert((*t4).nest1.third.buf);
  (*t4).nest1.third.size = 5;        /* 5 bytes */ 
  (*t4).nest1.third.buf[0] = 0xc0;   /* Set BIT STRING value */ 
  (*t4).nest1.third.buf[1] = 0xc0;   /* Set BIT STRING value */ 
  (*t4).nest1.third.buf[2] = 0xc0;   /* Set BIT STRING value */ 
  (*t4).nest1.third.buf[3] = 0xc0;   /* Set BIT STRING value */ 
  (*t4).nest1.third.buf[4] = 0xc0;   /* Set BIT STRING value */ 
  (*t4).nest1.third.bits_unused = 4; /* Trim unused bits */ 

  /* And another BIT STRING */
  (*t4).nest1.fourth.buf = calloc(7, 1);
  assert((*t4).nest1.fourth.buf);
  (*t4).nest1.fourth.size = 7;        /* 7 bytes */ 
  (*t4).nest1.fourth.buf[0] = 0xc0;   /* Set BIT STRING value */ 
  (*t4).nest1.fourth.buf[1] = 0xc0;   /* Set BIT STRING value */ 
  (*t4).nest1.fourth.buf[2] = 0xc0;   /* Set BIT STRING value */ 
  (*t4).nest1.fourth.buf[3] = 0xc0;   /* Set BIT STRING value */ 
  (*t4).nest1.fourth.buf[4] = 0xc0;   /* Set BIT STRING value */ 
  (*t4).nest1.fourth.buf[5] = 0xc0;   /* Set BIT STRING value */ 
  (*t4).nest1.fourth.buf[6] = 0xc0;   /* Set BIT STRING value */ 
  (*t4).nest1.fourth.bits_unused = 4; /* Trim unused bits */ 

  fprintf(stdout, "%d\n", sizeof(T4_t));

  if(ac < 2) {
       fprintf(stderr,"Specify filename for PER output\n");
  } else {
       const char *filename = av[1];
       FILE *fp = fopen(filename,"wb");    /* for PER output */
       if(!fp) {
            perror(filename);
            exit(71); /* better, EX_OSERR */
       }
       /* Encode T4 as PER */
       ec = uper_encode(&asn_DEF_T4,t4,write_out,fp);
       fclose(fp);
       if(ec.encoded == -1) {
            fprintf(stderr,"Could not encode T4 (at %s)\n",
            ec.failed_type ? ec.failed_type->name : "unknown");
       exit(65); /* better, EX_DATAERR */
       } else {
       fprintf(stderr,"Created %s with PER encoded T4\n",filename);
       }
  }
  /* Also print the constructed T4 XER encoded (XML) */
  xer_fprint(stdout,&asn_DEF_T4,t4);
  return 0; /* Encoding finished successfully */
}
