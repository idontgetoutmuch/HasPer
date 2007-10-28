#include <stdio.h>   /* for stdout */
#include  <stdlib.h> /* for malloc () */
#include  <assert.h> /* for run-time control */
#include <T3.h> /* T3 ASN.1 type */

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

  /* Declare a pointer to a T3 type */
  T3_t *t3;

  /* Encoder return value */
  asn_enc_rval_t ec;

  /* Allocate an instance of  T3 */
  t3 = calloc(1, sizeof(T3_t)); /* not malloc! */
  assert(t3); /* Assume infinite memory */

  /* Initialize T3 */
  (*t3).first = 3;
  (*t3).second = 5;
  (*t3).nest1.third = 7;
  (*t3).nest1.fourth = 11;
  (*t3).nest1.nest2.fifth = 13;
  (*t3).nest1.nest2.sixth = 17;

  fprintf(stdout, "%d\n", sizeof(T3_t));

  if(ac < 2) {
       fprintf(stderr,"Specify filename for PER output\n");
  } else {
       const char *filename = av[1];
       FILE *fp = fopen(filename,"wb");    /* for PER output */
       if(!fp) {
            perror(filename);
            exit(71); /* better, EX_OSERR */
       }
       /* Encode T3 as PER */
       ec = uper_encode(&asn_DEF_T3,t3,write_out,fp);
       fclose(fp);
       if(ec.encoded == -1) {
            fprintf(stderr,"Could not encode T3 (at %s)\n",
            ec.failed_type ? ec.failed_type->name : "unknown");
       exit(65); /* better, EX_DATAERR */
       } else {
       fprintf(stderr,"Created %s with BER encoded T3\n",filename);
       }
  }
  /* Also print the constructed T3 XER encoded (XML) */
  xer_fprint(stdout,&asn_DEF_T3,t3);
  return 0; /* Encoding finished successfully */
}
