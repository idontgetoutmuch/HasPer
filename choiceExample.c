#include <stdio.h>   /* for stdout */
#include  <stdlib.h> /* for malloc () */
#include  <assert.h> /* for run-time control */
#include <Type4.h> /* Type4 ASN.1 type */
 
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
   
  /* Declare a pointer to a Type4 type */
  Type4_t *type4;
   
  /* Encoder return value */
  asn_enc_rval_t ec;
   
  /* Allocate an instance of  T4 */
  type4 = calloc(1, sizeof(Type4_t)); /* not malloc! */
  assert(type4); /* Assume infinite memory */
   
  /* Initialize Type4 */
  (*type4).present = Type4_PR_element2;
  (*type4).choice.element2 = 128;

  if(ac < 2) {
       fprintf(stderr,"Specify filename for PER output\n");
  } else {
       const char *filename = av[1];
       FILE *fp = fopen(filename,"wb");    /* for PER output */
       if(!fp) {
            perror(filename);
            exit(71); /* better, EX_OSERR */
       }
       /* Encode Type4 as PER */
       ec = uper_encode(&asn_DEF_Type4,type4,write_out,fp);
       fclose(fp);
       if(ec.encoded == -1) {
            fprintf(stderr,"Could not encode Type4 (at %s)\n",
            ec.failed_type ? ec.failed_type->name : "unknown");
       exit(65); /* better, EX_DATAERR */
       } else {
       fprintf(stderr,"Created %s with PER encoded Type4\n",filename);
       }
  }
  /* Also print the constructed Type4 XER encoded (XML) */
  xer_fprint(stdout,&asn_DEF_Type4,type4);
  return 0; /* Encoding finished successfully */
}
