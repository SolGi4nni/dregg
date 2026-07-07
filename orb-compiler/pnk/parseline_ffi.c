/* C6 probe FFI driver for parseline.pnk. Linked next to the stock basis_ffi.c.
 *
 * ffiload_line:  c = 24-byte control block; writes the line length at offset 16.
 *                a = destination buffer for the request-line bytes.
 *                The line is taken verbatim from $LINE (raw bytes, no decoding).
 * ffireport_line: c points at the 4-word result block
 *                 [ok, i1, i2, verlen]; prints the Lean-shaped parse result:
 *                   ok=0 -> "NONE"
 *                   ok=1 -> "SOME method=(0,i1) target=(i1+1,i2) version=(i1+i2+2,verlen)"
 *                 (off = 0, so method.off = 0, matching parseRequestLine 0 line).
 */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

void ffiload_line(unsigned char *c, long clen, unsigned char *a, long alen) {
  const char *sb = getenv("LINE");
  uint64_t len = 0;
  if (sb) {
    size_t n = strlen(sb);
    if ((long)n > alen) { fprintf(stderr, "line too big\n"); exit(1); }
    memcpy(a, sb, n);
    len = (uint64_t)n;
  }
  memcpy(c + 16, &len, 8);
}

void ffireport_line(unsigned char *c, long clen, unsigned char *a, long alen) {
  uint64_t ok, i1, i2, ver;
  memcpy(&ok,  c,      8);
  memcpy(&i1,  c + 8,  8);
  memcpy(&i2,  c + 16, 8);
  memcpy(&ver, c + 24, 8);
  if (ok == 0) {
    printf("NONE\n");
  } else {
    printf("SOME method=(0,%llu) target=(%llu,%llu) version=(%llu,%llu)\n",
           (unsigned long long)i1,
           (unsigned long long)(i1 + 1),
           (unsigned long long)i2,
           (unsigned long long)(i1 + i2 + 2),
           (unsigned long long)ver);
  }
  fflush(stdout);
}
