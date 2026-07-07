/* C5 probe FFI driver for arenascan.pnk. Linked next to the stock basis_ffi.c.
 *
 * ffiload_line: c = 24-byte control block; we write the line length at offset 16.
 *               a = destination buffer for the request-line bytes.
 *               The line is taken verbatim from $LINE (raw bytes, no decoding),
 *               so real request lines ("GET / HTTP/1.1") replay directly.
 * ffireport_off: c = the 8-byte result word (the first-SP offset); prints it.
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
  memcpy(c + 16, &len, 8);           /* little-endian on x86-64, matches lds */
}

void ffireport_off(unsigned char *c, long clen, unsigned char *a, long alen) {
  uint64_t r;
  memcpy(&r, c, 8);
  printf("%llu\n", (unsigned long long)r);
  fflush(stdout);
}
