/* C7 probe FFI driver for arenawrite.pnk. Linked next to the stock basis_ffi.c.
 *
 * ffiload_line:   as C6 — $LINE -> buffer at `a`; line length written at c+16.
 * ffireport_arena: c = the 48-byte span arena writeSpans built (6 words = 3
 *                  (offset,length) records); a = @base, holding the fill count at
 *                  a+24 and the fillLoop arena at a+512.  Dumps both structures,
 *                  so the observed bytes can be checked against the Lean parser.
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

void ffireport_arena(unsigned char *c, long clen, unsigned char *a, long alen) {
  uint64_t r[6];
  for (int i = 0; i < 6; i++) memcpy(&r[i], c + i * 8, 8);
  printf("spans: method=(%llu,%llu) target=(%llu,%llu) version=(%llu,%llu)\n",
         (unsigned long long)r[0], (unsigned long long)r[1],
         (unsigned long long)r[2], (unsigned long long)r[3],
         (unsigned long long)r[4], (unsigned long long)r[5]);
  uint64_t fillN;
  memcpy(&fillN, a + 24, 8);
  printf("fill[N=%llu]:", (unsigned long long)fillN);
  for (uint64_t i = 0; i < fillN; i++) {
    uint64_t v;
    memcpy(&v, a + 512 + i * 8, 8);
    printf(" %llu", (unsigned long long)v);
  }
  printf("\n");
  fflush(stdout);
}
