/* C8 probe FFI driver for collect.pnk. Linked next to the stock basis_ffi.c.
 *
 * ffiload_line:    as C6/C7 — $LINE -> input buffer at `a`; line length at c+16.
 * ffireport_collect: c = the collected-offset arena `out` (one word per delimiter);
 *                    a = @base, holding the final bump pointer `bp` at a+24.
 *                    count = (bp - out) / 8 = number of delimiters collected.
 *                    Dumps (1) the arena read back and (2) the offsets recomputed
 *                    directly from $LINE by the SAME spec (delimiter positions),
 *                    so the two can be checked equal, byte for byte.
 */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

static char g_line[4096];
static uint64_t g_len = 0;

void ffiload_line(unsigned char *c, long clen, unsigned char *a, long alen) {
  const char *sb = getenv("LINE");
  uint64_t len = 0;
  if (sb) {
    size_t n = strlen(sb);
    if ((long)n > alen) { fprintf(stderr, "line too big\n"); exit(1); }
    memcpy(a, sb, n);
    len = (uint64_t)n;
    memcpy(g_line, sb, n);
  }
  g_len = len;
  memcpy(c + 16, &len, 8);
}

void ffireport_collect(unsigned char *c, long clen, unsigned char *a, long alen) {
  /* the bump pointer the emitted program left in memory */
  uint64_t bp;
  memcpy(&bp, a + 24, 8);
  uint64_t out = (uint64_t)(uintptr_t)c;
  uint64_t count = (bp - out) / 8;

  /* (1) the arena, read back: the collected offset list the loop built */
  printf("collect[n=%llu]:", (unsigned long long)count);
  for (uint64_t k = 0; k < count; k++) {
    uint64_t v;
    memcpy(&v, c + k * 8, 8);
    printf(" %llu", (unsigned long long)v);
  }

  /* (2) collectSp recomputed directly from the input line (delimiter offsets) */
  printf("   spec:");
  for (uint64_t j = 0; j < g_len; j++) {
    if ((unsigned char)g_line[j] == 32) printf(" %llu", (unsigned long long)j);
  }
  printf("\n");
  fflush(stdout);
}
