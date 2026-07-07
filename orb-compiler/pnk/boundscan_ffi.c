/* C0 probe FFI driver for boundscan.pnk. Linked next to the stock basis_ffi.c
 * (which provides main(), heap/stack setup, and cml_main dispatch).
 *
 * ffiload_vec:   c = 24-byte control block; we write [arena_len, off, len].
 *                a = destination buffer for the arena bytes.
 *                off from $OFF, len from $LEN (default 0). The arena is the
 *                fixed 16-byte vector below, identical to C0.arena in the
 *                Lean model, so all three kernels scan the same bytes.
 * ffireport_vec: c = the 8-byte result word; prints it as an unsigned decimal.
 */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* "GET / HTTP/1.1\r\n" — byte-identical to C0.arena in model/BoundScan.lean. */
static const unsigned char ARENA[16] = {
  0x47,0x45,0x54,0x20,0x2f,0x20,0x48,0x54,0x54,0x50,0x2f,0x31,0x2e,0x31,0x0d,0x0a
};

void ffiload_vec(unsigned char *c, long clen, unsigned char *a, long alen) {
  const char *so = getenv("OFF");
  const char *sl = getenv("LEN");
  uint64_t off = so ? strtoull(so, NULL, 10) : 0;
  uint64_t len = sl ? strtoull(sl, NULL, 10) : 0;
  uint64_t asz = (uint64_t)sizeof ARENA;
  if ((long)sizeof ARENA > alen) { fprintf(stderr, "arena too big\n"); exit(1); }
  memcpy(c,      &asz, 8);   /* little-endian on x86-64, matches Pancake lds */
  memcpy(c + 8,  &off, 8);
  memcpy(c + 16, &len, 8);
  memcpy(a, ARENA, sizeof ARENA);
}

void ffireport_vec(unsigned char *c, long clen, unsigned char *a, long alen) {
  uint64_t r;
  memcpy(&r, c, 8);
  printf("%llu\n", (unsigned long long)r);
  fflush(stdout);
}
