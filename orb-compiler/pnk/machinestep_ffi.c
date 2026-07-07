/* C2 probe FFI driver for machinestep.pnk. Linked next to the stock basis_ffi.c
 * (which provides main(), heap/stack setup, and cml_main dispatch).
 *
 * ffiload_vec:   c = 24-byte control block; we write len at offset 16.
 *                a = destination buffer for the input stream bytes.
 *                The stream is taken from $BYTES: a space-separated list of
 *                decimal byte values (0..255), e.g. BYTES="128 255 129 127 0".
 *                len is the count of bytes parsed. This lets every C2 vector
 *                (model/MachineStep.lean `vectors`) be replayed on the machine.
 * ffireport_vec: c = the 8-byte result word (final counter); prints it decimal.
 */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

void ffiload_vec(unsigned char *c, long clen, unsigned char *a, long alen) {
  const char *sb = getenv("BYTES");
  uint64_t len = 0;
  if (sb) {
    const char *p = sb;
    while (*p) {
      while (*p == ' ' || *p == ',') p++;
      if (!*p) break;
      char *end;
      long v = strtol(p, &end, 10);
      if (end == p) break;           /* no more numbers */
      if ((long)len >= alen) { fprintf(stderr, "stream too big\n"); exit(1); }
      a[len++] = (unsigned char)(v & 0xff);
      p = end;
    }
  }
  memcpy(c + 16, &len, 8);           /* little-endian on x86-64, matches lds */
}

void ffireport_vec(unsigned char *c, long clen, unsigned char *a, long alen) {
  uint64_t r;
  memcpy(&r, c, 8);
  printf("%llu\n", (unsigned long long)r);
  fflush(stdout);
}
