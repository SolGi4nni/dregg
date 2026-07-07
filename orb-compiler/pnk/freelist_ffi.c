/* C9 probe FFI driver for freelist.pnk. Linked next to the stock basis_ffi.c.
 *
 * ffireport_freelist: c = @base.  The emitted program left, at c+24/+32/+40, the
 *   three pointers returned by alloc #1/#2/#3, and at c+48 the arena base.  Each
 *   block is 16 bytes, so block index = (ptr - arena) / 16.  The reclaim property
 *   is that alloc #3 hands back the SAME address that alloc #2 got and free()
 *   returned to the pool: a3 == a2.
 */
#include <stdio.h>
#include <stdint.h>
#include <string.h>

typedef unsigned long long ull;

void ffireport_freelist(unsigned char *c, long clen, unsigned char *a, long alen) {
  uint64_t a1, a2, a3, arena;
  memcpy(&a1,    c + 24, 8);
  memcpy(&a2,    c + 32, 8);
  memcpy(&a3,    c + 40, 8);
  memcpy(&arena, c + 48, 8);

  uint64_t i1 = (a1 - arena) / 16;
  uint64_t i2 = (a2 - arena) / 16;
  uint64_t i3 = (a3 - arena) / 16;

  printf("alloc1 -> block%llu (0x%llx)\n", (ull)i1, (ull)a1);
  printf("alloc2 -> block%llu (0x%llx)\n", (ull)i2, (ull)a2);
  printf("free(alloc2)\n");
  printf("alloc3 -> block%llu (0x%llx)\n", (ull)i3, (ull)a3);
  printf("RECLAIM: alloc3 %s alloc2  ->  %s\n",
         a3 == a2 ? "==" : "!=",
         a3 == a2 ? "FREED BLOCK REUSED (same address handed back out)"
                  : "NO REUSE");
  fflush(stdout);
}
