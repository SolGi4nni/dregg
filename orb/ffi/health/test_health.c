/* Standalone re-entrancy + correctness smoke test for health_serve().
 * Calls health_serve REPEATEDLY (proving re-entrancy) and diffs each response
 * against the golden bytes read from argv[1]. Also exercises a mismatch. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

extern size_t health_serve(const uint8_t *req, size_t req_len,
                           uint8_t *out, size_t out_cap);
extern uint64_t cake_health_report_count;

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: %s golden.bin\n", argv[0]); return 2; }
    FILE *f = fopen(argv[1], "rb");
    if (!f) { perror("open golden"); return 2; }
    static uint8_t golden[65536];
    size_t glen = fread(golden, 1, sizeof golden, f);
    fclose(f);

    const uint8_t req[] = "GET /health HTTP/1.1\r\nHost: x\r\n\r\n";
    size_t reqlen = sizeof(req) - 1; /* drop the C NUL */

    static uint8_t out[65536];
    int ok = 1;
    for (int i = 0; i < 5; i++) {
        memset(out, 0, sizeof out);
        size_t n = health_serve(req, reqlen, out, sizeof out);
        int match = (n == glen) && (memcmp(out, golden, glen) == 0);
        printf("call %d: wrote %zu bytes, golden %zu, byte-identical=%s, report_count=%llu\n",
               i, n, glen, match ? "YES" : "NO",
               (unsigned long long)cake_health_report_count);
        if (!match) ok = 0;
    }

    /* mismatch: a different request must NOT be answered by the constant. */
    const uint8_t bad[] = "GET /nope HTTP/1.1\r\nHost: x\r\n\r\n";
    memset(out, 0, sizeof out);
    size_t bn = health_serve(bad, sizeof(bad) - 1, out, sizeof out);
    printf("mismatch call: wrote %zu bytes (expect 0)\n", bn);
    if (bn != 0) ok = 0;

    printf("%s\n", ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}
