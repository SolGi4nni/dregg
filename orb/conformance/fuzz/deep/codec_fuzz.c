/* In-process coverage-agnostic mutation fuzzer for the proven parse + codec
 * seams, driven DIRECTLY (no socket, no serve): the HTTP/1.1 request framer,
 * the WebSocket frame-header decoder / admission / UTF-8 automaton / close-code
 * registry, and the interactive HTTP/2 connection engine. Each seam is a
 * C-ABI export of the machine-checked core; this harness crosses it millions
 * of times on structurally-mutated inputs and reports any abort/segfault/hang.
 *
 * Crash isolation: the CURRENT input is held in a static buffer; a fatal-signal
 * handler (SIGSEGV/SIGABRT/SIGBUS/SIGFPE/SIGILL) and a watchdog (SIGALRM) write
 * that input's {surface,index,hex} to the state file and _exit(97|98). A driver
 * reruns past the culprit index so a single crash does not end the campaign.
 *
 * Every reported number is from an ACTUAL crossing done here — nothing asserted
 * without a run. A clean pass is the expected outcome for a proven codec and is
 * itself the useful signal (no ABI/compiled-form regression).
 */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <signal.h>
#include <time.h>
#include <fcntl.h>

static int open_state(const char* path) {
    return open(path, O_WRONLY|O_CREAT|O_TRUNC, 0644);
}

typedef struct LeanObj LeanObj;

/* runtime + module boot */
extern void lean_initialize_runtime_module(void);
extern void lean_io_mark_end_initialization(void);
extern LeanObj* initialize_Dataplane(uint8_t builtin, LeanObj* world);
/* The framer and WebSocket decoder are NOT in the serve module's import
 * closure (initialize_Dataplane does not reach them — see http.rs / ws.rs);
 * each seam's top module must be initialized explicitly, exactly as the host
 * does on first crossing. */
extern LeanObj* initialize_Body_FrameRaw(uint8_t, LeanObj*);
extern LeanObj* initialize_Ws_Decode(uint8_t, LeanObj*);
extern LeanObj* initialize_Ws_Encode(uint8_t, LeanObj*);
extern LeanObj* initialize_Ws_Utf8(uint8_t, LeanObj*);
extern LeanObj* initialize_Ws_ReassemblyAdmit(uint8_t, LeanObj*);
extern LeanObj* initialize_Reactor_H2Ingress(uint8_t, LeanObj*);

/* parse/codec seams */
extern LeanObj* drorb_frame_request(LeanObj* input);
extern LeanObj* drorb_ws_header(LeanObj* input);
extern uint8_t  drorb_ws_close_ok(uint32_t code);
extern uint32_t drorb_ws_utf8(uint32_t state, LeanObj* chunk);
extern uint64_t drorb_ws_admit(uint32_t m, uint64_t buf_len, uint32_t opcode,
                               uint8_t fin, uint64_t len, uint64_t cap);
extern LeanObj* drorb_h2c_conn_init(uint8_t unit);
extern LeanObj* drorb_h2c_conn_feed(LeanObj* state, LeanObj* input);

/* ffi/drorb_ffi.c marshalling adapter */
extern LeanObj* drorb_sarray_of_bytes(const uint8_t* p, size_t n);
extern size_t   drorb_sarray_len(LeanObj* o);
extern const uint8_t* drorb_sarray_ptr(LeanObj* o);
extern void     drorb_obj_dec(LeanObj* o);
extern LeanObj* drorb_io_world(void);
extern int      drorb_io_ok(LeanObj* o);
extern void     drorb_pair_split(LeanObj* pair, LeanObj** fst, LeanObj** snd);

/* ------------------------------------------------------------------ state */
#define MAXIN (256*1024)
static uint8_t   g_cur[MAXIN];
static size_t    g_cur_len;
static uint64_t  g_idx;
static const char* g_surface = "?";
static int       g_state_fd = -1;
static volatile sig_atomic_t g_in_call = 0;

static const char HEX[] = "0123456789abcdef";

/* async-signal-safe dump of the current input to the state fd, then _exit */
static void dump_and_exit(int code, const char* why) {
    if (g_state_fd >= 0) {
        char hdr[256];
        int n = 0;
        const char* s = "verdict="; while (*s) hdr[n++] = *s++;
        s = why; while (*s) hdr[n++] = *s++;
        hdr[n++] = '\n';
        s = "surface="; while (*s) hdr[n++] = *s++;
        s = g_surface; while (*s) hdr[n++] = *s++;
        hdr[n++] = '\n';
        /* index */
        s = "index="; while (*s) hdr[n++] = *s++;
        char num[24]; int ni = 0; uint64_t v = g_idx;
        if (v == 0) num[ni++] = '0';
        while (v) { num[ni++] = '0' + (v % 10); v /= 10; }
        while (ni) hdr[n++] = num[--ni];
        hdr[n++] = '\n';
        s = "hex="; while (*s) hdr[n++] = *s++;
        (void)!write(g_state_fd, hdr, n);
        /* hex of current input */
        static char hx[2*MAXIN + 2];
        size_t L = g_cur_len, j = 0;
        for (size_t i = 0; i < L; i++) {
            hx[j++] = HEX[g_cur[i] >> 4];
            hx[j++] = HEX[g_cur[i] & 15];
        }
        hx[j++] = '\n';
        (void)!write(g_state_fd, hx, j);
    }
    _exit(code);
}

static void on_fatal(int sig) {
    const char* why = "SIGNAL";
    switch (sig) {
        case SIGSEGV: why = "SIGSEGV"; break;
        case SIGABRT: why = "SIGABRT"; break;
        case SIGBUS:  why = "SIGBUS";  break;
        case SIGFPE:  why = "SIGFPE";  break;
        case SIGILL:  why = "SIGILL";  break;
    }
    dump_and_exit(97, why);
}

static void on_alarm(int sig) {
    (void)sig;
    if (g_in_call) dump_and_exit(98, "HANG-ALARM");
    /* not inside a crossing — just re-arm; progress is fine */
    alarm(20);
}

/* ------------------------------------------------------------------ prng */
static uint64_t rng_s;
static inline uint64_t xrand(void) {
    uint64_t x = rng_s;
    x ^= x << 13; x ^= x >> 7; x ^= x << 17;
    rng_s = x; return x;
}
static inline uint32_t rr(uint32_t n) { return n ? (uint32_t)(xrand() % n) : 0; }

/* ------------------------------------------------------------------ corpora */
typedef struct { const uint8_t* p; size_t n; } Seed;

/* HTTP/1.1 framer seeds (chunked / CL / pipelined) */
static const uint8_t f0[] = "GET /health HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n";
static const uint8_t f1[] = "POST /e HTTP/1.1\r\nHost: x\r\nContent-Length: 5\r\n\r\nhello";
static const uint8_t f2[] = "POST /e HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\n";
static const uint8_t f3[] = "POST /e HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n4;ext=1\r\ndata\r\n0\r\nTrailer: v\r\n\r\n";
static const uint8_t f4[] = "GET / HTTP/1.1\r\nHost: a\r\n\r\nGET / HTTP/1.1\r\nHost: b\r\n\r\n";
static const uint8_t f5[] = "POST /e HTTP/1.1\r\nHost: x\r\nContent-Length: 3\r\nTransfer-Encoding: chunked\r\n\r\n0\r\n\r\n";
static const Seed FRAME_SEEDS[] = {
    {f0,sizeof f0-1},{f1,sizeof f1-1},{f2,sizeof f2-1},
    {f3,sizeof f3-1},{f4,sizeof f4-1},{f5,sizeof f5-1},
};

/* WebSocket frame-header seeds (client->server: masked). 2 fixed + ext-len + mask */
static const uint8_t w0[] = {0x81,0x85,0x01,0x02,0x03,0x04,0x10,0x11,0x12,0x13,0x14}; /* text len5 */
static const uint8_t w1[] = {0x82,0xFE,0x01,0x00,0xAA,0xBB,0xCC,0xDD};                 /* binary 16-bit len */
static const uint8_t w2[] = {0x82,0xFF,0,0,0,0,0,1,0,0,0xDE,0xAD,0xBE,0xEF};           /* 64-bit len */
static const uint8_t w3[] = {0x88,0x82,0x00,0x00,0x00,0x00,0x03,0xE8};                 /* close code */
static const uint8_t w4[] = {0x89,0x80,0x00,0x00,0x00,0x00};                           /* ping len0 */
static const uint8_t w5[] = {0x01,0x85,0x01,0x02,0x03,0x04,0x00,0x00,0x00,0x00,0x00};  /* cont/frag text */
static const Seed WS_SEEDS[] = {
    {w0,sizeof w0},{w1,sizeof w1},{w2,sizeof w2},
    {w3,sizeof w3},{w4,sizeof w4},{w5,sizeof w5},
};

/* HTTP/2 client flight: preface + empty SETTINGS + HEADERS(GET /) */
static const uint8_t h0[] = {
    'P','R','I',' ','*',' ','H','T','T','P','/','2','.','0','\r','\n','\r','\n','S','M','\r','\n','\r','\n',
    0,0,0, 4, 0, 0,0,0,0,                 /* SETTINGS len0 */
    0,0,6, 1, 5, 0,0,0,1, 0x82,0x86,0x84,0x41,0x01,'x' /* HEADERS END_H|END_S */
};
/* preface + SETTINGS + partial/garbage frame region for the engine to walk */
static const uint8_t h1[] = {
    'P','R','I',' ','*',' ','H','T','T','P','/','2','.','0','\r','\n','\r','\n','S','M','\r','\n','\r','\n',
    0,0,0, 4, 0, 0,0,0,0,
    0,0,8, 0, 0, 0,0,0,1, 1,2,3,4,5,6,7,8 /* DATA on stream 1 */
};
static const Seed H2_SEEDS[] = { {h0,sizeof h0},{h1,sizeof h1} };

/* ------------------------------------------------------------------ mutate */
static size_t mutate(const Seed* seeds, size_t nseeds, uint8_t* out, size_t cap) {
    const Seed* s = &seeds[rr(nseeds)];
    size_t len = s->n;
    if (len > cap) len = cap;
    memcpy(out, s->p, len);
    uint32_t rounds = 1 + rr(6);
    for (uint32_t r = 0; r < rounds; r++) {
        if (len == 0) { out[0] = (uint8_t)xrand(); len = 1; }
        uint32_t op = rr(9);
        switch (op) {
        case 0: out[rr(len)] ^= (uint8_t)(1u << rr(8)); break;          /* bit flip */
        case 1: out[rr(len)] = (uint8_t)xrand(); break;                 /* byte set */
        case 2: { size_t i = rr(len), d = 1 + rr(16);                   /* delete span */
                  if (i + d > len) d = len - i;
                  memmove(out+i, out+i+d, len-i-d); len -= d; break; }
        case 3: { if (len < cap) { size_t i = rr(len+1);               /* insert */
                  memmove(out+i+1, out+i, len-i); out[i]=(uint8_t)xrand(); len++; } break; }
        case 4: len = rr(len+1); break;                                 /* truncate */
        case 5: { size_t i = rr(len), d = 1 + rr(64);                   /* dup span (grow) */
                  if (i + d > len) d = len - i;
                  if (len + d <= cap) { memmove(out+i+d, out+i, len-i); memcpy(out+i, out+i, d); len += d; } break; }
        case 6: { size_t i = rr(len+1), k = 1 + rr(8);                  /* CRLF spray */
                  for (uint32_t j=0;j<k && len+2<=cap;j++){ memmove(out+i+2,out+i,len-i); out[i]='\r'; out[i+1]='\n'; len+=2; } break; }
        case 7: { size_t i = rr(len);                                   /* length-field corruption */
                  out[i] = (uint8_t)(xrand() & 0xFF); if (i+1<len) out[i+1]=(uint8_t)xrand(); break; }
        default: { uint32_t k = 1 + rr(64);                             /* append junk */
                  for (uint32_t j=0;j<k && len<cap;j++) out[len++]=(uint8_t)xrand(); break; }
        }
    }
    return len;
}

/* ------------------------------------------------------------------ crossings */
static void cross_frame(const uint8_t* d, size_t n) {
    LeanObj* arg = drorb_sarray_of_bytes(d, n);
    LeanObj* out = drorb_frame_request(arg);
    volatile size_t m = drorb_sarray_len(out);
    if (m) { volatile uint8_t v = drorb_sarray_ptr(out)[0]; (void)v; }
    drorb_obj_dec(out);
}

static void cross_ws(const uint8_t* d, size_t n) {
    /* header decode over the whole prefix */
    LeanObj* arg = drorb_sarray_of_bytes(d, n);
    LeanObj* out = drorb_ws_header(arg);
    size_t m = drorb_sarray_len(out);
    const uint8_t* p = drorb_sarray_ptr(out);
    uint8_t tag = m ? p[0] : 0;
    /* if it decoded a header, exercise admit + close-code + utf8 with its fields */
    if (tag == 2 && m >= 16) {
        uint8_t fin = p[1], opcode = p[2];
        uint64_t len = 0; for (int i=0;i<8;i++) len |= (uint64_t)p[7+i] << (8*i);
        volatile uint64_t a = drorb_ws_admit(rr(3), rr(1u<<20), opcode, fin, len, 16ull<<20); (void)a;
    }
    drorb_obj_dec(out);
    /* close-code registry over a fuzzed code drawn from the bytes */
    uint32_t code = n>=2 ? ((uint32_t)d[0]<<8 | d[1]) : rr(70000);
    volatile uint8_t ok = drorb_ws_close_ok(code); (void)ok;
    /* incremental UTF-8 automaton fed the raw bytes as a payload chunk */
    LeanObj* c = drorb_sarray_of_bytes(d, n);
    volatile uint32_t st = drorb_ws_utf8(n ? d[0] : 0, c); (void)st;
}

static void cross_h2(const uint8_t* d, size_t n) {
    LeanObj* state = drorb_h2c_conn_init(0);
    /* feed in up to 3 splits so partial-frame buffering in the engine is walked */
    size_t off = 0; int splits = 1 + (int)rr(3);
    for (int i = 0; i < splits && off <= n; i++) {
        size_t remain = n - off;
        size_t take = (i == splits-1) ? remain : rr((uint32_t)remain + 1);
        LeanObj* input = drorb_sarray_of_bytes(d + off, take);
        LeanObj* pair = drorb_h2c_conn_feed(state, input);
        LeanObj* next = NULL; LeanObj* octets = NULL;
        drorb_pair_split(pair, &next, &octets);
        volatile size_t m = drorb_sarray_len(octets); (void)m;
        drorb_obj_dec(octets);
        state = next;
        off += take;
        if (take == 0) break;
    }
    drorb_obj_dec(state);
}

/* ------------------------------------------------------------------ main */
int main(int argc, char** argv) {
    uint64_t seed = 1, count = 1000000, start = 0;
    const char* surface = "all";
    const char* statef = NULL;
    for (int i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "--seed") && i+1<argc) seed = strtoull(argv[++i],0,10);
        else if (!strcmp(argv[i], "--count") && i+1<argc) count = strtoull(argv[++i],0,10);
        else if (!strcmp(argv[i], "--start") && i+1<argc) start = strtoull(argv[++i],0,10);
        else if (!strcmp(argv[i], "--surface") && i+1<argc) surface = argv[++i];
        else if (!strcmp(argv[i], "--state") && i+1<argc) statef = argv[++i];
    }
    if (statef) g_state_fd = open_state(statef);

    /* fatal-signal + watchdog handlers BEFORE any crossing */
    struct sigaction sa; memset(&sa,0,sizeof sa); sa.sa_handler = on_fatal;
    sigaction(SIGSEGV,&sa,0); sigaction(SIGABRT,&sa,0); sigaction(SIGBUS,&sa,0);
    sigaction(SIGFPE,&sa,0);  sigaction(SIGILL,&sa,0);
    struct sigaction wa; memset(&wa,0,sizeof wa); wa.sa_handler = on_alarm;
    sigaction(SIGALRM,&wa,0);

    lean_initialize_runtime_module();
    lean_io_mark_end_initialization();
    #define INIT(fn) do { LeanObj* r = fn(1, drorb_io_world()); \
        if (drorb_io_ok(r) != 1) { fprintf(stderr,"%s failed\n",#fn); return 2; } \
        drorb_obj_dec(r); } while(0)
    INIT(initialize_Dataplane);        /* h2 engine closure (Reactor.H2Ingress) */
    INIT(initialize_Body_FrameRaw);    /* HTTP/1.1 framer + chunked/CL smuggling */
    INIT(initialize_Ws_Decode);        /* WS frame-header decoder */
    INIT(initialize_Ws_Encode);        /* WS server-frame encoder */
    INIT(initialize_Ws_Utf8);          /* WS incremental UTF-8 automaton */
    INIT(initialize_Ws_ReassemblyAdmit);/* WS §5.4 + cap admission verdict */

    int do_frame = !strcmp(surface,"all")||!strcmp(surface,"frame");
    int do_ws    = !strcmp(surface,"all")||!strcmp(surface,"ws");
    int do_h2    = !strcmp(surface,"all")||!strcmp(surface,"h2");

    /* deterministic per-index seeding so --start resumes past a culprit */
    uint64_t nf=0,nw=0,nh=0;
    alarm(20);
    for (uint64_t i = start; i < count; i++) {
        g_idx = i;
        rng_s = (seed*0x9E3779B97F4A7C15ull) ^ (i+0x1234567u);
        if (!rng_s) rng_s = 0xDEADBEEF;
        uint32_t pick = rr(3);
        g_in_call = 1;
        if (do_frame && (pick==0 || (!do_ws && !do_h2))) {
            g_surface="frame"; g_cur_len = mutate(FRAME_SEEDS,6,g_cur,MAXIN);
            cross_frame(g_cur, g_cur_len); nf++;
        } else if (do_ws && (pick==1 || !do_h2)) {
            g_surface="ws"; g_cur_len = mutate(WS_SEEDS,6,g_cur, 4096);
            cross_ws(g_cur, g_cur_len); nw++;
        } else if (do_h2) {
            g_surface="h2"; g_cur_len = mutate(H2_SEEDS,2,g_cur, 64*1024);
            cross_h2(g_cur, g_cur_len); nh++;
        } else if (do_frame) {
            g_surface="frame"; g_cur_len = mutate(FRAME_SEEDS,6,g_cur,MAXIN);
            cross_frame(g_cur, g_cur_len); nf++;
        }
        g_in_call = 0;
        if (((i - start) & 0x3FFFF) == 0x3FFFF) { alarm(20); }
    }
    printf("{\"clean\":true,\"surface\":\"%s\",\"cases\":%llu,\"frame\":%llu,\"ws\":%llu,\"h2\":%llu,\"seed\":%llu}\n",
           surface,(unsigned long long)(count-start),(unsigned long long)nf,
           (unsigned long long)nw,(unsigned long long)nh,(unsigned long long)seed);
    return 0;
}
