/* Feed a chunked request with a chunk-extension of N bytes directly to the
 * proven framer seam (drorb_frame_request), on a thread with a chosen stack
 * size, to localize the observed stack overflow and find its threshold. */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <pthread.h>

typedef struct LeanObj LeanObj;
extern void lean_initialize_runtime_module(void);
extern void lean_io_mark_end_initialization(void);
extern LeanObj* initialize_Body_FrameRaw(uint8_t, LeanObj*);
extern LeanObj* drorb_frame_request(LeanObj*);
extern LeanObj* drorb_sarray_of_bytes(const uint8_t*, size_t);
extern size_t   drorb_sarray_len(LeanObj*);
extern const uint8_t* drorb_sarray_ptr(LeanObj*);
extern void     drorb_obj_dec(LeanObj*);
extern LeanObj* drorb_io_world(void);
extern int      drorb_io_ok(LeanObj*);
extern void     lean_initialize_thread(void);
extern void     lean_finalize_thread(void);

static size_t g_ext;
static const char* g_kind;

static void* worker(void* _) {
    lean_initialize_thread();
    /* build: POST /e ... TE: chunked \r\n\r\n <hexsize>;<EXT>\r\ndata\r\n0\r\n\r\n */
    size_t cap = g_ext + 512;
    uint8_t* buf = malloc(cap);
    int n = sprintf((char*)buf,
        "POST /e HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n4;");
    if (!strcmp(g_kind,"ext")) { memset(buf+n, 'a', g_ext); n += g_ext;
        n += sprintf((char*)buf+n, "\r\ndata\r\n0\r\n\r\n"); }
    else if (!strcmp(g_kind,"trailer")) { /* 0\r\n then N trailer bytes */
        n = sprintf((char*)buf, "POST /e HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n0\r\n");
        for (size_t i=0;i<g_ext && (size_t)n<cap-8;i++) buf[n++]='X';
        n += sprintf((char*)buf+n, "\r\n\r\n"); }
    else { /* single huge header value */
        n = sprintf((char*)buf, "GET / HTTP/1.1\r\nHost: x\r\nX-B: ");
        memset(buf+n,'z',g_ext); n+=g_ext; n+=sprintf((char*)buf+n,"\r\n\r\n"); }
    LeanObj* arg = drorb_sarray_of_bytes(buf, n);
    LeanObj* out = drorb_frame_request(arg);
    size_t m = drorb_sarray_len(out);
    const uint8_t* p = drorb_sarray_ptr(out);
    fprintf(stderr, "kind=%s ext=%zu reqlen=%d -> tag=%d\n", g_kind, g_ext, n, m?p[0]:-1);
    drorb_obj_dec(out);
    lean_finalize_thread();
    return NULL;
}

int main(int argc, char** argv) {
    g_kind = argc>1 ? argv[1] : "ext";
    g_ext  = argc>2 ? strtoull(argv[2],0,10) : 200000;
    size_t stack = argc>3 ? strtoull(argv[3],0,10) : 0;  /* 0 = default */
    lean_initialize_runtime_module();
    lean_io_mark_end_initialization();
    LeanObj* r = initialize_Body_FrameRaw(1, drorb_io_world());
    if (drorb_io_ok(r)!=1){fprintf(stderr,"init fail\n");return 2;}
    drorb_obj_dec(r);
    pthread_attr_t at; pthread_attr_init(&at);
    if (stack) pthread_attr_setstacksize(&at, stack);
    pthread_t th; pthread_create(&th,&at,worker,0); pthread_join(th,0);
    fprintf(stderr, "SURVIVED\n");
    return 0;
}
