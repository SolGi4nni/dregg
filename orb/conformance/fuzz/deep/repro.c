/* Reproduce a single seam crossing from a hex string, with selectable module
 * init, to separate an input-triggered codec fault from an init/ABI issue. */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

typedef struct LeanObj LeanObj;
extern void lean_initialize_runtime_module(void);
extern void lean_io_mark_end_initialization(void);
extern LeanObj* initialize_Dataplane(uint8_t, LeanObj*);
extern LeanObj* initialize_Body_FrameRaw(uint8_t, LeanObj*);
extern LeanObj* initialize_Ws_Decode(uint8_t, LeanObj*);
extern LeanObj* drorb_frame_request(LeanObj*);
extern LeanObj* drorb_ws_header(LeanObj*);
extern LeanObj* drorb_sarray_of_bytes(const uint8_t*, size_t);
extern size_t   drorb_sarray_len(LeanObj*);
extern const uint8_t* drorb_sarray_ptr(LeanObj*);
extern void     drorb_obj_dec(LeanObj*);
extern LeanObj* drorb_io_world(void);
extern int      drorb_io_ok(LeanObj*);

static size_t unhex(const char* s, uint8_t* out) {
    size_t n = 0;
    while (s[0] && s[1]) {
        int hi = s[0]<='9'?s[0]-'0':(s[0]|32)-'a'+10;
        int lo = s[1]<='9'?s[1]-'0':(s[1]|32)-'a'+10;
        out[n++] = (uint8_t)(hi*16+lo); s += 2;
    }
    return n;
}

int main(int argc, char** argv) {
    /* argv[1]=init {dataplane|framer|wsdecode}  argv[2]=seam {frame|ws}  argv[3]=hex */
    const char* init = argv[1], *seam = argv[2], *hex = argv[3];
    static uint8_t buf[262144];
    size_t n = unhex(hex, buf);
    lean_initialize_runtime_module();
    lean_io_mark_end_initialization();
    LeanObj* r;
    if (!strcmp(init,"dataplane")) r = initialize_Dataplane(1, drorb_io_world());
    else if (!strcmp(init,"framer")) r = initialize_Body_FrameRaw(1, drorb_io_world());
    else r = initialize_Ws_Decode(1, drorb_io_world());
    fprintf(stderr,"init io_ok=%d n=%zu\n", drorb_io_ok(r), n);
    drorb_obj_dec(r);
    LeanObj* arg = drorb_sarray_of_bytes(buf, n);
    LeanObj* out = !strcmp(seam,"frame") ? drorb_frame_request(arg) : drorb_ws_header(arg);
    size_t m = drorb_sarray_len(out);
    const uint8_t* p = drorb_sarray_ptr(out);
    fprintf(stderr,"OUT len=%zu tag=%d\n", m, m?p[0]:-1);
    drorb_obj_dec(out);
    fprintf(stderr,"REPRO_OK\n");
    return 0;
}
