/*
 * drorb_ffi.c — the byte-marshalling adapter between the Rust dataplane and the
 * leanc-compiled proven serve.
 *
 * The Lean ByteArray ABI (an `sarray` object) is reached through accessors that
 * <lean/lean.h> defines as `static inline` — so they are not linkable symbols a
 * foreign caller can name. This shim includes lean.h and re-exposes exactly the
 * handful the host needs as plain C entry points. It parses nothing and holds no
 * state; it moves bytes across the sarray boundary and nothing else. The runtime
 * init and the `drorb_serve` call itself are made by the Rust host directly
 * against the real exported symbols.
 */
#include <lean/lean.h>
#include <string.h>
#include <stdint.h>

/* Wrap `n` host bytes in a fresh Lean ByteArray (sarray). The returned object is
 * owned; `drorb_serve` consumes it. */
lean_object *drorb_sarray_of_bytes(const uint8_t *p, size_t n) {
    lean_object *o = lean_alloc_sarray(1, n, n);
    if (n) memcpy(lean_sarray_cptr(o), p, n);
    return o;
}

/* Length and data pointer of a Lean ByteArray (the response sarray). */
size_t drorb_sarray_len(lean_object *o) { return lean_sarray_size(o); }
const uint8_t *drorb_sarray_ptr(lean_object *o) { return lean_sarray_cptr(o); }

/* Drop an owned Lean object reference. */
void drorb_obj_dec(lean_object *o) { lean_dec(o); }

/* Destructure an owned pair object (`A × B`): consumes `pair`, hands back its
 * two fields as owned references. Used by the interactive h2c host to split
 * `drorb_h2c_conn_feed`'s `(state', octets)` result. */
void drorb_pair_split(lean_object *pair, lean_object **fst, lean_object **snd) {
    lean_object *a = lean_ctor_get(pair, 0);
    lean_object *b = lean_ctor_get(pair, 1);
    lean_inc(a);
    lean_inc(b);
    lean_dec(pair);
    *fst = a;
    *snd = b;
}

/* The RealWorld token threaded through Lean IO / module initializers. */
lean_object *drorb_io_world(void) { return lean_io_mk_world(); }

/* A successful `IO Unit` result. Host-implemented `@[extern] ... : IO Unit`
 * hooks (the `drorb_tls_obs_*` observation seam) must hand one of these back to
 * the Lean caller; `lean_io_result_mk_ok` is a static inline in lean.h and so is
 * not nameable from Rust. These hooks never fail — an observation error is
 * swallowed host-side rather than surfaced into the proven connection. */
lean_object *drorb_io_unit_ok(void) {
    return lean_io_result_mk_ok(lean_box(0));
}

/* Wrap an owned Lean ByteArray as a successful `IO ByteArray` result. The TLS
 * static-file seam (`drorb_static_tls_serve`, crates/dataplane/src/tls.rs) hands
 * one of these back; `lean_io_result_mk_ok` is a static inline in lean.h and so
 * not nameable from Rust. */
lean_object *drorb_io_bytes_ok(lean_object *ba) {
    return lean_io_result_mk_ok(ba);
}

/* Did a Lean `IO α` result come back ok (vs. an error)? */
int drorb_io_ok(lean_object *o) { return lean_io_result_is_ok(o) ? 1 : 0; }
