/*
 * derp_net.c — a minimal blocking TCP client seam for the DERP live driver.
 *
 * DERP runs its length-prefixed frame protocol over a single TCP connection
 * (established by an HTTP Upgrade). The proven `Derp` model computes the exact
 * handshake / relay frame bytes as pure functions on the verified `Crypto`
 * crypto_box; this shim only moves those bytes over a real socket. It parses
 * nothing, decrypts nothing, and holds no protocol state — all framing, crypto,
 * and the handshake logic live in the proven/verified Lean. It is the untrusted
 * environment the proven core runs in, the TCP sibling of ffi/wg_udp.c.
 *
 * Exposed to Lean:
 *   drorb_tcp_connect    : String -> UInt16 -> IO UInt32           (connected fd)
 *   drorb_tcp_send       : UInt32 -> ByteArray -> IO Unit          (send all)
 *   drorb_tcp_recv_exact : UInt32 -> UInt32 -> UInt32 -> IO (Option ByteArray)
 *                          (fd, nbytes, timeoutMs) -> read EXACTLY nbytes, or none
 *   drorb_tcp_close      : UInt32 -> IO Unit
 */

#include <lean/lean.h>

#include <stdint.h>
#include <string.h>
#include <errno.h>
#include <unistd.h>
#include <arpa/inet.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <sys/time.h>

static lean_object *tcp_err(const char *msg) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

/* Connect a TCP socket to host:port (host a dotted-quad IPv4 literal). */
LEAN_EXPORT lean_object *drorb_tcp_connect(lean_object *host, uint16_t port,
                                           lean_object *world) {
    (void)world;
    const char *h = lean_string_cstr(host);

    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) return tcp_err("derp_net: socket() failed");

    struct sockaddr_in addr;
    memset(&addr, 0, sizeof(addr));
    addr.sin_family = AF_INET;
    addr.sin_port = htons(port);
    if (inet_pton(AF_INET, h, &addr.sin_addr) != 1) {
        close(fd);
        return tcp_err("derp_net: inet_pton() failed (need dotted-quad IPv4)");
    }
    if (connect(fd, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
        close(fd);
        return tcp_err("derp_net: connect() failed");
    }
    int one = 1;
    setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof(one));
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)fd));
}

/* Send all bytes of `payload` on `fd`. */
LEAN_EXPORT lean_object *drorb_tcp_send(uint32_t fd, lean_object *payload,
                                        lean_object *world) {
    (void)world;
    int s = (int)fd;
    size_t plen = lean_sarray_size(payload);
    const uint8_t *p = lean_sarray_cptr(payload);
    size_t off = 0;
    while (off < plen) {
        ssize_t n = send(s, p + off, plen - off, 0);
        if (n <= 0) return tcp_err("derp_net: send() failed");
        off += (size_t)n;
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* Read EXACTLY `nbytes` from `fd`, waiting up to `timeout_ms` total for the
 * stream to deliver them. Returns some(bytes) on success, none on timeout, EOF
 * before nbytes, or error. */
LEAN_EXPORT lean_object *drorb_tcp_recv_exact(uint32_t fd, uint32_t nbytes,
                                              uint32_t timeout_ms,
                                              lean_object *world) {
    (void)world;
    int s = (int)fd;

    struct timeval tv;
    tv.tv_sec = timeout_ms / 1000;
    tv.tv_usec = (timeout_ms % 1000) * 1000;
    setsockopt(s, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));

    lean_object *out = lean_alloc_sarray(1, (size_t)nbytes, (size_t)nbytes);
    uint8_t *buf = lean_sarray_cptr(out);
    size_t off = 0;
    while (off < nbytes) {
        ssize_t n = recv(s, buf + off, (size_t)nbytes - off, 0);
        if (n <= 0) {
            /* timeout (EAGAIN/EWOULDBLOCK), EOF (0), or error: no full read. */
            lean_dec_ref(out);
            return lean_io_result_mk_ok(lean_box(0));   /* none */
        }
        off += (size_t)n;
    }
    lean_object *some = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(some, 0, out);
    return lean_io_result_mk_ok(some);
}

LEAN_EXPORT lean_object *drorb_tcp_close(uint32_t fd, lean_object *world) {
    (void)world;
    close((int)fd);
    return lean_io_result_mk_ok(lean_box(0));
}
