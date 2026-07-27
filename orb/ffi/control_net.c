/*
 * control_net.c — the untrusted TCP *server* seam for the control-plane driver.
 *
 * The proven `Control` / `Control.Channel` state machine is sans-IO: it computes
 * the ts2021 Noise-IK handshake and the AEAD-sealed control-frame bytes as pure
 * functions on the verified `Crypto` and `Wireguard.Noise` machinery. The client
 * side of the socket (connect / send / recv-exact / close) is already provided by
 * ffi/derp_net.c (drorb_tcp_connect …). This shim adds the ONLY server-side
 * capability the coord process needs and that derp_net.c lacks: bind+listen and
 * accept. It parses no frames, decrypts nothing, and holds no protocol state —
 * all framing, crypto, and handshake logic live in the proven/verified Lean. It
 * is the untrusted environment the proven control plane runs in, the server
 * sibling of ffi/derp_net.c.
 *
 * Exposed to Lean:
 *   drorb_tcp_listen : UInt16 -> IO UInt32                 (listening fd)
 *   drorb_tcp_accept : UInt32 -> UInt32 -> IO (Option UInt32)
 *                      (listenfd, timeoutMs) -> accepted fd, or none on timeout
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
#include <poll.h>

static lean_object *cn_err(const char *msg) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

/* Bind and listen on 127.0.0.1:port; return the listening fd. */
LEAN_EXPORT lean_object *drorb_tcp_listen(uint16_t port, lean_object *world) {
    (void)world;
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) return cn_err("control_net: socket() failed");

    int one = 1;
    setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));

    struct sockaddr_in addr;
    memset(&addr, 0, sizeof(addr));
    addr.sin_family = AF_INET;
    addr.sin_port = htons(port);
    addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    if (bind(fd, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
        close(fd);
        return cn_err("control_net: bind() failed");
    }
    if (listen(fd, 16) < 0) {
        close(fd);
        return cn_err("control_net: listen() failed");
    }
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)fd));
}

/* Accept one connection, waiting up to timeout_ms. some(fd) or none on timeout. */
LEAN_EXPORT lean_object *drorb_tcp_accept(uint32_t lfd, uint32_t timeout_ms,
                                          lean_object *world) {
    (void)world;
    struct pollfd pfd;
    pfd.fd = (int)lfd;
    pfd.events = POLLIN;
    int pr = poll(&pfd, 1, (int)timeout_ms);
    if (pr <= 0) return lean_io_result_mk_ok(lean_box(0)); /* none: timeout/error */

    int cfd = accept((int)lfd, NULL, NULL);
    if (cfd < 0) return lean_io_result_mk_ok(lean_box(0)); /* none */
    int one = 1;
    setsockopt(cfd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof(one));

    lean_object *some = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(some, 0, lean_box_uint32((uint32_t)cfd));
    return lean_io_result_mk_ok(some);
}
