/*
 * derp_relay_net.c — the untrusted TCP *server* seam for the DERP relay driver.
 *
 * The proven `Derp.Relay` state machine is sans-IO: it computes the routing
 * decision and the exact forwarded frame bytes as pure functions on the verified
 * `Derp` frame codec. This shim only moves those bytes over real sockets and
 * multiplexes the accepted connections. It parses no frames, decrypts nothing,
 * and holds no protocol state — all framing, crypto, routing, and the forwarding
 * discipline live in the proven/verified Lean. It is the untrusted environment
 * the proven relay runs in, the server sibling of ffi/derp_net.c.
 *
 * Symbols are `relay_`-prefixed so this object can be linked into the derp-relay
 * binary without colliding with the client seam (ffi/derp_net.c) elsewhere.
 *
 * Exposed to Lean:
 *   relay_tcp_listen     : UInt16 -> IO UInt32                 (listening fd, loopback)
 *   relay_tcp_listen_addr: String -> UInt16 -> IO UInt32       (listening fd, bind <host>)
 *   relay_tcp_accept     : UInt32 -> UInt32 -> IO (Option UInt32)
 *                          (listenfd, timeoutMs) -> accepted fd, or none on timeout
 *   relay_tcp_send       : UInt32 -> ByteArray -> IO Unit      (send all)
 *   relay_tcp_recv_exact : UInt32 -> UInt32 -> UInt32 -> IO (Option ByteArray)
 *                          (fd, nbytes, timeoutMs) -> read EXACTLY nbytes, or none
 *   relay_tcp_recv_some  : UInt32 -> UInt32 -> UInt32 -> IO (Option ByteArray)
 *                          (fd, maxbytes, timeoutMs) -> read whatever is available
 *   relay_poll_readable  : UInt32 -> UInt32 -> UInt32 -> IO Int32
 *                          (fdA, fdB, timeoutMs) -> 0 if A readable, 1 if B, -1 timeout
 *   relay_tcp_close      : UInt32 -> IO Unit
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
#include <poll.h>

static lean_object *relay_err(const char *msg) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

/* Bind and listen on 127.0.0.1:port; return the listening fd. */
LEAN_EXPORT lean_object *relay_tcp_listen(uint16_t port, lean_object *world) {
    (void)world;
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) return relay_err("derp_relay_net: socket() failed");

    int one = 1;
    setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));

    struct sockaddr_in addr;
    memset(&addr, 0, sizeof(addr));
    addr.sin_family = AF_INET;
    addr.sin_port = htons(port);
    addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    if (bind(fd, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
        close(fd);
        return relay_err("derp_relay_net: bind() failed");
    }
    if (listen(fd, 16) < 0) {
        close(fd);
        return relay_err("derp_relay_net: listen() failed");
    }
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)fd));
}

/* Bind and listen on <host>:port; host "" or "0.0.0.0" -> INADDR_ANY (routable),
 * otherwise the dotted-quad is parsed with inet_pton. Same fd contract as
 * relay_tcp_listen above; ONLY the bind address differs. Host glue: the relay's
 * proven forwarding (Derp.Server.dispatch) is unchanged; a routable listen just
 * lets a client on another host reach the same verified relay. */
LEAN_EXPORT lean_object *relay_tcp_listen_addr(lean_object *host_obj,
                                               uint16_t port, lean_object *world) {
    (void)world;
    const char *host = lean_string_cstr(host_obj);

    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) return relay_err("derp_relay_net: socket() failed");

    int one = 1;
    setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));

    struct sockaddr_in addr;
    memset(&addr, 0, sizeof(addr));
    addr.sin_family = AF_INET;
    addr.sin_port = htons(port);
    if (host[0] == '\0' || strcmp(host, "0.0.0.0") == 0) {
        addr.sin_addr.s_addr = htonl(INADDR_ANY);
    } else if (inet_pton(AF_INET, host, &addr.sin_addr) != 1) {
        close(fd);
        return relay_err("derp_relay_net: inet_pton(host) failed");
    }
    if (bind(fd, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
        close(fd);
        return relay_err("derp_relay_net: bind() failed");
    }
    if (listen(fd, 16) < 0) {
        close(fd);
        return relay_err("derp_relay_net: listen() failed");
    }
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)fd));
}

/* Accept one connection, waiting up to timeout_ms. some(fd) or none on timeout. */
LEAN_EXPORT lean_object *relay_tcp_accept(uint32_t lfd, uint32_t timeout_ms,
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

/* Send all bytes of `payload` on `fd`. */
LEAN_EXPORT lean_object *relay_tcp_send(uint32_t fd, lean_object *payload,
                                        lean_object *world) {
    (void)world;
    int s = (int)fd;
    size_t plen = lean_sarray_size(payload);
    const uint8_t *p = lean_sarray_cptr(payload);
    size_t off = 0;
    while (off < plen) {
        ssize_t n = send(s, p + off, plen - off, 0);
        if (n <= 0) return relay_err("derp_relay_net: send() failed");
        off += (size_t)n;
    }
    return lean_io_result_mk_ok(lean_box(0));
}

/* Read EXACTLY nbytes, waiting up to timeout_ms. some(bytes) or none. */
LEAN_EXPORT lean_object *relay_tcp_recv_exact(uint32_t fd, uint32_t nbytes,
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
            lean_dec_ref(out);
            return lean_io_result_mk_ok(lean_box(0)); /* none */
        }
        off += (size_t)n;
    }
    lean_object *some = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(some, 0, out);
    return lean_io_result_mk_ok(some);
}

/* Read whatever is available now (up to maxbytes), waiting up to timeout_ms for
 * the first byte. some(bytes, possibly short) or none on timeout/EOF. Used to
 * drain the client's HTTP Upgrade preamble, whose length is not known ahead. */
LEAN_EXPORT lean_object *relay_tcp_recv_some(uint32_t fd, uint32_t maxbytes,
                                             uint32_t timeout_ms,
                                             lean_object *world) {
    (void)world;
    int s = (int)fd;
    struct timeval tv;
    tv.tv_sec = timeout_ms / 1000;
    tv.tv_usec = (timeout_ms % 1000) * 1000;
    setsockopt(s, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));

    uint8_t *tmp = (uint8_t *)malloc((size_t)maxbytes);
    if (!tmp) return relay_err("derp_relay_net: malloc() failed");
    ssize_t n = recv(s, tmp, (size_t)maxbytes, 0);
    if (n <= 0) {
        free(tmp);
        return lean_io_result_mk_ok(lean_box(0)); /* none */
    }
    lean_object *out = lean_alloc_sarray(1, (size_t)n, (size_t)n);
    memcpy(lean_sarray_cptr(out), tmp, (size_t)n);
    free(tmp);
    lean_object *some = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(some, 0, out);
    return lean_io_result_mk_ok(some);
}

/* Wait until fdA or fdB is readable (or timeout). Returns 0 for A, 1 for B,
 * 0xFFFFFFFF on timeout. If both are ready, A wins. */
LEAN_EXPORT lean_object *relay_poll_readable(uint32_t fdA, uint32_t fdB,
                                             uint32_t timeout_ms,
                                             lean_object *world) {
    (void)world;
    struct pollfd pfds[2];
    pfds[0].fd = (int)fdA; pfds[0].events = POLLIN;
    pfds[1].fd = (int)fdB; pfds[1].events = POLLIN;
    int pr = poll(pfds, 2, (int)timeout_ms);
    uint32_t r = 0xFFFFFFFFu;
    if (pr > 0) {
        if (pfds[0].revents & (POLLIN | POLLHUP | POLLERR)) r = 0;
        else if (pfds[1].revents & (POLLIN | POLLHUP | POLLERR)) r = 1;
    }
    return lean_io_result_mk_ok(lean_box_uint32(r));
}

/* Poll an ARRAY of fds (the listen fd plus every live client fd) for
 * readability, waiting up to timeout_ms. Returns the index (into the array) of
 * the first readable fd, or 0xFFFFFFFF on timeout. A slot holding the sentinel
 * 0xFFFFFFFF casts to (int)-1, which poll() ignores — so closed connections can
 * keep their stable ConnId slot in the caller's array without being polled.
 * This is the N-connection analogue of relay_poll_readable, needed so a single
 * relay process can serve many stock-client DERP connections at once (each
 * magicsock holds a persistent home-DERP connection). */
LEAN_EXPORT lean_object *relay_poll_many(lean_object *fds, uint32_t timeout_ms,
                                         lean_object *world) {
    (void)world;
    size_t n = lean_array_size(fds);
    if (n == 0) return lean_io_result_mk_ok(lean_box_uint32(0xFFFFFFFFu));
    struct pollfd *pfds = (struct pollfd *)malloc(n * sizeof(struct pollfd));
    if (!pfds) return relay_err("derp_relay_net: malloc() failed");
    lean_object **cptr = lean_array_cptr(fds);
    for (size_t i = 0; i < n; i++) {
        uint32_t fd = lean_unbox_uint32(cptr[i]);
        pfds[i].fd = (int)fd;              /* 0xFFFFFFFF -> -1, ignored by poll */
        pfds[i].events = POLLIN;
        pfds[i].revents = 0;
    }
    int pr = poll(pfds, (nfds_t)n, (int)timeout_ms);
    uint32_t r = 0xFFFFFFFFu;
    if (pr > 0) {
        for (size_t i = 0; i < n; i++) {
            if (pfds[i].fd >= 0 &&
                (pfds[i].revents & (POLLIN | POLLHUP | POLLERR))) {
                r = (uint32_t)i;
                break;
            }
        }
    }
    free(pfds);
    return lean_io_result_mk_ok(lean_box_uint32(r));
}

LEAN_EXPORT lean_object *relay_tcp_close(uint32_t fd, lean_object *world) {
    (void)world;
    close((int)fd);
    return lean_io_result_mk_ok(lean_box(0));
}
