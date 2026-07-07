/*
 * wg_udp.c — a minimal UDP client seam for the WireGuard live-handshake driver.
 *
 * The WireGuard model (Wireguard.lean) is sans-IO: it computes handshake and
 * transport bytes as pure functions. To VERIFY that construction against a real
 * WireGuard peer, this shim moves those bytes across a real UDP socket — send a
 * datagram to a peer, wait (bounded) for one reply. It parses nothing, decrypts
 * nothing, and holds no protocol state; all parsing/crypto/state lives in the
 * proven/verified Lean. It is the untrusted environment the proven core runs in,
 * exactly like ffi/mac_udp.c (the server sibling).
 *
 * Exposed to Lean:
 *   drorb_udp_socket   : String -> UInt16 -> IO UInt32          (connected fd)
 *   drorb_udp_send_recv: UInt32 -> ByteArray -> UInt32 -> IO (Option ByteArray)
 *   drorb_udp_close    : UInt32 -> IO Unit
 *
 * The responder side (a real peer is the INITIATOR, drorb responds) needs to
 * bind, receive a datagram from an as-yet-unknown source, then reply to that
 * exact source. These add a bound-socket recv/reply seam:
 *   drorb_udp_listen   : UInt16 -> IO UInt32                    (bound fd)
 *   drorb_udp_recv     : UInt32 -> UInt32 -> IO (Option ByteArray)
 *   drorb_udp_reply    : UInt32 -> ByteArray -> IO Unit
 * `drorb_udp_recv` records the datagram's source address; `drorb_udp_reply`
 * sends to that recorded address. Same discipline as the client seam: parses
 * nothing, decrypts nothing, holds no protocol state — all of that is the
 * proven/verified Lean.
 */

#include <lean/lean.h>

#include <stdint.h>
#include <string.h>
#include <errno.h>
#include <unistd.h>
#include <arpa/inet.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <sys/time.h>

#define DRORB_UDP_MAX 65536

static lean_object *udp_err(const char *msg) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

/* Create a UDP socket connected to host:port (host a dotted-quad IPv4 literal).
 * `connect` on a datagram socket just fixes the default peer; we still get the
 * source-filtering that lets recv() only see this peer's replies. */
LEAN_EXPORT lean_object *drorb_udp_socket(lean_object *host, uint16_t port,
                                          lean_object *world) {
    (void)world;
    const char *h = lean_string_cstr(host);

    int fd = socket(AF_INET, SOCK_DGRAM, 0);
    if (fd < 0) return udp_err("wg_udp: socket() failed");

    struct sockaddr_in addr;
    memset(&addr, 0, sizeof(addr));
    addr.sin_family = AF_INET;
    addr.sin_port = htons(port);
    if (inet_pton(AF_INET, h, &addr.sin_addr) != 1) {
        close(fd);
        return udp_err("wg_udp: inet_pton() failed (need dotted-quad IPv4)");
    }
    if (connect(fd, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
        close(fd);
        return udp_err("wg_udp: connect() failed");
    }
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)fd));
}

/* Send `payload` on `fd`, then wait up to `timeout_ms` for one reply datagram.
 * Returns some(bytes) on a reply, none on timeout. */
LEAN_EXPORT lean_object *drorb_udp_send_recv(uint32_t fd, lean_object *payload,
                                             uint32_t timeout_ms,
                                             lean_object *world) {
    (void)world;
    int s = (int)fd;

    size_t plen = lean_sarray_size(payload);
    ssize_t sent = send(s, lean_sarray_cptr(payload), plen, 0);
    if (sent < 0) return udp_err("wg_udp: send() failed");

    struct timeval tv;
    tv.tv_sec = timeout_ms / 1000;
    tv.tv_usec = (timeout_ms % 1000) * 1000;
    setsockopt(s, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));

    uint8_t buf[DRORB_UDP_MAX];
    ssize_t n = recv(s, buf, sizeof(buf), 0);
    if (n < 0) {
        /* timeout (EAGAIN/EWOULDBLOCK) or interrupt: no reply. */
        return lean_io_result_mk_ok(lean_box(0));   /* none */
    }

    lean_object *dg = lean_alloc_sarray(1, (size_t)n, (size_t)n);
    if (n) memcpy(lean_sarray_cptr(dg), buf, (size_t)n);
    lean_object *some = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(some, 0, dg);
    return lean_io_result_mk_ok(some);
}

LEAN_EXPORT lean_object *drorb_udp_close(uint32_t fd, lean_object *world) {
    (void)world;
    close((int)fd);
    return lean_io_result_mk_ok(lean_box(0));
}

/* ------------------------------------------------------------------ *
 * Responder seam: bind a UDP socket, recv from an unknown peer, reply *
 * to that peer. Single-peer, single-threaded live cross-check, so the *
 * last datagram's source is remembered in one static slot.           *
 * ------------------------------------------------------------------ */

static struct sockaddr_storage g_peer;
static socklen_t g_peerlen = 0;

/* Bind a UDP socket to 0.0.0.0:port and return the fd. */
LEAN_EXPORT lean_object *drorb_udp_listen(uint16_t port, lean_object *world) {
    (void)world;
    int fd = socket(AF_INET, SOCK_DGRAM, 0);
    if (fd < 0) return udp_err("wg_udp: socket() failed");

    int one = 1;
    setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));

    struct sockaddr_in addr;
    memset(&addr, 0, sizeof(addr));
    addr.sin_family = AF_INET;
    addr.sin_port = htons(port);
    addr.sin_addr.s_addr = htonl(INADDR_ANY);
    if (bind(fd, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
        close(fd);
        return udp_err("wg_udp: bind() failed");
    }
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)fd));
}

/* Wait up to `timeout_ms` for one datagram on the bound `fd`; record its
 * source address for a later reply. Returns some(bytes), or none on timeout. */
LEAN_EXPORT lean_object *drorb_udp_recv(uint32_t fd, uint32_t timeout_ms,
                                        lean_object *world) {
    (void)world;
    int s = (int)fd;

    struct timeval tv;
    tv.tv_sec = timeout_ms / 1000;
    tv.tv_usec = (timeout_ms % 1000) * 1000;
    setsockopt(s, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));

    uint8_t buf[DRORB_UDP_MAX];
    struct sockaddr_storage from;
    socklen_t fromlen = sizeof(from);
    ssize_t n = recvfrom(s, buf, sizeof(buf), 0,
                         (struct sockaddr *)&from, &fromlen);
    if (n < 0) {
        /* timeout (EAGAIN/EWOULDBLOCK) or interrupt: no datagram. */
        return lean_io_result_mk_ok(lean_box(0));   /* none */
    }
    memcpy(&g_peer, &from, (size_t)fromlen);
    g_peerlen = fromlen;

    lean_object *dg = lean_alloc_sarray(1, (size_t)n, (size_t)n);
    if (n) memcpy(lean_sarray_cptr(dg), buf, (size_t)n);
    lean_object *some = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(some, 0, dg);
    return lean_io_result_mk_ok(some);
}

/* Send `payload` to the address of the last datagram received on this fd. */
LEAN_EXPORT lean_object *drorb_udp_reply(uint32_t fd, lean_object *payload,
                                         lean_object *world) {
    (void)world;
    int s = (int)fd;
    if (g_peerlen == 0) return udp_err("wg_udp: reply before any recv");

    size_t plen = lean_sarray_size(payload);
    ssize_t sent = sendto(s, lean_sarray_cptr(payload), plen, 0,
                          (struct sockaddr *)&g_peer, g_peerlen);
    if (sent < 0) return udp_err("wg_udp: sendto() failed");
    return lean_io_result_mk_ok(lean_box(0));
}
