/*
 * webrtc_udp.c — a minimal UDP client seam for the WebRTC/DTLS live driver.
 *
 * The WebRTC transport model (WebrtcTransport.lean) and the DTLS 1.2 record /
 * handshake bytes the live driver (WebrtcLive.lean) builds are pure Lean; the
 * cryptography is the verified EverCrypt boundary (Crypto.lean). To drive that
 * construction against a REAL WebRTC peer's DTLS engine (aiortc's OpenSSL
 * DTLS 1.2 server, conformance/webrtc/dtls_peer.py), this shim moves datagrams
 * across a real UDP socket. Unlike the one-shot wg_udp.c, a DTLS flight can span
 * several datagrams, so send and receive are separate bounded calls: the driver
 * sends its ClientHello, then reads the server's flight datagram(s) with a
 * timeout. It parses nothing, decrypts nothing, holds no protocol state — all
 * parsing/crypto/state lives in the proven/verified Lean. It is the untrusted
 * environment the proven core runs in, exactly like ffi/wg_udp.c.
 *
 * Exposed to Lean:
 *   drorb_wrtc_udp_connect : String -> UInt16 -> IO UInt32   (connected fd)
 *   drorb_wrtc_udp_send    : UInt32 -> ByteArray -> IO Unit
 *   drorb_wrtc_udp_recv    : UInt32 -> UInt32 -> IO (Option ByteArray)
 *   drorb_wrtc_udp_close   : UInt32 -> IO Unit
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

#define DRORB_WRTC_UDP_MAX 65536

static lean_object *wrtc_err(const char *msg) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

/* Create a UDP socket connected to host:port (host a dotted-quad IPv4 literal). */
LEAN_EXPORT lean_object *drorb_wrtc_udp_connect(lean_object *host, uint16_t port,
                                                lean_object *world) {
    (void)world;
    const char *h = lean_string_cstr(host);

    int fd = socket(AF_INET, SOCK_DGRAM, 0);
    if (fd < 0) return wrtc_err("webrtc_udp: socket() failed");

    struct sockaddr_in addr;
    memset(&addr, 0, sizeof(addr));
    addr.sin_family = AF_INET;
    addr.sin_port = htons(port);
    if (inet_pton(AF_INET, h, &addr.sin_addr) != 1) {
        close(fd);
        return wrtc_err("webrtc_udp: inet_pton() failed (need dotted-quad IPv4)");
    }
    if (connect(fd, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
        close(fd);
        return wrtc_err("webrtc_udp: connect() failed");
    }
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)fd));
}

/* Send one datagram on `fd`. */
LEAN_EXPORT lean_object *drorb_wrtc_udp_send(uint32_t fd, lean_object *payload,
                                             lean_object *world) {
    (void)world;
    size_t plen = lean_sarray_size(payload);
    ssize_t sent = send((int)fd, lean_sarray_cptr(payload), plen, 0);
    if (sent < 0) return wrtc_err("webrtc_udp: send() failed");
    return lean_io_result_mk_ok(lean_box(0));
}

/* Wait up to `timeout_ms` for one datagram on `fd`. some(bytes) or none on timeout. */
LEAN_EXPORT lean_object *drorb_wrtc_udp_recv(uint32_t fd, uint32_t timeout_ms,
                                             lean_object *world) {
    (void)world;
    int s = (int)fd;

    struct timeval tv;
    tv.tv_sec = timeout_ms / 1000;
    tv.tv_usec = (timeout_ms % 1000) * 1000;
    setsockopt(s, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));

    uint8_t buf[DRORB_WRTC_UDP_MAX];
    ssize_t n = recv(s, buf, sizeof(buf), 0);
    if (n < 0) {
        return lean_io_result_mk_ok(lean_box(0));   /* none */
    }

    lean_object *dg = lean_alloc_sarray(1, (size_t)n, (size_t)n);
    if (n) memcpy(lean_sarray_cptr(dg), buf, (size_t)n);
    lean_object *some = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(some, 0, dg);
    return lean_io_result_mk_ok(some);
}

LEAN_EXPORT lean_object *drorb_wrtc_udp_close(uint32_t fd, lean_object *world) {
    (void)world;
    close((int)fd);
    return lean_io_result_mk_ok(lean_box(0));
}
