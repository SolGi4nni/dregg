/*
 * h2c_host.c — a minimal interactive TCP host for the verified HTTP/2
 * connection engine (H2/Conn.lean, exported via Reactor/H2Ingress.lean).
 *
 * This C shim is NOT verified and makes no protocol decision. Per accepted
 * connection it creates one engine state (`drorb_h2c_conn_init`), then loops:
 * read a chunk off the socket, hand it to `drorb_h2c_conn_feed`, write the
 * octets the engine returns, and close (cleanly: shutdown + drain) when the
 * engine raises its close flag. Preface validation, frame walking, HPACK,
 * stream FSM, SETTINGS/PING acknowledgement, flow-control pacing, GOAWAY and
 * RST_STREAM emission all happen inside the Lean engine.
 *
 * This is the interactive sibling of the dataplane's one-shot h2c path: an
 * external conformance battery (h2spec) needs SETTINGS synchronization, PING
 * liveness probes, and WINDOW_UPDATE-paced responses, all of which require the
 * connection to stay open across reads — exactly what this loop provides. The
 * same feed loop is the reference for hosting the engine inside the dataplane's
 * connection handler.
 *
 * Build: see build.sh next to this file (links .lake/build/lib/libdrorb.a
 * against the Lean runtime, same recipe as the Rust dataplane host).
 */

#include <lean/lean.h>

#include <errno.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <netinet/in.h>
#include <netinet/tcp.h>

/* Lean runtime bring-up (same sequence as the Rust dataplane host). */
extern void lean_initialize_runtime_module(void);
extern void lean_io_mark_end_initialization(void);
extern lean_object *initialize_Dataplane(uint8_t builtin, lean_object *world);

/* The verified engine seam (Reactor/H2Ingress.lean @[export]s). */
extern lean_object *drorb_h2c_conn_init(uint8_t unit);
extern lean_object *drorb_h2c_conn_feed(lean_object *state, lean_object *input);

/* Write all n bytes, retrying short writes. Returns 0 on success. */
static int write_all(int fd, const uint8_t *p, size_t n) {
    size_t off = 0;
    while (off < n) {
        ssize_t w = send(fd, p + off, n - off, 0);
        if (w < 0) { if (errno == EINTR) continue; return -1; }
        if (w == 0) return -1;
        off += (size_t)w;
    }
    return 0;
}

/* Serve one connection: thread the engine state across socket reads. */
static void serve_conn(int fd) {
    int nd = 1;
    setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &nd, sizeof(nd));

    /* An idle HTTP/2 connection with no traffic is reclaimed after this many
     * seconds; a conformance client acts well within it. */
    struct timeval tv = { .tv_sec = 15, .tv_usec = 0 };
    setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof(tv));

    lean_object *state = drorb_h2c_conn_init(0);

    uint8_t buf[65536];
    for (;;) {
        ssize_t n = recv(fd, buf, sizeof(buf), 0);
        if (n < 0) {
            if (errno == EINTR) continue;
            break; /* timeout or error: reclaim the connection */
        }
        if (n == 0) break; /* peer closed */

        lean_object *input = lean_alloc_sarray(1, (size_t)n, (size_t)n);
        memcpy(lean_sarray_cptr(input), buf, (size_t)n);

        /* feed consumes both arguments; the result is (state', out). */
        lean_object *r = drorb_h2c_conn_feed(state, input);
        state = lean_ctor_get(r, 0);
        lean_object *out = lean_ctor_get(r, 1);
        lean_inc(state);
        lean_inc(out);
        lean_dec(r);

        size_t len = lean_sarray_size(out);
        const uint8_t *p = lean_sarray_cptr(out);
        int close_after = (len > 0 && p[0] == 1);
        int wfail = 0;
        if (len > 1) wfail = write_all(fd, p + 1, len - 1);
        lean_dec(out);
        if (wfail) break;

        if (close_after) {
            /* Clean teardown: half-close our side, then drain the peer's
             * remaining octets so the kernel sends FIN, not RST. */
            shutdown(fd, SHUT_WR);
            struct timeval dtv = { .tv_sec = 1, .tv_usec = 0 };
            setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &dtv, sizeof(dtv));
            while (recv(fd, buf, sizeof(buf), 0) > 0) {}
            break;
        }
    }

    lean_dec(state);
    close(fd);
}

int main(int argc, char **argv) {
    uint16_t port = (argc > 1) ? (uint16_t)atoi(argv[1]) : 18081;

    lean_initialize_runtime_module();
    lean_object *res = initialize_Dataplane(1, lean_io_mk_world());
    if (!lean_io_result_is_ok(res)) {
        fprintf(stderr, "h2c-host: initialize_Dataplane failed\n");
        return 1;
    }
    lean_dec_ref(res);
    lean_io_mark_end_initialization();

    int lsock = socket(AF_INET, SOCK_STREAM, 0);
    if (lsock < 0) { perror("socket"); return 1; }
    int one = 1;
    setsockopt(lsock, SOL_SOCKET, SO_REUSEADDR, &one, sizeof(one));

    struct sockaddr_in addr;
    memset(&addr, 0, sizeof(addr));
    addr.sin_family = AF_INET;
    addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    addr.sin_port = htons(port);
    if (bind(lsock, (struct sockaddr *)&addr, sizeof(addr)) < 0) {
        perror("bind");
        return 1;
    }
    if (listen(lsock, 128) < 0) { perror("listen"); return 1; }

    fprintf(stderr, "h2c-host: listening on 127.0.0.1:%u (verified HTTP/2 engine, interactive)\n",
            (unsigned)port);

    /* One process per connection: a connection that idles until its receive
     * timeout must not head-of-line-block the accept loop (a conformance
     * battery opens each test's connection while the previous one may still
     * be draining). The child owns its fd and its own engine state; the
     * parent never touches Lean objects across the fork. */
    signal(SIGCHLD, SIG_IGN); /* auto-reap children */

    for (;;) {
        int cfd = accept(lsock, NULL, NULL);
        if (cfd < 0) { if (errno == EINTR) continue; break; }
        pid_t pid = fork();
        if (pid == 0) {
            close(lsock);
            serve_conn(cfd);
            _exit(0);
        }
        close(cfd);
        if (pid < 0) { perror("fork"); }
    }
    return 0;
}
