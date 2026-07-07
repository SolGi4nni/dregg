/*
 * cgi_exec.c — the CGI/1.1 process-spawn shim (RFC 3875 §7).
 *
 * Backs the `@[extern "drorb_cgi_exec"]` primitive `Cgi.execBytes`. Given a
 * script path, a meta-variable environment block, and a request body, it runs
 * the script as a child process with the RFC 3875 meta-variable environment
 * installed, feeds the body on the child's stdin, captures the child's stdout,
 * and returns those bytes to Lean. This is the one boundary the Cgi library
 * models but does not itself execute: `Cgi.envList` builds the environment and
 * `Cgi.classify` frames the response; the actual `fork`/`execve` lives here.
 *
 * The environment block is the newline-separated `NAME=VALUE` rendering that
 * `Cgi.envBlockOf` produces from `Cgi.envList`; each line becomes one entry of
 * the child's `envp` verbatim (the value keeps every byte after the first `=`,
 * so a `QUERY_STRING=a=1&b=2` survives intact). No shell is involved — the
 * script is `execve`'d directly.
 *
 * Lean calling convention (matches ffi/crypto_shim.c):
 *   - String arguments arrive as borrowed `b_lean_obj_arg`; read with
 *     lean_string_cstr, do NOT free.
 *   - The stdin ByteArray arrives borrowed; read with lean_sarray_cptr /
 *     lean_sarray_size, do NOT free.
 *   - The result is a freshly allocated ByteArray (tag-1 sarray) owned by the
 *     caller.
 *
 * Precompiled to ffi/cgi_exec.o by ffi/build-cgi-shim.sh (TOML lakefiles cannot
 * compile a C source as a build target); the exes whose deployed serve reaches
 * a CGI route link it via moreLinkArgs.
 */
#include <lean/lean.h>
#include <string.h>
#include <stdlib.h>
#include <stdint.h>
#include <unistd.h>
#include <errno.h>
#include <sys/wait.h>

/* Build a NULL-terminated envp from a newline-separated "NAME=VALUE" block.
 * Each line becomes one malloc'd entry; the returned array is malloc'd. */
static char **cgi_build_envp(const char *block) {
    size_t n = 0;
    if (block && *block) {
        n = 1;
        for (const char *p = block; *p; ++p)
            if (*p == '\n') ++n;
    }
    char **envp = (char **) calloc(n + 1, sizeof(char *));
    if (!envp) return NULL;
    size_t i = 0;
    const char *start = block;
    while (block && *block && i < n) {
        const char *nl = strchr(start, '\n');
        size_t len = nl ? (size_t)(nl - start) : strlen(start);
        char *e = (char *) malloc(len + 1);
        if (!e) break;
        memcpy(e, start, len);
        e[len] = '\0';
        envp[i++] = e;
        if (!nl) break;
        start = nl + 1;
    }
    envp[i] = NULL;
    return envp;
}

static void cgi_free_envp(char **envp) {
    if (!envp) return;
    for (char **p = envp; *p; ++p) free(*p);
    free(envp);
}

/* Allocate an empty owned ByteArray. */
static lean_object *cgi_empty_bytes(void) {
    return lean_alloc_sarray(1, 0, 0);
}

LEAN_EXPORT lean_obj_res drorb_cgi_exec(b_lean_obj_arg script_obj,
                                        b_lean_obj_arg env_obj,
                                        b_lean_obj_arg stdin_obj) {
    const char *script   = lean_string_cstr(script_obj);
    const char *envblock = lean_string_cstr(env_obj);
    const uint8_t *inbuf = lean_sarray_cptr((lean_object *) stdin_obj);
    size_t inlen         = lean_sarray_size((lean_object *) stdin_obj);

    char **envp = cgi_build_envp(envblock);
    if (!envp) return cgi_empty_bytes();

    int inpipe[2]  = { -1, -1 };
    int outpipe[2] = { -1, -1 };
    if (pipe(inpipe) != 0 || pipe(outpipe) != 0) {
        if (inpipe[0]  >= 0) { close(inpipe[0]);  close(inpipe[1]); }
        cgi_free_envp(envp);
        return cgi_empty_bytes();
    }

    pid_t pid = fork();
    if (pid < 0) {
        close(inpipe[0]);  close(inpipe[1]);
        close(outpipe[0]); close(outpipe[1]);
        cgi_free_envp(envp);
        return cgi_empty_bytes();
    }

    if (pid == 0) {
        /* child: wire pipes to stdin/stdout, exec the script directly */
        dup2(inpipe[0], 0);
        dup2(outpipe[1], 1);
        close(inpipe[0]);  close(inpipe[1]);
        close(outpipe[0]); close(outpipe[1]);
        char *argv[] = { (char *) script, NULL };
        execve(script, argv, envp);
        _exit(127);  /* exec failed */
    }

    /* parent */
    close(inpipe[0]);
    close(outpipe[1]);

    /* feed the request body on the child's stdin, then signal EOF */
    size_t off = 0;
    while (off < inlen) {
        ssize_t w = write(inpipe[1], inbuf + off, inlen - off);
        if (w < 0) { if (errno == EINTR) continue; break; }
        if (w == 0) break;
        off += (size_t) w;
    }
    close(inpipe[1]);

    /* drain the child's stdout in full */
    size_t cap = 4096, len = 0;
    uint8_t *buf = (uint8_t *) malloc(cap);
    if (!buf) {
        close(outpipe[0]);
        waitpid(pid, NULL, 0);
        cgi_free_envp(envp);
        return cgi_empty_bytes();
    }
    for (;;) {
        if (len == cap) {
            size_t ncap = cap * 2;
            uint8_t *nb = (uint8_t *) realloc(buf, ncap);
            if (!nb) break;
            buf = nb; cap = ncap;
        }
        ssize_t r = read(outpipe[0], buf + len, cap - len);
        if (r < 0) { if (errno == EINTR) continue; break; }
        if (r == 0) break;
        len += (size_t) r;
    }
    close(outpipe[0]);

    int status;
    waitpid(pid, &status, 0);
    cgi_free_envp(envp);

    lean_object *out = lean_alloc_sarray(1, len, len);
    if (len) memcpy(lean_sarray_cptr(out), buf, len);
    free(buf);
    return out;
}
