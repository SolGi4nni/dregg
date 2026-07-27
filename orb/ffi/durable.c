/*
 * durable.c — the untrusted SYSCALL seam for durable commits.
 *
 * The commit POLICY (what to write, in what order, and what the resulting
 * guarantee is) is authored in Lean, in Control/Durable.lean. This file holds
 * the one capability the Lean core cannot express: forcing bytes that are
 * already in the kernel page cache out to stable storage. It parses nothing,
 * decides nothing, and holds no state — it opens the path it is handed, calls
 * fsync(2) on it, and closes it.
 *
 * Why two entry points and not one: on POSIX, fsync(2) on a FILE makes that
 * file's data and metadata durable, but it says NOTHING about the DIRECTORY
 * ENTRY that names it. A rename(2) is atomic with respect to a crash of the
 * PROCESS, yet the updated directory block may still be only in the page cache
 * when the power goes; the rename is made durable by fsync(2) on the containing
 * DIRECTORY. Both halves are needed, and the second is the one that is usually
 * missed.
 *
 * Exposed to Lean:
 *   drorb_fsync_path : String -> IO Unit   (fsync a regular file by path)
 *   drorb_fsync_dir  : String -> IO Unit   (fsync a directory by path)
 *
 * Both raise an IO error rather than returning silently: a durability call that
 * fails and is ignored is worse than no durability call, because the caller then
 * reports an ACKNOWLEDGED write it cannot back.
 */

#include <lean/lean.h>

#include <stdio.h>
#include <string.h>
#include <errno.h>
#include <fcntl.h>
#include <unistd.h>

static lean_object *dur_err(const char *op, const char *path, int e) {
    char buf[512];
    snprintf(buf, sizeof(buf), "durable: %s(%s) failed: %s", op, path, strerror(e));
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(buf)));
}

/* fsync a regular file named by path: its data AND its metadata (the size an
 * append just grew) are on stable storage when this returns ok. */
LEAN_EXPORT lean_object *drorb_fsync_path(b_lean_obj_arg path_obj, lean_object *world) {
    (void)world;
    const char *path = lean_string_cstr(path_obj);
    int fd = open(path, O_WRONLY);
    if (fd < 0) return dur_err("open", path, errno);
    if (fsync(fd) != 0) { int e = errno; close(fd); return dur_err("fsync", path, e); }
    if (close(fd) != 0) return dur_err("close", path, errno);
    return lean_io_result_mk_ok(lean_box(0));
}

/* fsync a DIRECTORY named by path: the directory entries it holds — in
 * particular the one a rename(2) just replaced — are on stable storage when
 * this returns ok. A directory must be opened O_RDONLY; O_WRONLY on a directory
 * is EISDIR. */
LEAN_EXPORT lean_object *drorb_fsync_dir(b_lean_obj_arg path_obj, lean_object *world) {
    (void)world;
    const char *path = lean_string_cstr(path_obj);
    int fd = open(path, O_RDONLY | O_DIRECTORY);
    if (fd < 0) return dur_err("opendir", path, errno);
    if (fsync(fd) != 0) { int e = errno; close(fd); return dur_err("fsyncdir", path, e); }
    if (close(fd) != 0) return dur_err("closedir", path, errno);
    return lean_io_result_mk_ok(lean_box(0));
}
