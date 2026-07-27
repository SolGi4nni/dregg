import Control.Store

/-!
# Control.Durable — what "committed" MEANS for the coordination store

`Control.Store` proves what a persisted log MEANS: `recoverStore_encodeStore`
(round-trip), `recover_torn_write` (a log torn mid-append still replays every
event committed before the tear), `restart_sound` (replaying the log
reconstructs exactly the live state). Every one of those theorems is a statement
about the BYTES THAT ARE ON THE DISK. None of them says how bytes get there.

That gap is this module. The commit path used to be:

* atomic rewrite — write `path.tmp`, then `rename` it over `path`;
* append — open `O_APPEND`, `write`, `flush`.

Both are correct against a **crashed process**: `rename` is atomic, so a
coordinator killed at any instant leaves either the old store or the new one,
never a spliced one; and an append that is cut short leaves a torn tail, which is
exactly `recover_torn_write`'s hypothesis. That is the guarantee an UPGRADE needs,
and it is the one the restart probe exercises (40x SIGKILL mid-write).

It is NOT durability against **power loss**. `write` returning, and `rename`
returning, mean the kernel has accepted the change into its page cache — not that
any of it reached the storage device. A coordinator that has answered a node "you
are registered, your address is 100.64.0.7" and then loses power can come back up
having never heard of that node: an ACKNOWLEDGED write, gone. Nothing in
`Control.Store` is violated — the log on disk replays perfectly — the log on disk
is simply missing the tail the client was told about.

## The two-fsync rule

Forcing the file is only half of it, and the missed half is the second:

1. `fsync` the FILE — its data and its metadata (the size an append just grew)
   are on stable storage.
2. `fsync` the CONTAINING DIRECTORY — the directory ENTRY is on stable storage.
   `rename` changes a directory, not the file; forcing the renamed file says
   nothing about the name that now points at it. Without this, a power cut after
   a rename can come back to the OLD name-to-inode mapping even though the new
   file's contents were forced.

An append needs (1) only: the directory entry already exists and was already made
durable when the store was created.

## What this module does NOT claim

The guarantee below is derived from the POSIX/Linux contract for `fsync`, not
measured: a power cut cannot be staged on a shared build box, and a device that
lies about its write cache breaks `fsync`'s contract underneath us. The claim is
exactly "we now issue the calls the contract requires, in the order it requires",
and the strength of the result is the strength of the device's honouring of them.
-/

namespace Control.Durable

/-- **Force a regular file to stable storage.** Thin wrapper over `fsync`
(`ffi/durable.c`); raises an `IO` error if the syscall fails, so a caller can
never report an acknowledged write it could not back. -/
@[extern "drorb_fsync_path"]
opaque fsyncPath (path : @& String) : IO Unit

/-- **Force a DIRECTORY to stable storage** — i.e. its entries, which is what a
`rename` mutates. Thin wrapper over `fsync` on an `O_RDONLY|O_DIRECTORY`
descriptor (`ffi/durable.c`). -/
@[extern "drorb_fsync_dir"]
opaque fsyncDir (path : @& String) : IO Unit

/-- The directory that CONTAINS `path` — the one whose entry a `rename` onto
`path` changes. A bare filename (no separator) lives in the working directory. -/
def parentDirOf (path : String) : String :=
  match (System.FilePath.mk path).parent with
  | some p => let s := p.toString; if s.isEmpty then "." else s
  | none   => "."

/-- `fsync` the directory containing `path`. -/
def fsyncParentOf (path : String) : IO Unit := fsyncDir (parentDirOf path)

/-- **Atomic + durable whole-file commit.** Write a sibling temp file, force ITS
data, `rename` it over `path`, then force the DIRECTORY so the rename itself
survives a power cut. On return: the bytes are the whole content of `path`, and
both a process kill and a power cut leave `path` as either the complete old
content or the complete new content. -/
def commitAtomic (path : String) (bytes : ByteArray) : IO Unit := do
  let tmp := path ++ ".tmp"
  IO.FS.writeBinFile tmp bytes
  fsyncPath tmp
  IO.FS.rename tmp path
  fsyncParentOf path

/-- **Durable append.** `O_APPEND` the bytes, flush the userspace buffer so they
have actually reached the kernel, then force the file. On return the appended
bytes are on stable storage; a power cut after this cannot lose them. A power cut
DURING it leaves a prefix — a torn tail — which is exactly the shape
`Control.Store.recover_torn_write` covers, so recovery is unchanged.

No directory fsync: appending mutates the file, not its name. -/
def commitAppend (path : String) (bytes : ByteArray) : IO Unit := do
  let h ← IO.FS.Handle.mk path IO.FS.Mode.append
  h.write bytes
  h.flush
  fsyncPath path

end Control.Durable
