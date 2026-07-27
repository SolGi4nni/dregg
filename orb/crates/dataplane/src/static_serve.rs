//! Host-side static-file streaming (roadmap Stage 3, `BodySrc.staticFile`).
//!
//! The proven core DECIDES the static lane's response — which file to serve,
//! and the complete serving PLAN (status, every header byte, and the exact
//! file byte windows) — as batch-small decisions. This module is the HOST
//! side of that split for LARGE local bodies: it opens the resolved file,
//! writes the plan's response bytes, and streams the planned file windows to
//! the client one bounded block at a time, so the whole body never passes
//! through the cons-list core and the host's per-request working set is one
//! block regardless of the file size.
//!
//! ## The path decision IS the proven core's (not a host mirror)
//!
//! The traversal decision — split the target, percent-decode each segment
//! exactly ONCE (percent-decode is not idempotent, so `%252e%252e` cannot be
//! double-decoded into `..`), gate every decoded segment on UTF-8
//! well-formedness, and remove dot-segments with `..` never popping above the
//! root — is made by the proven `Route.StaticResolve.resolveRel`, crossed per
//! request as `drorb_static_resolve` (via [`StaticRoot::resolve_with`]). The
//! host supplies only the boundary the theorems leave to it: the
//! serving-prefix strip before the crossing, and the canonicalize +
//! root-prefix re-check after (which also rejects symlink escapes —
//! filesystem state the core does not see). The core-side theorems
//! (`resolveRel_confined`, `decode_once_only`, `resolveRel_no_dot`) hold for
//! EVERY input.
//!
//! ## The RESPONSE decision IS the proven core's too (the serving plan)
//!
//! Everything after path resolution is ONE crossing of
//! `Route.StaticDecide.staticDecideC` (`drorb_static_decide`, via
//! [`decide_frame`]): the host sends its boundary facts — found, the real
//! file's byte length and mtime, its post-canonicalize name, the client's
//! keep-alive intent — plus the RAW request bytes, and gets back the PLAN it
//! executes verbatim ([`PlanOut`]):
//!
//! * a verbatim response (`404` — the model's `notFoundResp` bytes exactly,
//!   `notFound_split`; `405` with `Allow`; `304` with the representation
//!   validators, decided by the PROVEN `ConditionalRequest.ifNoneMatchMatches`
//!   matcher plus the exact-date `If-Modified-Since` compare,
//!   `stage_bridge_304`; `416` with `Content-Range: bytes */len`; and every
//!   `HEAD` head);
//! * a `200` head (with `ETag`/`Last-Modified` validators, `okHead2`) to
//!   stream the whole file after;
//! * a `206` head plus ONE file window — proven to be exactly the requested
//!   byte range, in place and in bounds (`window_exact`, grounded on the
//!   proven `MultiRange.slice_length`/`slice_decomposition`);
//! * a `206 multipart/byteranges` head plus per-part prefaces/windows and the
//!   closing delimiter — proven to reassemble to EXACTLY the proven
//!   `MultiRange.multipartBody` (`partsWire_eq_multipartBody`), with the
//!   framed `Content-Length` counting it exactly (`multiLen_exact`).
//!
//! The host assembles NO header bytes, owns NO MIME row, compares NO
//! precondition, and parses NO range: it opens files, frames boundary facts,
//! and executes plans. An EMPTY seam output (malformed frame) fails safe: the
//! connection is dropped, never host-built bytes. A file that shrinks between
//! metadata and read fails the same way (never a silently short body).
//!
//! Both crossings run through the runtime-owner thread's job channel
//! (`serve.rs`, `Seam::StaticResolve` / `Seam::StaticDecide`), so the
//! multi-owner runtime-safety analysis applies unchanged.
//!
//! Gated entirely on `DRORB_STATIC_ROOT`: unset ⇒ no static lane ⇒ the default
//! serve path is byte-identical and untouched.

use std::io::{Read, Seek, SeekFrom, Write};
#[cfg(target_os = "linux")]
use std::os::unix::io::AsRawFd;
use std::os::unix::io::RawFd;
use std::path::PathBuf;
use std::sync::OnceLock;

/// Process-global static root, initialised once from `DRORB_STATIC_ROOT`. `None`
/// when the variable is unset / not a directory (no static lane configured, the
/// default serve path untouched).
static STATIC_ROOT: OnceLock<Option<StaticRoot>> = OnceLock::new();

/// The configured static root, or `None` when `DRORB_STATIC_ROOT` is unset.
pub fn get() -> Option<&'static StaticRoot> {
    STATIC_ROOT.get_or_init(StaticRoot::from_env).as_ref()
}

/// The bounded copy buffer for the streaming file pump: one block held at a time,
/// so peak host memory for a static serve is this plus the response head,
/// regardless of the file size. A slow client back-pressures the read because the
/// next file read only happens after the current block is written to the client.
const STREAM_CHUNK: usize = 64 * 1024;

/// Build the `drorb_static_decide` input frame from the host's boundary facts:
/// `flags(1) :: len(8 BE) :: mtime(8 BE) :: nameLen(2 BE) :: name :: request`,
/// flags bit 0 = the client's keep-alive intent, bit 1 = found (a regular file
/// resolved; its length/mtime/name follow), bit 2 = redir (the resolved entity
/// is a directory and the request target lacks its trailing slash — the core
/// answers a `301` to the target plus `/`).
fn decide_frame(
    found: bool,
    redir: bool,
    ka: bool,
    len: u64,
    mtime: u64,
    name: &[u8],
    req: &[u8],
) -> Vec<u8> {
    let flags: u8 = (ka as u8) | ((found as u8) << 1) | ((redir as u8) << 2);
    let mut f = Vec::with_capacity(19 + name.len() + req.len());
    f.push(flags);
    f.extend_from_slice(&len.to_be_bytes());
    f.extend_from_slice(&mtime.to_be_bytes());
    f.extend_from_slice(&(name.len() as u16).to_be_bytes());
    f.extend_from_slice(name);
    f.extend_from_slice(req);
    f
}

/// A decoded serving plan (`Route.StaticDecide.encodePlan`, the seam's output).
/// The host EXECUTES this; every byte it writes besides file content is inside it.
enum PlanOut {
    /// Write these bytes verbatim (`404`/`405`/`416`/`304` and every `HEAD`).
    Reply(Vec<u8>),
    /// Write the head, then stream the whole file.
    Whole(Vec<u8>),
    /// Write the head, then stream the file window `[off, off+n)` (a single-range
    /// `206` — the window proven exact core-side, `window_exact`).
    Window { off: u64, n: u64, head: Vec<u8> },
    /// Write the head, then for each `(preface, off, n)` the preface and the file
    /// window, then the tail (a `206 multipart/byteranges` — proven to reassemble
    /// to the proven `multipartBody`, `partsWire_eq_multipartBody`).
    Parts {
        head: Vec<u8>,
        tail: Vec<u8>,
        segs: Vec<(Vec<u8>, u64, u64)>,
    },
}

fn be_u64(b: &[u8]) -> u64 {
    u64::from_be_bytes(b.try_into().unwrap_or([0; 8]))
}

/// What the host's filesystem resolution found for a `GET`/`HEAD` target — the
/// boundary fact the decide seam consumes (see [`StaticRoot::resolve_entity`]).
enum Resolved {
    /// A regular file to serve (post-canonicalize, under the root).
    File(PathBuf),
    /// A directory requested WITHOUT its trailing slash: the core answers a
    /// `301` redirect to the target plus `/`.
    Redirect,
    /// Nothing servable — missing, escaped, malformed, or a directory with no
    /// `index.html`.
    Missing,
}

/// Decode the seam's plan encoding: tag byte then the shape
/// (`1` reply · `2` whole · `3` window `off(8) n(8) head` ·
/// `4` parts `headLen(4) head tailLen(2) tail count(2) {preLen(2) pre off(8) n(8)}*`).
/// `None` on any malformed shape — the caller fails safe (drops the connection).
fn parse_plan(out: &[u8]) -> Option<PlanOut> {
    let (&tag, rest) = out.split_first()?;
    match tag {
        1 => Some(PlanOut::Reply(rest.to_vec())),
        2 => Some(PlanOut::Whole(rest.to_vec())),
        3 => {
            if rest.len() < 16 {
                return None;
            }
            Some(PlanOut::Window {
                off: be_u64(&rest[..8]),
                n: be_u64(&rest[8..16]),
                head: rest[16..].to_vec(),
            })
        }
        4 => {
            let mut p = rest;
            fn take<'a>(p: &mut &'a [u8], n: usize) -> Option<&'a [u8]> {
                if p.len() < n {
                    return None;
                }
                let (a, b) = p.split_at(n);
                *p = b;
                Some(a)
            }
            let head_len = u32::from_be_bytes(take(&mut p, 4)?.try_into().ok()?) as usize;
            let head = take(&mut p, head_len)?.to_vec();
            let tail_len = u16::from_be_bytes(take(&mut p, 2)?.try_into().ok()?) as usize;
            let tail = take(&mut p, tail_len)?.to_vec();
            let count = u16::from_be_bytes(take(&mut p, 2)?.try_into().ok()?) as usize;
            let mut segs = Vec::with_capacity(count);
            for _ in 0..count {
                let pre_len = u16::from_be_bytes(take(&mut p, 2)?.try_into().ok()?) as usize;
                let pre = take(&mut p, pre_len)?.to_vec();
                let off = be_u64(take(&mut p, 8)?);
                let n = be_u64(take(&mut p, 8)?);
                segs.push((pre, off, n));
            }
            if !p.is_empty() {
                return None;
            }
            Some(PlanOut::Parts { head, tail, segs })
        }
        _ => None,
    }
}

/// A configured static-file document root and URL prefix. The core's decisions
/// (which file, the whole serving plan) are realized here; this struct only maps a
/// request target to a file under the root and executes plans.
pub struct StaticRoot {
    /// The document root (canonicalized at construction). No resolved path escapes
    /// it.
    root: PathBuf,
    /// The URL path prefix a request must carry to be served statically
    /// (default `/static/`). The remainder is resolved under `root`.
    prefix: String,
    /// The `try_files` SPA fallback index, RELATIVE to `root` (e.g. `index.html`),
    /// from `DRORB_STATIC_SPA_INDEX` / `DRORB_STATIC_SPA`. `None` disables the
    /// fallback (a missing target is the core's `404`). When set, a `GET`/`HEAD`
    /// whose target names no regular file under the root is served this index
    /// instead (a `200`), so client-side routes resolve. The index is a FIXED
    /// path re-checked under the root, so the proven traversal confinement is
    /// UNCHANGED — the escaping/unmatched target is never opened, only the index.
    spa_index: Option<String>,
}

/// What the host records after a STREAMED static serve: the response head (status
/// line + headers, for metrics / access log), the total bytes written, and whether
/// the client connection may stay open. The body itself was written straight to the
/// client and never buffered whole.
pub struct StaticOutcome {
    pub head: Vec<u8>,
    pub bytes: u64,
    pub keepalive: bool,
}

/// One segment of a linearized serving plan (see [`StaticPlan`]): literal bytes
/// that go on the wire verbatim, or a file window an async reactor moves straight
/// from the page cache to the socket.
pub enum StaticSeg {
    /// Literal response bytes — a head, a multipart preface/tail, or a whole
    /// verbatim reply (`404`/`405`/`416`/`304`/`301`, and every `HEAD`).
    Buf(Vec<u8>),
    /// The file window `[off, off+n)` to place on the wire from the plan's file.
    Window { off: u64, n: u64 },
}

/// A static serving plan linearized for an ASYNC reactor (the io_uring shard):
/// the proven decision — [`handle_streaming_zc`](StaticRoot::handle_streaming_zc)'s
/// resolve + decide crossing — already made, but instead of the bytes being
/// written synchronously they are handed back as an ordered [`StaticSeg`] sequence
/// plus the open file the windows read from. The reactor walks the segments in
/// order (literals as ordinary sends, file windows via `IORING_OP_SPLICE`
/// file->pipe->socket), producing exactly the same wire bytes as the synchronous
/// `sendfile(2)` path — the plan, and thus every byte besides file content, is the
/// proven core's. `file` is kept alive for the whole async send; it is `None` for a
/// bodyless reply.
pub struct StaticPlan {
    pub segs: Vec<StaticSeg>,
    pub file: Option<std::fs::File>,
    pub keepalive: bool,
    /// The response head (status line + headers), for metrics / access log — the
    /// first literal segment for a file plan, or the whole reply's head for a
    /// verbatim plan.
    pub head: Vec<u8>,
}

/// The fail-safe error for a missing/malformed plan: the caller drops the
/// connection rather than building response bytes host-side.
fn seam_err(what: &'static str) -> std::io::Error {
    std::io::Error::new(std::io::ErrorKind::InvalidData, what)
}

impl StaticRoot {
    /// Build from `DRORB_STATIC_ROOT` (the document root) and `DRORB_STATIC_PREFIX`
    /// (the URL prefix, default `/static/`). Returns `None` when the root is unset or
    /// does not canonicalize to an existing directory — the static lane is then
    /// inert and the default serve path is untouched.
    pub fn from_env() -> Option<StaticRoot> {
        let root = std::env::var("DRORB_STATIC_ROOT").ok()?;
        let root = std::fs::canonicalize(&root).ok()?;
        if !root.is_dir() {
            return None;
        }
        let mut prefix = std::env::var("DRORB_STATIC_PREFIX").unwrap_or_else(|_| "/static/".into());
        if !prefix.starts_with('/') {
            prefix.insert(0, '/');
        }
        if !prefix.ends_with('/') {
            prefix.push('/');
        }
        // try_files SPA fallback: `DRORB_STATIC_SPA_INDEX` names the fallback index
        // (relative to the root); `DRORB_STATIC_SPA` truthy selects the default
        // `index.html`. Unset / falsey ⇒ no fallback (a miss is the core's 404).
        let spa_index = std::env::var("DRORB_STATIC_SPA_INDEX")
            .ok()
            .or_else(|| {
                std::env::var("DRORB_STATIC_SPA").ok().and_then(|v| {
                    let v = v.trim();
                    if v.is_empty()
                        || v.eq_ignore_ascii_case("0")
                        || v.eq_ignore_ascii_case("false")
                    {
                        None
                    } else if v.eq_ignore_ascii_case("1") || v.eq_ignore_ascii_case("true") {
                        Some("index.html".to_string())
                    } else {
                        Some(v.to_string())
                    }
                })
            })
            .map(|s| s.trim_start_matches('/').trim().to_string())
            .filter(|s| !s.is_empty());
        Some(StaticRoot {
            root,
            prefix,
            spa_index,
        })
    }

    /// Is this request one the static lane should serve? ANY method whose target
    /// begins with the configured prefix — the METHOD decision (`GET`/`HEAD`
    /// serve, everything else the core's `405`, `plan_405`) is the proven core's,
    /// so a `POST /static/…` must reach the crossing rather than fall through.
    pub fn is_static_path(&self, req: &[u8]) -> bool {
        let Some((method, target)) = request_line(req) else {
            return false;
        };
        if method.is_empty() {
            return false;
        }
        target_path(target).starts_with(self.prefix.as_bytes())
    }

    /// Resolve a request target to a file path under the root, or `None` when the
    /// target is malformed, escapes the root, or names no regular file.
    ///
    /// The DECISION — split, percent-decode ONCE, UTF-8 gate, dot-segment walk
    /// clamped at the root — is the proven core's: `core` crosses
    /// `drorb_static_resolve` (`Route.StaticResolve.resolveRel`) and returns the
    /// '/'-joined resolved relative path, or `None` on the core's reject. The host
    /// contributes only its boundary: the prefix strip before the crossing, and
    /// canonicalize + root-prefix re-check after (filesystem state — symlinks,
    /// existence — the core does not see).
    pub fn resolve_with(
        &self,
        target: &[u8],
        core: impl FnOnce(&[u8]) -> Option<Vec<u8>>,
    ) -> Option<PathBuf> {
        let path = target_path(target);
        // Strip the serving prefix; the remainder is the path under the root.
        let rel = path.strip_prefix(self.prefix.as_bytes())?;
        // The proven resolution: `0x01 ++ joined` was already unwrapped by the
        // seam caller; `None` is the core's reject (or a gone serve thread —
        // fail-safe 404 either way).
        let joined = core(rel)?;
        // The core proved every resolved segment UTF-8 well-formed
        // (`resolveRel`'s gate); this conversion is marshalling, not a decision —
        // a failure would mean seam corruption, and fails safe.
        let joined = String::from_utf8(joined).ok()?;
        let mut candidate = self.root.clone();
        if !joined.is_empty() {
            candidate.push(&joined);
        }
        // Canonicalize and re-check containment: the resolved real path must keep the
        // document root as a prefix (belt-and-suspenders over the proven walk;
        // also rejects symlink escapes).
        let real = std::fs::canonicalize(&candidate).ok()?;
        if !real.starts_with(&self.root) {
            return None;
        }
        if !real.is_file() {
            return None;
        }
        Some(real)
    }

    /// Resolve a `GET`/`HEAD` target to a filesystem boundary fact, applying the
    /// `try_files` SPA fallback: the primary resolution ([`resolve_primary`]) is
    /// tried first, and only a [`Resolved::Missing`] (with an SPA index
    /// configured) is turned into the fixed, root-confined index file — served
    /// `200`, so a client-side route resolves to the app shell. `File`/`Redirect`
    /// pass through unchanged, and the confinement is unchanged: the index is a
    /// constant path re-checked under the root, so the escaping/unmatched target
    /// is never opened.
    ///
    /// [`resolve_primary`]: StaticRoot::resolve_primary
    fn resolve_entity(
        &self,
        target: &[u8],
        core: impl FnOnce(&[u8]) -> Option<Vec<u8>>,
    ) -> Resolved {
        match self.resolve_primary(target, core) {
            Resolved::Missing => match self.spa_index_file() {
                Some(idx) => Resolved::File(idx),
                None => Resolved::Missing,
            },
            other => other,
        }
    }

    /// The configured SPA fallback index as a real, root-confined file, or `None`
    /// when no SPA index is configured or it does not resolve to a regular file
    /// under the root. Canonicalize + root-prefix re-check keeps the fallback
    /// confined (rejects a symlinked index that escapes), exactly like the primary
    /// path — the fallback introduces no new traversal surface.
    fn spa_index_file(&self) -> Option<PathBuf> {
        let rel = self.spa_index.as_ref()?;
        let candidate = self.root.join(rel);
        let real = std::fs::canonicalize(&candidate).ok()?;
        if !real.starts_with(&self.root) {
            return None;
        }
        if real.is_file() { Some(real) } else { None }
    }

    /// The primary filesystem resolution (no SPA fallback): a regular file to
    /// serve, a directory that must be redirected to its trailing-slash form, or
    /// nothing servable.
    ///
    /// The path DECISION is the proven core's (as in [`resolve_with`]); the host
    /// adds only the filesystem facts the theorems leave to it — canonicalize +
    /// root re-check, regular-file vs directory, and (for a directory served
    /// with its trailing slash) its `index.html`. A directory requested WITHOUT
    /// the trailing slash yields [`Resolved::Redirect`]: the `301` and its
    /// `Location` are then the core's (`Route.StaticDecide.resp301`).
    ///
    /// [`resolve_with`]: StaticRoot::resolve_with
    fn resolve_primary(
        &self,
        target: &[u8],
        core: impl FnOnce(&[u8]) -> Option<Vec<u8>>,
    ) -> Resolved {
        let path = target_path(target);
        let Some(rel) = path.strip_prefix(self.prefix.as_bytes()) else {
            return Resolved::Missing;
        };
        let Some(joined) = core(rel) else {
            return Resolved::Missing;
        };
        let Ok(joined) = String::from_utf8(joined) else {
            return Resolved::Missing;
        };
        let mut candidate = self.root.clone();
        if !joined.is_empty() {
            candidate.push(&joined);
        }
        let Ok(real) = std::fs::canonicalize(&candidate) else {
            return Resolved::Missing;
        };
        if !real.starts_with(&self.root) {
            return Resolved::Missing;
        }
        if real.is_file() {
            return Resolved::File(real);
        }
        if real.is_dir() {
            // Directory WITHOUT its trailing slash: the core redirects to the
            // slash form. WITH the slash: serve its `index.html` when present
            // (a directory with no index resolves to nothing — a `404`).
            if !path.ends_with(b"/") {
                return Resolved::Redirect;
            }
            let idx = real.join("index.html");
            if let Ok(ireal) = std::fs::canonicalize(&idx) {
                if ireal.starts_with(&self.root) && ireal.is_file() {
                    return Resolved::File(ireal);
                }
            }
        }
        Resolved::Missing
    }

    /// Serve a static request by EXECUTING the core's plan: cross the path
    /// decision (`resolve`, for a `GET`/`HEAD`), frame the boundary facts, cross
    /// the response decision (`decide`), then write exactly what the plan says —
    /// verbatim bytes, or a head followed by the planned file windows streamed
    /// with a bounded buffer (never the whole file in memory).
    ///
    /// `Err` is returned on a client write failure, a gone/malformed seam, or a
    /// file that shrank below a planned window (the connection must be dropped —
    /// the alternatives would be host-built bytes or a silently short body).
    pub fn handle_streaming<W: Write>(
        &self,
        req: &[u8],
        keepalive_req: bool,
        client: &mut W,
        resolve: impl FnOnce(&[u8]) -> Option<Vec<u8>>,
        decide: impl FnOnce(&[u8]) -> Option<Vec<u8>>,
    ) -> std::io::Result<StaticOutcome> {
        self.handle_streaming_zc(req, keepalive_req, client, None, resolve, decide)
    }

    /// Same as [`Self::handle_streaming`], but when `zc_fd` is the client
    /// socket's raw fd (a blocking Linux socket) the planned FILE windows are
    /// placed on the wire with `sendfile(2)` — the body bytes move file->socket
    /// inside the kernel, never copied through this process's address space. The
    /// head and part prefaces still go through `client`; on the production path
    /// `client` IS that same socket, so those bytes are flushed before each
    /// spliced window and wire ordering holds. `None` (tests, non-Linux) keeps
    /// the bounded userspace pump. The wire output is byte-identical either way
    /// (exactly the file bytes `[off, off+n)`); a file that shrank below a
    /// planned window is an error on both paths (fail-safe: drop the connection).
    #[allow(clippy::too_many_arguments)]
    pub fn handle_streaming_zc<W: Write>(
        &self,
        req: &[u8],
        keepalive_req: bool,
        client: &mut W,
        zc_fd: Option<RawFd>,
        resolve: impl FnOnce(&[u8]) -> Option<Vec<u8>>,
        decide: impl FnOnce(&[u8]) -> Option<Vec<u8>>,
    ) -> std::io::Result<StaticOutcome> {
        let Some((method, target)) = request_line(req) else {
            return Err(seam_err(
                "static lane invoked on an unparseable request line",
            ));
        };

        // Filesystem boundary facts. Only a GET/HEAD can use a resolved file; the
        // METHOD decision itself is the core's — for any other method the core
        // answers the 405 off the request bytes regardless of these facts.
        let mut file = None;
        let mut len = 0u64;
        let mut mtime = 0u64;
        let mut name: Vec<u8> = Vec::new();
        let mut redir = false;
        if method == b"GET" || method == b"HEAD" {
            match self.resolve_entity(target, resolve) {
                Resolved::File(path) => {
                    if let Ok(f) = std::fs::File::open(&path) {
                        if let Ok(md) = f.metadata() {
                            len = md.len();
                            mtime = md
                                .modified()
                                .ok()
                                .and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok())
                                .map(|d| d.as_secs())
                                .unwrap_or(0);
                            name = path.file_name().map(os_bytes).unwrap_or(&[]).to_vec();
                            file = Some(f);
                        }
                    }
                }
                // A directory without its trailing slash: the core answers the
                // 301 off the request target; no file is opened.
                Resolved::Redirect => redir = true,
                Resolved::Missing => {}
            }
        }
        let found = file.is_some();

        // ONE crossing decides the whole response.
        let out = decide(&decide_frame(
            found,
            redir,
            keepalive_req,
            len,
            mtime,
            &name,
            req,
        ))
        .ok_or_else(|| seam_err("static decide seam returned no plan"))?;
        let plan = parse_plan(&out)
            .ok_or_else(|| seam_err("static decide seam returned a malformed plan"))?;

        match plan {
            PlanOut::Reply(resp) => {
                client.write_all(&resp)?;
                client.flush()?;
                let head_end = resp
                    .windows(4)
                    .position(|w| w == b"\r\n\r\n")
                    .map(|p| p + 4)
                    .unwrap_or(resp.len());
                Ok(StaticOutcome {
                    head: resp[..head_end].to_vec(),
                    bytes: resp.len() as u64,
                    keepalive: keepalive_req,
                })
            }
            PlanOut::Whole(head) => {
                let mut f = file.ok_or_else(|| seam_err("whole-file plan without a file"))?;
                client.write_all(&head)?;
                let mut bytes = head.len() as u64;
                // Body = the whole file [0, len), where `len` is the metadata
                // length the 200 head's Content-Length was framed from. Zero-copy
                // (sendfile) when a socket fd is available, else the bounded
                // userspace pump — both place exactly `len` file bytes on the
                // wire, and a file shorter than `len` is an error (fail-safe: the
                // head is already sent, so the connection must drop).
                bytes += send_window(&mut f, client, zc_fd, 0, len)?;
                client.flush()?;
                Ok(StaticOutcome {
                    head,
                    bytes,
                    keepalive: keepalive_req,
                })
            }
            PlanOut::Window { off, n, head } => {
                let mut f = file.ok_or_else(|| seam_err("window plan without a file"))?;
                client.write_all(&head)?;
                let mut bytes = head.len() as u64;
                bytes += send_window(&mut f, client, zc_fd, off, n)?;
                client.flush()?;
                Ok(StaticOutcome {
                    head,
                    bytes,
                    keepalive: keepalive_req,
                })
            }
            PlanOut::Parts { head, tail, segs } => {
                let mut f = file.ok_or_else(|| seam_err("parts plan without a file"))?;
                client.write_all(&head)?;
                let mut bytes = head.len() as u64;
                for (pre, off, n) in &segs {
                    client.write_all(pre)?;
                    bytes += pre.len() as u64;
                    bytes += send_window(&mut f, client, zc_fd, *off, *n)?;
                }
                client.write_all(&tail)?;
                bytes += tail.len() as u64;
                client.flush()?;
                Ok(StaticOutcome {
                    head,
                    bytes,
                    keepalive: keepalive_req,
                })
            }
        }
    }

    /// Serve a static request into an in-memory buffer — the HTTPS front door's
    /// entry point. The whole TLS connection is terminated inside the proven Lean
    /// server, so there is no host socket to write through and no request the
    /// plaintext reactors could intercept; the decrypted request crosses back to
    /// the host here (`drorb_static_tls_serve`) and the SAME proven resolve +
    /// decide crossing renders the response bytes, which the caller then seals
    /// through the verified record layer.
    ///
    /// The zero-copy `sendfile(2)` the plaintext lane uses cannot survive TLS —
    /// the body must be encrypted through the record layer, so it is streamed into
    /// this buffer (`zc_fd = None`, the bounded userspace pump) rather than moved
    /// file→socket in the kernel. Every byte besides file content is the proven
    /// core's plan; the file bytes are the same bytes the plaintext lane serves.
    ///
    /// Returns `Ok(bytes)` with the full `head ++ body` response, or `Err` on a
    /// gone/malformed seam or a file that shrank below a planned window (the caller
    /// falls back to the proven serve's response).
    pub fn serve_tls_buf(
        &self,
        req: &[u8],
        keepalive_req: bool,
        resolve: impl FnOnce(&[u8]) -> Option<Vec<u8>>,
        decide: impl FnOnce(&[u8]) -> Option<Vec<u8>>,
    ) -> std::io::Result<Vec<u8>> {
        let mut buf: Vec<u8> = Vec::new();
        self.handle_streaming(req, keepalive_req, &mut buf, resolve, decide)?;
        Ok(buf)
    }

    /// Cross the same proven resolve + decide crossing as
    /// [`Self::handle_streaming_zc`], but return the serving plan LINEARIZED for an
    /// async reactor ([`StaticPlan`]) instead of writing it: the response head, the
    /// ordered literal/file-window segments, and the open file the windows read
    /// from. The wire bytes an executor produces by walking the plan are identical
    /// to what `handle_streaming_zc` writes (the plan encodes every byte besides
    /// file content); the executor merely chooses how the FILE windows reach the
    /// socket (e.g. `IORING_OP_SPLICE`). `Err` on a gone/malformed seam or a plan
    /// that references a file that could not be opened — the caller fails safe
    /// (drops the connection), never building response bytes itself.
    pub fn plan(
        &self,
        req: &[u8],
        keepalive_req: bool,
        resolve: impl FnOnce(&[u8]) -> Option<Vec<u8>>,
        decide: impl FnOnce(&[u8]) -> Option<Vec<u8>>,
    ) -> std::io::Result<StaticPlan> {
        let Some((method, target)) = request_line(req) else {
            return Err(seam_err(
                "static lane invoked on an unparseable request line",
            ));
        };

        // Filesystem boundary facts — the SAME resolution `handle_streaming_zc`
        // performs: only a GET/HEAD can use a resolved file; the METHOD decision is
        // the core's (any other method gets the core's 405 off the request bytes).
        let mut file = None;
        let mut len = 0u64;
        let mut mtime = 0u64;
        let mut name: Vec<u8> = Vec::new();
        let mut redir = false;
        if method == b"GET" || method == b"HEAD" {
            match self.resolve_entity(target, resolve) {
                Resolved::File(path) => {
                    if let Ok(f) = std::fs::File::open(&path) {
                        if let Ok(md) = f.metadata() {
                            len = md.len();
                            mtime = md
                                .modified()
                                .ok()
                                .and_then(|t| t.duration_since(std::time::UNIX_EPOCH).ok())
                                .map(|d| d.as_secs())
                                .unwrap_or(0);
                            name = path.file_name().map(os_bytes).unwrap_or(&[]).to_vec();
                            file = Some(f);
                        }
                    }
                }
                Resolved::Redirect => redir = true,
                Resolved::Missing => {}
            }
        }
        let found = file.is_some();

        // ONE crossing decides the whole response.
        let out = decide(&decide_frame(
            found,
            redir,
            keepalive_req,
            len,
            mtime,
            &name,
            req,
        ))
        .ok_or_else(|| seam_err("static decide seam returned no plan"))?;
        let plan = parse_plan(&out)
            .ok_or_else(|| seam_err("static decide seam returned a malformed plan"))?;

        let (segs, head, file) = match plan {
            PlanOut::Reply(resp) => {
                let head_end = resp
                    .windows(4)
                    .position(|w| w == b"\r\n\r\n")
                    .map(|p| p + 4)
                    .unwrap_or(resp.len());
                let head = resp[..head_end].to_vec();
                (vec![StaticSeg::Buf(resp)], head, None)
            }
            PlanOut::Whole(head) => {
                let f = file.ok_or_else(|| seam_err("whole-file plan without a file"))?;
                // Body = the whole file [0, len), where `len` is the metadata length
                // the 200 head's Content-Length was framed from — the same window the
                // synchronous path sends.
                let segs = vec![
                    StaticSeg::Buf(head.clone()),
                    StaticSeg::Window { off: 0, n: len },
                ];
                (segs, head, Some(f))
            }
            PlanOut::Window { off, n, head } => {
                let f = file.ok_or_else(|| seam_err("window plan without a file"))?;
                let segs = vec![StaticSeg::Buf(head.clone()), StaticSeg::Window { off, n }];
                (segs, head, Some(f))
            }
            PlanOut::Parts {
                head,
                tail,
                segs: parts,
            } => {
                let f = file.ok_or_else(|| seam_err("parts plan without a file"))?;
                let mut segs = Vec::with_capacity(parts.len() * 2 + 2);
                segs.push(StaticSeg::Buf(head.clone()));
                for (pre, off, n) in parts {
                    segs.push(StaticSeg::Buf(pre));
                    segs.push(StaticSeg::Window { off, n });
                }
                segs.push(StaticSeg::Buf(tail));
                (segs, head, Some(f))
            }
        };
        Ok(StaticPlan {
            segs,
            file,
            keepalive: keepalive_req,
            head,
        })
    }
}

/// Stream exactly the file window `[off, off+n)` to the client with a bounded
/// buffer. A file that can no longer supply the window (it shrank since the
/// metadata read) is an error — the plan's framing can't be honored, so the
/// caller drops the connection instead of sending a silently short body.
fn pump_window<W: Write>(
    f: &mut std::fs::File,
    client: &mut W,
    off: u64,
    n: u64,
) -> std::io::Result<u64> {
    f.seek(SeekFrom::Start(off))?;
    let mut remaining = n;
    let mut buf = vec![0u8; STREAM_CHUNK];
    while remaining > 0 {
        let want = remaining.min(STREAM_CHUNK as u64) as usize;
        let got = match f.read(&mut buf[..want]) {
            Ok(0) => {
                client.flush().ok();
                return Err(std::io::Error::new(
                    std::io::ErrorKind::UnexpectedEof,
                    "static file shorter than the planned window",
                ));
            }
            Ok(g) => g,
            Err(e) => {
                client.flush().ok();
                return Err(e);
            }
        };
        client.write_all(&buf[..got])?;
        remaining -= got as u64;
    }
    Ok(n)
}

/// Whether the static body send path may use `sendfile(2)` zero-copy. On by
/// default; set `DRORB_STATIC_NO_ZEROCOPY` to force the bounded userspace pump
/// (an escape hatch, and the A/B lever for measuring the zero-copy win — the
/// wire bytes are identical on both paths). Read once, then cached.
#[cfg(target_os = "linux")]
fn zerocopy_enabled() -> bool {
    static ZC: OnceLock<bool> = OnceLock::new();
    *ZC.get_or_init(|| std::env::var_os("DRORB_STATIC_NO_ZEROCOPY").is_none())
}

/// Place the file window `[off, off+n)` on the wire. When `zc_fd` is the client
/// socket's raw fd (a blocking Linux socket) the body moves file->socket in the
/// kernel via `sendfile(2)` — no userspace copy. Otherwise the bounded pump
/// ([`pump_window`]) carries it. Both write exactly the file bytes `[off, off+n)`;
/// a file that shrank below the window is an error on either path.
fn send_window<W: Write>(
    f: &mut std::fs::File,
    client: &mut W,
    zc_fd: Option<RawFd>,
    off: u64,
    n: u64,
) -> std::io::Result<u64> {
    #[cfg(target_os = "linux")]
    if let Some(sock) = zc_fd {
        if zerocopy_enabled() {
            // Flush any buffered head/preface bytes first: on the production path
            // `client` IS this socket, so the spliced window must follow them.
            client.flush()?;
            sendfile_window(sock, f.as_raw_fd(), off, n)?;
            return Ok(n);
        }
    }
    let _ = zc_fd;
    pump_window(f, client, off, n)
}

/// One file window moved to the socket with `sendfile(2)`, chunked under the
/// per-call ceiling and EINTR-retried. `sendfile` advances its own `offset`
/// argument, so the file's seek position is untouched (Parts issues several
/// windows in turn). A short count — the file shrank since the metadata read —
/// is reported as `UnexpectedEof`, matching the pump's fail-safe.
#[cfg(target_os = "linux")]
fn sendfile_window(sock: RawFd, file: RawFd, off: u64, n: u64) -> std::io::Result<()> {
    let mut offset = off as libc::off_t;
    let mut remaining = n;
    while remaining > 0 {
        let want = remaining.min(0x7fff_f000) as usize;
        let sent = unsafe { libc::sendfile(sock, file, &mut offset, want) };
        if sent < 0 {
            let e = std::io::Error::last_os_error();
            if e.kind() == std::io::ErrorKind::Interrupted {
                continue;
            }
            return Err(e);
        }
        if sent == 0 {
            return Err(std::io::Error::new(
                std::io::ErrorKind::UnexpectedEof,
                "static file shorter than the planned window (sendfile)",
            ));
        }
        remaining -= sent as u64;
    }
    Ok(())
}

/// The request line's `(method, target)`, borrowed from the request bytes.
fn request_line(req: &[u8]) -> Option<(&[u8], &[u8])> {
    let line_end = req.windows(2).position(|w| w == b"\r\n")?;
    let line = &req[..line_end];
    let mut it = line.splitn(3, |&c| c == b' ');
    let method = it.next()?;
    let target = it.next()?;
    Some((method, target))
}

/// The path portion of a request target (drop a `?query`/`#fragment`).
fn target_path(target: &[u8]) -> &[u8] {
    let end = target
        .iter()
        .position(|&b| b == b'?' || b == b'#')
        .unwrap_or(target.len());
    &target[..end]
}

/// The raw bytes of a file name for the decide-seam frame. The extension → MIME
/// decision on these bytes is the CORE's (`Route.StaticHead.extOf`/`ctypeFor`);
/// no host extension parsing happens.
fn os_bytes(name: &std::ffi::OsStr) -> &[u8] {
    use std::os::unix::ffi::OsStrExt;
    name.as_bytes()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tmp_root() -> PathBuf {
        let mut d = std::env::temp_dir();
        d.push(format!("drorb-static-test-{}", std::process::id()));
        let _ = std::fs::create_dir_all(&d);
        std::fs::canonicalize(&d).unwrap()
    }

    /// A distinct temp root (so a test writing `index.html` cannot collide with
    /// another running in the same process).
    fn tmp_root_named(tag: &str) -> PathBuf {
        let mut d = std::env::temp_dir();
        d.push(format!("drorb-static-{}-{}", tag, std::process::id()));
        let _ = std::fs::create_dir_all(&d);
        std::fs::canonicalize(&d).unwrap()
    }

    /// TEST-ONLY stand-in for the `drorb_static_resolve` crossing (unit tests
    /// cannot boot the proven runtime): the same split / decode-once / UTF-8
    /// gate / clamped dot-walk, '/'-joined. It exists to exercise THIS module's
    /// host plumbing (prefix strip, join, canonicalize re-check); the REAL seam
    /// is exercised end-to-end against the running binary (the differential
    /// harness) — do not read these tests as covering the core.
    fn mirror_resolve(rel: &[u8]) -> Option<Vec<u8>> {
        fn hex_val(b: u8) -> Option<u8> {
            match b {
                b'0'..=b'9' => Some(b - b'0'),
                b'a'..=b'f' => Some(b - b'a' + 10),
                b'A'..=b'F' => Some(b - b'A' + 10),
                _ => None,
            }
        }
        let mut segs: Vec<String> = Vec::new();
        for raw in rel.split(|&b| b == b'/') {
            if raw.is_empty() {
                continue;
            }
            let mut decoded = Vec::with_capacity(raw.len());
            let mut i = 0;
            while i < raw.len() {
                if raw[i] == b'%' && i + 2 < raw.len() {
                    if let (Some(h), Some(l)) = (hex_val(raw[i + 1]), hex_val(raw[i + 2])) {
                        decoded.push(h * 16 + l);
                        i += 3;
                        continue;
                    }
                }
                decoded.push(raw[i]);
                i += 1;
            }
            let s = String::from_utf8(decoded).ok()?;
            match s.as_str() {
                "." => {}
                ".." => {
                    segs.pop();
                }
                _ => segs.push(s),
            }
        }
        Some(segs.join("/").into_bytes())
    }

    // Plan encoders mirroring `Route.StaticDecide.encodePlan`'s FRAMING — these
    // build SYNTHETIC plans so the tests exercise the host EXECUTOR (frame
    // layout, window pump, byte accounting) without mirroring the core's
    // decision logic. The real decision is exercised against the running
    // binary by the differential harness.
    fn enc_reply(resp: &[u8]) -> Vec<u8> {
        let mut v = vec![1u8];
        v.extend_from_slice(resp);
        v
    }
    fn enc_whole(head: &[u8]) -> Vec<u8> {
        let mut v = vec![2u8];
        v.extend_from_slice(head);
        v
    }
    fn enc_window(off: u64, n: u64, head: &[u8]) -> Vec<u8> {
        let mut v = vec![3u8];
        v.extend_from_slice(&off.to_be_bytes());
        v.extend_from_slice(&n.to_be_bytes());
        v.extend_from_slice(head);
        v
    }
    fn enc_parts(head: &[u8], tail: &[u8], segs: &[(&[u8], u64, u64)]) -> Vec<u8> {
        let mut v = vec![4u8];
        v.extend_from_slice(&(head.len() as u32).to_be_bytes());
        v.extend_from_slice(head);
        v.extend_from_slice(&(tail.len() as u16).to_be_bytes());
        v.extend_from_slice(tail);
        v.extend_from_slice(&(segs.len() as u16).to_be_bytes());
        for (pre, off, n) in segs {
            v.extend_from_slice(&(pre.len() as u16).to_be_bytes());
            v.extend_from_slice(pre);
            v.extend_from_slice(&off.to_be_bytes());
            v.extend_from_slice(&n.to_be_bytes());
        }
        v
    }

    #[test]
    fn detects_static_path() {
        let root = tmp_root();
        let sr = StaticRoot {
            root,
            prefix: "/static/".into(),
            spa_index: None,
        };
        assert!(sr.is_static_path(b"GET /static/app.js HTTP/1.1\r\nHost: x\r\n\r\n"));
        assert!(sr.is_static_path(b"HEAD /static/a HTTP/1.1\r\n\r\n"));
        // Non-GET/HEAD methods are CLAIMED now: the 405 is the core's decision,
        // so a POST /static/… must reach the crossing rather than fall through.
        assert!(sr.is_static_path(b"POST /static/a HTTP/1.1\r\n\r\n"));
        assert!(sr.is_static_path(b"DELETE /static/a HTTP/1.1\r\n\r\n"));
        assert!(!sr.is_static_path(b"GET /api HTTP/1.1\r\n\r\n"));
        assert!(!sr.is_static_path(b"OPTIONS * HTTP/1.1\r\n\r\n"));
    }

    #[test]
    fn resolves_and_confines() {
        let root = tmp_root();
        let mut f = std::fs::File::create(root.join("hello.txt")).unwrap();
        f.write_all(b"hi there").unwrap();
        drop(f);
        let sr = StaticRoot {
            root: root.clone(),
            prefix: "/static/".into(),
            spa_index: None,
        };

        // A real file resolves.
        let p = sr
            .resolve_with(b"/static/hello.txt", mirror_resolve)
            .unwrap();
        assert_eq!(p, root.join("hello.txt"));

        // A traversal target cannot escape the root (resolves to nothing under root).
        assert!(
            sr.resolve_with(b"/static/../../etc/passwd", mirror_resolve)
                .is_none()
        );
        // A double-encoded `..` decodes ONCE to the literal `%2e%2e`, not to `..`,
        // so it names no file and is rejected.
        assert!(
            sr.resolve_with(b"/static/%252e%252e/etc/passwd", mirror_resolve)
                .is_none()
        );
        // A missing file is rejected.
        assert!(
            sr.resolve_with(b"/static/nope.txt", mirror_resolve)
                .is_none()
        );
        // A core reject (e.g. the UTF-8 gate) is a fail-safe None.
        assert!(sr.resolve_with(b"/static/hello.txt", |_| None).is_none());
    }

    #[test]
    fn resolves_directory_redirect_and_index() {
        let root = tmp_root();
        std::fs::write(root.join("index.html"), b"<i>root</i>").unwrap();
        std::fs::create_dir_all(root.join("dir")).unwrap();
        std::fs::write(root.join("dir/index.html"), b"<i>dir</i>").unwrap();
        let sr = StaticRoot {
            root: root.clone(),
            prefix: "/static/".into(),
            spa_index: None,
        };

        // A directory WITHOUT its trailing slash ⇒ a redirect boundary fact.
        assert!(matches!(
            sr.resolve_entity(b"/static/dir", mirror_resolve),
            Resolved::Redirect
        ));
        // WITH the trailing slash ⇒ its index.html served as a file.
        match sr.resolve_entity(b"/static/dir/", mirror_resolve) {
            Resolved::File(p) => assert_eq!(p, root.join("dir/index.html")),
            _ => panic!("expected dir/index.html"),
        }
        // The prefix root itself ⇒ the root index.html.
        match sr.resolve_entity(b"/static/", mirror_resolve) {
            Resolved::File(p) => assert_eq!(p, root.join("index.html")),
            _ => panic!("expected root index.html"),
        }
        // A regular file still resolves as a file.
        std::fs::write(root.join("plain.txt"), b"x").unwrap();
        assert!(matches!(
            sr.resolve_entity(b"/static/plain.txt", mirror_resolve),
            Resolved::File(_)
        ));
    }

    #[test]
    fn frame_carries_boundary_facts() {
        let root = tmp_root();
        std::fs::write(root.join("f.txt"), b"0123456789").unwrap();
        let sr = StaticRoot {
            root,
            prefix: "/static/".into(),
            spa_index: None,
        };
        let req: &[u8] = b"GET /static/f.txt HTTP/1.1\r\nHost: x\r\n\r\n";
        let mut seen: Vec<u8> = Vec::new();
        let mut out: Vec<u8> = Vec::new();
        let _ = sr.handle_streaming(req, true, &mut out, mirror_resolve, |frame| {
            seen = frame.to_vec();
            Some(enc_whole(b"HTTP/1.1 200 OK\r\nContent-Length: 10\r\n\r\n"))
        });
        // flags: keep-alive + found.
        assert_eq!(seen[0], 0b11);
        // len = 10 (big-endian).
        assert_eq!(&seen[1..9], &10u64.to_be_bytes());
        // name = "f.txt" after the 2-byte name length.
        let name_len = u16::from_be_bytes([seen[17], seen[18]]) as usize;
        assert_eq!(&seen[19..19 + name_len], b"f.txt");
        // the raw request bytes ride at the end.
        assert!(seen.ends_with(req));
    }

    #[test]
    fn executes_reply_plan_verbatim() {
        let root = tmp_root();
        let sr = StaticRoot {
            root,
            prefix: "/static/".into(),
            spa_index: None,
        };
        let resp: &[u8] =
            b"HTTP/1.1 404 Not Found\r\nConnection: keep-alive\r\nContent-Length: 9\r\n\r\nnot found";
        let mut out: Vec<u8> = Vec::new();
        let o = sr
            .handle_streaming(
                b"GET /static/nope.txt HTTP/1.1\r\nHost: x\r\n\r\n",
                true,
                &mut out,
                mirror_resolve,
                |_| Some(enc_reply(resp)),
            )
            .unwrap();
        assert_eq!(out, resp);
        assert!(o.head.ends_with(b"\r\n\r\n"));
        assert_eq!(o.bytes, resp.len() as u64);
    }

    #[test]
    fn executes_whole_plan_streaming() {
        let root = tmp_root();
        // A body several chunks long: the pump must reassemble it exactly.
        let body: Vec<u8> = (0..(STREAM_CHUNK * 3 + 123))
            .map(|i| (i % 251) as u8)
            .collect();
        std::fs::write(root.join("big.bin"), &body).unwrap();
        let sr = StaticRoot {
            root,
            prefix: "/static/".into(),
            spa_index: None,
        };
        let head: &[u8] = b"HTTP/1.1 200 OK\r\nContent-Length: 196731\r\n\r\n";
        let mut out: Vec<u8> = Vec::new();
        let o = sr
            .handle_streaming(
                b"GET /static/big.bin HTTP/1.1\r\nHost: x\r\n\r\n",
                true,
                &mut out,
                mirror_resolve,
                |_| Some(enc_whole(head)),
            )
            .unwrap();
        assert!(o.keepalive);
        let head_end = out.windows(4).position(|w| w == b"\r\n\r\n").unwrap() + 4;
        assert_eq!(&out[..head_end], head);
        assert_eq!(&out[head_end..], &body[..]);
    }

    #[test]
    fn executes_window_plan_exact_slice() {
        let root = tmp_root();
        let body: Vec<u8> = (0..(STREAM_CHUNK * 2 + 500))
            .map(|i| (i % 249) as u8)
            .collect();
        std::fs::write(root.join("w.bin"), &body).unwrap();
        let sr = StaticRoot {
            root,
            prefix: "/static/".into(),
            spa_index: None,
        };
        let head: &[u8] = b"HTTP/1.1 206 Partial Content\r\n\r\n";
        // A window crossing a chunk boundary.
        let (off, n) = (STREAM_CHUNK as u64 - 7, 1000u64);
        let mut out: Vec<u8> = Vec::new();
        let o = sr
            .handle_streaming(
                b"GET /static/w.bin HTTP/1.1\r\nHost: x\r\n\r\n",
                true,
                &mut out,
                mirror_resolve,
                |_| Some(enc_window(off, n, head)),
            )
            .unwrap();
        assert_eq!(&out[..head.len()], head);
        assert_eq!(&out[head.len()..], &body[off as usize..(off + n) as usize]);
        assert_eq!(o.bytes, head.len() as u64 + n);
    }

    #[test]
    fn executes_parts_plan_in_order() {
        let root = tmp_root();
        let body: Vec<u8> = (0..1000).map(|i| (i % 255) as u8).collect();
        std::fs::write(root.join("p.bin"), &body).unwrap();
        let sr = StaticRoot {
            root,
            prefix: "/static/".into(),
            spa_index: None,
        };
        let head: &[u8] = b"HTTP/1.1 206 Partial Content\r\n\r\n";
        let mut out: Vec<u8> = Vec::new();
        let o = sr
            .handle_streaming(
                b"GET /static/p.bin HTTP/1.1\r\nHost: x\r\n\r\n",
                true,
                &mut out,
                mirror_resolve,
                |_| {
                    Some(enc_parts(
                        head,
                        b"\r\n--end--\r\n",
                        &[(b"--b1\r\n\r\n", 0, 10), (b"\r\n--b2\r\n\r\n", 20, 10)],
                    ))
                },
            )
            .unwrap();
        let mut want = head.to_vec();
        want.extend_from_slice(b"--b1\r\n\r\n");
        want.extend_from_slice(&body[0..10]);
        want.extend_from_slice(b"\r\n--b2\r\n\r\n");
        want.extend_from_slice(&body[20..30]);
        want.extend_from_slice(b"\r\n--end--\r\n");
        assert_eq!(out, want);
        assert_eq!(o.bytes, want.len() as u64);
    }

    #[test]
    fn short_file_window_fails_safe() {
        let root = tmp_root();
        std::fs::write(root.join("s.bin"), b"short").unwrap();
        let sr = StaticRoot {
            root,
            prefix: "/static/".into(),
            spa_index: None,
        };
        let mut out: Vec<u8> = Vec::new();
        // A window past EOF: the executor must ERROR (drop the connection), never
        // emit a short body under a longer Content-Length.
        let r = sr.handle_streaming(
            b"GET /static/s.bin HTTP/1.1\r\nHost: x\r\n\r\n",
            true,
            &mut out,
            mirror_resolve,
            |_| Some(enc_window(0, 100, b"HTTP/1.1 206 Partial Content\r\n\r\n")),
        );
        assert!(r.is_err());
    }

    #[test]
    fn empty_seam_output_fails_safe() {
        let root = tmp_root();
        let sr = StaticRoot {
            root,
            prefix: "/static/".into(),
            spa_index: None,
        };
        let mut out: Vec<u8> = Vec::new();
        let r = sr.handle_streaming(
            b"GET /static/x HTTP/1.1\r\nHost: x\r\n\r\n",
            true,
            &mut out,
            mirror_resolve,
            |_| None,
        );
        assert!(r.is_err());
        assert!(out.is_empty()); // nothing host-built reached the wire
    }

    #[test]
    fn spa_fallback_serves_index_for_unknown_path() {
        let root = tmp_root_named("spa");
        std::fs::write(root.join("index.html"), b"<!doctype html>SPA").unwrap();
        std::fs::write(root.join("app.js"), b"console.log(1)").unwrap();
        let sr = StaticRoot {
            root: root.clone(),
            prefix: "/static/".into(),
            spa_index: Some("index.html".into()),
        };

        // (1) an existing asset resolves to the asset itself (the fallback never
        // masks a real file). Its Content-Type is then the asset's own extension
        // (the decide/head seam keys on the resolved file name, `app.js`).
        match sr.resolve_entity(b"/static/app.js", mirror_resolve) {
            Resolved::File(p) => assert_eq!(p, root.join("app.js")),
            _ => panic!("expected the app.js asset"),
        }

        // (2) an unknown client-route path (no such file) falls back to the SPA
        // index — a 200, so client-side routing resolves.
        match sr.resolve_entity(b"/static/dashboard/foo", mirror_resolve) {
            Resolved::File(p) => assert_eq!(p, root.join("index.html")),
            _ => panic!("expected the index.html SPA fallback"),
        }

        // (3) a traversal target never escapes: the core clamps it under the root,
        // so it names no file and falls back to the FIXED index — /etc/passwd is
        // never opened. The fallback served is index.html, not the escaping path.
        match sr.resolve_entity(b"/static/../../etc/passwd", mirror_resolve) {
            Resolved::File(p) => assert_eq!(p, root.join("index.html")),
            _ => panic!("expected the confined index fallback"),
        }

        // (4) with the SPA fallback disabled, an unknown path is Missing (the
        // core's 404) — the fallback is strictly opt-in.
        let sr_off = StaticRoot {
            root,
            prefix: "/static/".into(),
            spa_index: None,
        };
        assert!(matches!(
            sr_off.resolve_entity(b"/static/dashboard/foo", mirror_resolve),
            Resolved::Missing
        ));
    }
}
