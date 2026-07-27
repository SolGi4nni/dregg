import StaticFile
import Reactor.Stage.Compress

/-!
# Reactor.Stage.Variants — pre-compressed variant (sidecar) serving

Static-file serving of *pre-compressed* representations. When the document root
holds a `foo.txt.br` (Brotli) or `foo.txt.gz` (gzip) **sidecar** next to
`foo.txt`, a request that advertises the matching `Accept-Encoding` is served the
already-compressed sidecar bytes verbatim — no per-request compression — with the
transport `Content-Encoding` stamped and `Vary: Accept-Encoding` set so caches key
the two representations apart (RFC 9110 §8.4.1 `Content-Encoding`, §12.5.5 `Vary`,
§3.2 selecting representations).

This is the *precompress* half of static serving. It reuses:

* `StaticFile.Config` — the filesystem boundary (`fs : path → Option bytes`,
  `docRoot`) that decides whether a sidecar exists;
* `Reactor.Stage.Compress` — the `Accept-Encoding` scan (`isInfix` / the `br`,
  `gzip` tokens), the `Encoding` codec tags and their `Content-Encoding` names;
* `Route.Path` — the traversal discipline (`normalize`, `descend`) that keeps
  every resolved path — sidecar included — under the document root.

## The selection (server-preference, existence-gated)

`selectEnc` runs the two-factor decision the reference implements: a coding is
chosen only when the client advertises it **and** the sidecar file actually
exists. Server preference is `br > gzip`; failing both, `identity` (serve the
original file, no `Content-Encoding`). Advertising `br` alone does NOT serve a
`.br` that is not on disk — the naive "trust `Accept-Encoding`" mutant is ruled
out (`variant_absent_falls_back`).

## What is proven

* `variant_selects` — the full decision table: `br` chosen iff advertised and the
  `.br` sidecar exists; else `gzip` iff advertised and `.gz` exists; else
  `identity` on the base file.
* `variant_vary` — the emitted response carries `Vary: Accept-Encoding` always,
  and `Content-Encoding: <token>` exactly on a non-identity choice (and never on
  `identity`).
* `variant_no_escape` — the sidecar path (`.br`/`.gz` appended to the resolved
  file name) still keeps the document root as a prefix, even under a `..`-popping
  filesystem walker: a sidecar cannot climb out of the root.
-/

namespace Reactor.Stage.Variants

open Reactor.Stage.Compress (Encoding isInfix lower brTok gzipTok encName ceName)
open StaticFile (Config)

/-- Byte strings, as everywhere on the wire. -/
abbrev Bytes := List UInt8

/-! ## Header names/values (RFC 9110 §12.5.5, §8.4.1) -/

/-- `Vary` header name. -/
def varyName : Bytes := [86, 97, 114, 121]

/-- The `Vary` value this handler emits: `Accept-Encoding` — the request header
the selected representation depends on. -/
def aeVary : Bytes :=
  [65, 99, 99, 101, 112, 116, 45, 69, 110, 99, 111, 100, 105, 110, 103]

/-! ## Does the client advertise a coding?

Reuses the `Reactor.Stage.Compress` token scan: a coding is *advertised* when its
token occurs (case-insensitively) in the raw `Accept-Encoding` value. This is the
same membership test the dynamic compress stage negotiates over, so the two halves
of static serving agree on what "the client accepts br" means. -/

/-- The client advertises Brotli. -/
def acceptsBr (ae : Bytes) : Bool := isInfix brTok (lower ae)

/-- The client advertises gzip. -/
def acceptsGz (ae : Bytes) : Bool := isInfix gzipTok (lower ae)

/-! ## The request

A variant request is a static request target plus the raw `Accept-Encoding`
value. (The base static handler dispatches on the target alone; the variant
handler additionally consults `Accept-Encoding`.) -/

/-- A pre-compressed-variant request. -/
structure VReq where
  /-- Raw request-target segments (percent-encoded, possibly adversarial). -/
  target : List String
  /-- Raw `Accept-Encoding` value (`[]` when the header is absent). -/
  acceptEncoding : Bytes := []

/-! ## Sidecar path construction -/

/-- Append `suffix` to the LAST segment of a path — the sidecar of `…/foo.txt`
with suffix `.br` is `…/foo.txt.br` (same directory, extended file name). On the
empty path (the document root itself, a directory — never a sidecar target) it is
the identity. -/
def appendSuffixLast (suffix : String) : List String → List String
  | []      => []
  | [x]     => [x ++ suffix]
  | x :: xs => x :: appendSuffixLast suffix xs

/-- The resolved *relative* tail under the document root: the target
percent-decoded and dot-segment-normalized (RFC 3986 §5.2.4). No `..` survives. -/
def relTail (req : VReq) : List String := Route.Path.normalize req.target

/-- The resolved base file path: the document root followed by the normalized
tail. Definitionally `StaticFile`'s resolution (`base_eq_resolvePath`). -/
def basePath (cfg : Config) (req : VReq) : List String :=
  cfg.docRoot ++ relTail req

/-- The sidecar path for a coding: the base path with the coding's file suffix on
its last segment. `.br` for Brotli, `.gz` for gzip; `identity` has no sidecar and
resolves to the base file. -/
def sidecarPath (cfg : Config) (req : VReq) : Encoding → List String
  | .brotli   => cfg.docRoot ++ appendSuffixLast ".br" (relTail req)
  | .gzip     => cfg.docRoot ++ appendSuffixLast ".gz" (relTail req)
  | .deflate  => basePath cfg req
  | .identity => basePath cfg req

/-! ## The selection -/

/-- **The variant selection.** Choose Brotli iff the client advertises `br` and
the `.br` sidecar exists on disk; else gzip iff `gzip` advertised and the `.gz`
sidecar exists; else `identity` (the base file). Existence-gated and in server
preference order — advertising a coding whose sidecar is absent does not select
it. -/
def selectEnc (cfg : Config) (req : VReq) : Encoding :=
  if acceptsBr req.acceptEncoding && (cfg.fs (sidecarPath cfg req .brotli)).isSome then
    .brotli
  else if acceptsGz req.acceptEncoding && (cfg.fs (sidecarPath cfg req .gzip)).isSome then
    .gzip
  else
    .identity

/-- The file actually read for this request: the selected coding's sidecar (or
the base file for `identity`). -/
def servedPath (cfg : Config) (req : VReq) : List String :=
  sidecarPath cfg req (selectEnc cfg req)

/-! ## The response -/

/-- The response the variant handler emits. -/
structure VResp where
  status : Nat
  body : Bytes
  headers : List (Bytes × Bytes)
deriving Repr, DecidableEq

/-- **Serve a pre-compressed variant.** Select the coding, read the served file;
on a hit stamp `Vary: Accept-Encoding` (always — the representation genuinely
depends on `Accept-Encoding`) and, for a non-identity coding, the transport
`Content-Encoding: <token>`. A miss is `404`, still `Vary`-tagged. The sidecar
bytes are served verbatim: no per-request compression. -/
def serveVariant (cfg : Config) (req : VReq) : VResp :=
  match cfg.fs (servedPath cfg req) with
  | none      => { status := 404, body := [], headers := [(varyName, aeVary)] }
  | some body =>
    match selectEnc cfg req with
    | .identity => { status := 200, body := body, headers := [(varyName, aeVary)] }
    | e         => { status := 200, body := body,
                     headers := [(ceName, encName e), (varyName, aeVary)] }

/-! ## `variant_selects` — the decision table -/

/-- From `¬(a = true ∧ b = true)` conclude `(a && b) = false`. -/
theorem andFalse_of_not_and {a b : Bool} (h : ¬ (a = true ∧ b = true)) :
    (a && b) = false := by
  cases a <;> cases b <;> simp_all

/-- **The variant selection is the existence-gated, server-preference decision.**

* Brotli is chosen exactly when the client advertises `br` and the `.br` sidecar
  exists — and then the file served is that sidecar;
* failing that, gzip exactly when `gzip` is advertised and the `.gz` sidecar
  exists;
* failing both, `identity` — the base file, uncompressed.

Every branch is a real implication over an arbitrary filesystem boundary. -/
theorem variant_selects (cfg : Config) (req : VReq) :
    -- br: advertised ∧ sidecar present ⇒ serve the `.br` sidecar
    (acceptsBr req.acceptEncoding = true
        → (cfg.fs (sidecarPath cfg req .brotli)).isSome = true
        → selectEnc cfg req = .brotli
          ∧ servedPath cfg req = sidecarPath cfg req .brotli)
    -- gzip: no br ∧ gzip advertised ∧ `.gz` present ⇒ serve the `.gz` sidecar
    ∧ (¬ (acceptsBr req.acceptEncoding = true
              ∧ (cfg.fs (sidecarPath cfg req .brotli)).isSome = true)
        → acceptsGz req.acceptEncoding = true
        → (cfg.fs (sidecarPath cfg req .gzip)).isSome = true
        → selectEnc cfg req = .gzip
          ∧ servedPath cfg req = sidecarPath cfg req .gzip)
    -- identity: neither coding available ⇒ serve the base file
    ∧ (¬ (acceptsBr req.acceptEncoding = true
              ∧ (cfg.fs (sidecarPath cfg req .brotli)).isSome = true)
        → ¬ (acceptsGz req.acceptEncoding = true
              ∧ (cfg.fs (sidecarPath cfg req .gzip)).isSome = true)
        → selectEnc cfg req = .identity
          ∧ servedPath cfg req = basePath cfg req) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hbr hex
    have hsel : selectEnc cfg req = .brotli := by
      unfold selectEnc; rw [hbr, hex]; rfl
    exact ⟨hsel, by unfold servedPath; rw [hsel]⟩
  · intro hnbr hgz hex
    have h1 : (acceptsBr req.acceptEncoding && (cfg.fs (sidecarPath cfg req .brotli)).isSome)
        = false := andFalse_of_not_and hnbr
    have hsel : selectEnc cfg req = .gzip := by
      unfold selectEnc; rw [h1]; simp only [Bool.false_eq_true, if_false]
      rw [hgz, hex]; rfl
    exact ⟨hsel, by unfold servedPath; rw [hsel]⟩
  · intro hnbr hngz
    have h1 : (acceptsBr req.acceptEncoding && (cfg.fs (sidecarPath cfg req .brotli)).isSome)
        = false := andFalse_of_not_and hnbr
    have h2 : (acceptsGz req.acceptEncoding && (cfg.fs (sidecarPath cfg req .gzip)).isSome)
        = false := andFalse_of_not_and hngz
    have hsel : selectEnc cfg req = .identity := by
      unfold selectEnc; rw [h1, h2]; simp
    exact ⟨hsel, by unfold servedPath; rw [hsel]; rfl⟩

/-- **Mutant guard (the naive `Accept-Encoding`-only implementation is wrong).**
A client that advertises `br` but whose `.br` sidecar is absent (and no `.gz`) is
NOT served Brotli — it falls back to `identity`. The `Accept-Encoding` header
alone never conjures a sidecar. -/
theorem variant_absent_falls_back (cfg : Config) (req : VReq)
    (hbr : acceptsBr req.acceptEncoding = true)
    (hno_br : (cfg.fs (sidecarPath cfg req .brotli)).isSome = false)
    (hno_gz : ¬ (acceptsGz req.acceptEncoding = true
              ∧ (cfg.fs (sidecarPath cfg req .gzip)).isSome = true)) :
    selectEnc cfg req = .identity := by
  have h1 : (acceptsBr req.acceptEncoding && (cfg.fs (sidecarPath cfg req .brotli)).isSome)
      = false := by rw [hno_br, Bool.and_false]
  have h2 : (acceptsGz req.acceptEncoding && (cfg.fs (sidecarPath cfg req .gzip)).isSome)
      = false := andFalse_of_not_and hno_gz
  unfold selectEnc; rw [h1, h2]; simp

/-! ## `variant_vary` — Vary + Content-Encoding on the wire -/

/-- **The `Vary: Accept-Encoding` header is always emitted**, on hit and miss
alike — the URL's representation genuinely depends on `Accept-Encoding`, so caches
must key on it (RFC 9110 §12.5.5). -/
theorem variant_vary_always (cfg : Config) (req : VReq) :
    (varyName, aeVary) ∈ (serveVariant cfg req).headers := by
  unfold serveVariant
  cases cfg.fs (servedPath cfg req) with
  | none => simp
  | some body =>
    cases selectEnc cfg req with
    | identity => simp
    | brotli => simp
    | gzip => simp
    | deflate => simp

/-- **`Content-Encoding` is stamped exactly on a compressed choice.** On a hit
with a non-identity coding, the emitted headers carry `Content-Encoding: <token>`
(the codec's `encName`) alongside `Vary`. -/
theorem variant_ce_header (cfg : Config) (req : VReq) (body : Bytes)
    (hhit : cfg.fs (servedPath cfg req) = some body)
    (hne : selectEnc cfg req ≠ .identity) :
    (ceName, encName (selectEnc cfg req)) ∈ (serveVariant cfg req).headers
    ∧ (varyName, aeVary) ∈ (serveVariant cfg req).headers := by
  unfold serveVariant
  rw [hhit]
  cases hsel : selectEnc cfg req with
  | identity => exact absurd hsel hne
  | brotli => simp
  | gzip => simp
  | deflate => simp

/-- **No `Content-Encoding` on the identity choice.** When no sidecar is served,
the response carries no `Content-Encoding` header at all — the original bytes are
served as-is. -/
theorem variant_identity_no_ce (cfg : Config) (req : VReq)
    (hid : selectEnc cfg req = .identity) :
    ∀ v, (ceName, v) ∉ (serveVariant cfg req).headers := by
  intro v hv
  unfold serveVariant at hv
  cases hf : cfg.fs (servedPath cfg req) with
  | none =>
    rw [hf] at hv
    simp only [List.mem_singleton, Prod.mk.injEq] at hv
    exact absurd hv.1 (by decide)
  | some body =>
    rw [hf, hid] at hv
    simp only [List.mem_singleton, Prod.mk.injEq] at hv
    exact absurd hv.1 (by decide)

/-- **`variant_vary` (headline).** The emitted response always sets
`Vary: Accept-Encoding`, and carries `Content-Encoding: <token>` for the selected
coding exactly when that coding is non-identity (and none otherwise). -/
theorem variant_vary (cfg : Config) (req : VReq) (body : Bytes)
    (hhit : cfg.fs (servedPath cfg req) = some body) :
    (varyName, aeVary) ∈ (serveVariant cfg req).headers
    ∧ (selectEnc cfg req ≠ .identity
        → (ceName, encName (selectEnc cfg req)) ∈ (serveVariant cfg req).headers)
    ∧ (selectEnc cfg req = .identity
        → ∀ v, (ceName, v) ∉ (serveVariant cfg req).headers) :=
  ⟨variant_vary_always cfg req,
   fun hne => (variant_ce_header cfg req body hhit hne).1,
   variant_identity_no_ce cfg req⟩

/-! ## `variant_no_escape` — the sidecar stays under the root -/

/-- A path suffix of length ≥ 3 appended to any segment cannot equal a dot-segment
(`"."` len 1, `".."` len 2). -/
theorem append_long_not_dot (x suffix : String) (h3 : 3 ≤ suffix.length) :
    ¬ Route.Path.IsDot (x ++ suffix) := by
  intro h
  have hlen : (x ++ suffix).length = x.length + suffix.length := String.length_append x suffix
  rcases h with h | h
  · rw [h] at hlen
    have hd : ".".length = 1 := rfl
    rw [hd] at hlen; omega
  · rw [h] at hlen
    have hd : "..".length = 2 := rfl
    rw [hd] at hlen; omega

/-- Appending a `≥3`-long suffix to the last segment of a dot-free list keeps
every segment dot-free. -/
theorem appendSuffixLast_noDot {suffix : String} (h3 : 3 ≤ suffix.length) :
    ∀ {segs : List String}, (∀ s ∈ segs, ¬ Route.Path.IsDot s)
      → ∀ s ∈ appendSuffixLast suffix segs, ¬ Route.Path.IsDot s := by
  intro segs
  induction segs with
  | nil => intro _ s hs; cases hs
  | cons a rest ih =>
    intro hseg s hs
    cases rest with
    | nil =>
      -- appendSuffixLast suffix [a] = [a ++ suffix]
      simp only [appendSuffixLast, List.mem_singleton] at hs
      subst hs
      exact append_long_not_dot a suffix h3
    | cons b bs =>
      -- appendSuffixLast suffix (a :: b :: bs) = a :: appendSuffixLast suffix (b :: bs)
      have hstep : appendSuffixLast suffix (a :: b :: bs)
          = a :: appendSuffixLast suffix (b :: bs) := rfl
      rw [hstep] at hs
      rcases List.mem_cons.mp hs with hs | hs
      · rw [hs]; exact hseg a (by simp)
      · exact ih (fun x hx => hseg x (List.mem_cons_of_mem _ hx)) s hs

/-- The sidecar path is the document root followed by the (dot-free) normalized
tail with the coding suffix on its last segment. -/
theorem sidecar_shape (cfg : Config) (req : VReq) (enc : Encoding) :
    sidecarPath cfg req enc
      = cfg.docRoot ++ (match enc with
          | .brotli => appendSuffixLast ".br" (relTail req)
          | .gzip   => appendSuffixLast ".gz" (relTail req)
          | _       => relTail req) := by
  cases enc <;> rfl

/-- **`variant_no_escape` (headline).** For any request target — however many
encoded or literal `..` — and any selected coding, interpreting the served
sidecar/base path with the real `..`-popping filesystem walker (`descend`) still
keeps a clean document root as a prefix. A pre-compressed sidecar cannot be used
to climb out of the document root: the attacker's `..` was normalized away before
the suffix was appended, and the appended `.br`/`.gz` suffix is never a `..`. -/
theorem variant_no_escape (cfg : Config) (req : VReq)
    (hclean : ∀ s ∈ cfg.docRoot, ¬ Route.Path.IsDot s) :
    cfg.docRoot <+: Route.Path.descend [] (servedPath cfg req) := by
  -- The served path is docRoot ++ tail, where tail is dot-free.
  have htail : ∀ s ∈ (match selectEnc cfg req with
          | .brotli => appendSuffixLast ".br" (relTail req)
          | .gzip   => appendSuffixLast ".gz" (relTail req)
          | _       => relTail req), ¬ Route.Path.IsDot s := by
    have hrel : ∀ s ∈ relTail req, ¬ Route.Path.IsDot s :=
      Route.Path.normalize_noDot req.target
    cases selectEnc cfg req with
    | brotli   => exact appendSuffixLast_noDot (by decide) hrel
    | gzip     => exact appendSuffixLast_noDot (by decide) hrel
    | deflate  => exact hrel
    | identity => exact hrel
  have hno : ∀ s ∈ servedPath cfg req, ¬ Route.Path.IsDot s := by
    intro s hs
    unfold servedPath at hs
    rw [sidecar_shape cfg req (selectEnc cfg req)] at hs
    rcases List.mem_append.mp hs with hs | hs
    · exact hclean s hs
    · exact htail s hs
  rw [Route.Path.descend_noDot hno, List.nil_append]
  -- docRoot is a prefix of docRoot ++ tail.
  unfold servedPath
  rw [sidecar_shape cfg req (selectEnc cfg req)]
  exact List.prefix_append _ _

/-! ## The served base path is exactly `StaticFile`'s resolution

The `identity`/`deflate` branch serves `basePath`, which is definitionally the
document root followed by the normalized target — i.e. `StaticFile.resolvePath`.
So variant serving composes with the base static handler on the same resolved
file, not a divergent one. -/

/-- `basePath` is `StaticFile.resolvePath` on the same target. -/
theorem base_eq_resolvePath (cfg : Config) (req : VReq) :
    basePath cfg req = StaticFile.resolvePath cfg { target := req.target } := by
  unfold basePath relTail StaticFile.resolvePath
  rw [Safety.Traversal.serveStatic_eq_normalize]

/-! ## Concrete non-vacuity — a real embedded filesystem -/

/-- A document root `/site`. -/
def demoRoot : List String := ["site"]

/-- The `.br` sidecar bytes for `/site/page.html` (`"BR"` marker + a payload). -/
def brBytes : Bytes := [66, 82, 1, 2, 3]

/-- The plain bytes for `/site/page.html`. -/
def plainBytes : Bytes := [60, 104, 116, 109, 108, 62]  -- "<html>"

/-- An embedded filesystem: `/site/page.html` and its `.br` sidecar exist; no
`.gz` sidecar. -/
def demoFs : List String → Option Bytes
  | ["site", "page.html"]    => some plainBytes
  | ["site", "page.html.br"] => some brBytes
  | _                        => none

/-- The demo config over the embedded filesystem. -/
def demoCfg : Config where
  docRoot := demoRoot
  fs := demoFs
  isDir := fun _ => false
  readDir := fun _ => []
  etag := fun _ => { weak := false, tag := "" }
  lastModified := fun _ => 0

/-- A request for `/page.html` advertising `Accept-Encoding: br`. -/
def brReq : VReq := { target := ["page.html"], acceptEncoding := brTok }

/-- A request for `/page.html` advertising `Accept-Encoding: gzip` (no `.gz`
sidecar on disk). -/
def gzReq : VReq := { target := ["page.html"], acceptEncoding := gzipTok }

/-- **The `br` request selects the `.br` sidecar and serves its bytes.** -/
theorem demo_br_selects :
    selectEnc demoCfg brReq = .brotli
    ∧ servedPath demoCfg brReq = ["site", "page.html.br"]
    ∧ demoCfg.fs (servedPath demoCfg brReq) = some brBytes := by
  refine ⟨by decide, by decide, by decide⟩

/-- **The `br` response is the sidecar bytes, `Content-Encoding: br`,
`Vary: Accept-Encoding`.** The genuine wire effect. -/
theorem demo_br_response :
    serveVariant demoCfg brReq
      = { status := 200, body := brBytes,
          headers := [(ceName, brTok), (varyName, aeVary)] } := by
  decide

/-- **The `gzip` request has no `.gz` sidecar → identity.** It serves the plain
file with NO `Content-Encoding`, still `Vary`-tagged. This is the
existence-gating that the `Accept-Encoding`-only mutant would get wrong. -/
theorem demo_gz_falls_back :
    selectEnc demoCfg gzReq = .identity
    ∧ serveVariant demoCfg gzReq
        = { status := 200, body := plainBytes, headers := [(varyName, aeVary)] } := by
  refine ⟨by decide, by decide⟩

end Reactor.Stage.Variants
