/-
# Autoindex — directory index / autoindex listing (RFC 9110 §7.1, §15.3)

A sans-IO model of the directory-index stage a static file server owes when a
request target resolves to a *directory* rather than a regular file. It closes
three obligations, all reusing the traversal discipline the file handler already
proves (`Safety.Traversal.serveStatic`), never a fresh path routine:

  * **Index precedence.** A directory is first probed for a configured index
    document (`index.html`, `index.htm`, …). The FIRST configured index name
    that names an existing regular file is served *as that file*; the generated
    listing is produced only when none exists. This is the ordered "directory
    index" fallback of RFC 9110 §7.1 target resolution — a served index is a
    normal `200`, not a machine-generated page.

  * **Listing.** With no index present, the directory's entries are rendered as
    an HTML document: one link row per entry name, under a heading naming the
    request path. Every listed entry appears as its own row.

  * **No escape.** Every link the listing emits points at `reqTarget ++ [name]`
    — the current request path extended by a single entry component — and is
    resolved back through the SAME `serveStatic` discipline. So following any
    listed link keeps the document root as a path prefix, even for an adversarial
    entry name (a literal `..`) and even under a filesystem walker that actually
    pops on `..` (`Route.Path.descend`). The listing is incapable of minting an
    escaping href because it re-uses the proven-safe resolver.

The filesystem is the uninterpreted boundary: `existsFile` (is there a regular
file at a resolved path), `isDir`, and `readDir` (a directory's entry names, each
a single path component) enter as total fields of `DirConfig`. The theorems are
about the index-vs-listing *selection* and the *hrefs* it emits, not about any
real disk.

Theorems:
  * `autoindex_index_precedence` — a present index file is served instead of the
    listing (and the result is provably NOT a listing).
  * `resolveIndex_first`         — precedence picks the FIRST existing index name.
  * `autoindex_lists_dir`        — a directory with no index renders a listing in
    which every entry name appears as its own link row.
  * `autoindex_no_escape`        — every listed link resolves under the document
    root (prefix form, and under a popping walker), for real listed entries and
    for an adversarial `..` entry.
-/

import StaticFile
import Safety.Traversal

namespace Reactor.Stage.Autoindex

open StaticFile (Bytes strBytes find?_first)

/-! ## Configuration (the filesystem boundary) -/

/-- Directory-index configuration. Every filesystem-shaped field is an
uninterpreted total function — the boundary. -/
structure DirConfig where
  /-- The configured document root, as clean directory segments. -/
  docRoot : List String
  /-- Whether a resolved path names an existing *regular file*. -/
  existsFile : List String → Bool
  /-- Whether a resolved path names a directory. -/
  isDir : List String → Bool
  /-- A directory's entry names — each a single path component (no separators,
  supplied by the boundary `readdir`). -/
  readDir : List String → List String
  /-- Ordered index document names probed for a directory (e.g.
  `["index.html", "index.htm"]`). -/
  indexNames : List String

/-! ## Path resolution (reusing the traversal discipline) -/

/-- Resolve a request target under the document root with the file handler's
exact discipline: decode once, strip dot-segments, join under the root. No fresh
path routine — this is the same `serveStatic` the static handler is proven on. -/
def resolveDir (cfg : DirConfig) (reqTarget : List String) : List String :=
  Safety.Traversal.serveStatic cfg.docRoot reqTarget

/-- The client target a listed entry links to: the current request path extended
by the single entry component. A browser following the link re-requests exactly
this, which is resolved through `resolveDir` again. -/
def entryTarget (reqTarget : List String) (name : String) : List String :=
  reqTarget ++ [name]

/-! ## Index precedence -/

/-- Probe the configured index names in order; the first that names an existing
regular file in the directory wins. `none` = no index present (list the dir). -/
def resolveIndex (cfg : DirConfig) (dirPath : List String) : Option String :=
  cfg.indexNames.find? (fun n => cfg.existsFile (dirPath ++ [n]))

/-- **Precedence picks the FIRST existing index name.** Given index names
`pre ++ n :: post` where no earlier name exists as a file and `n` does, the
resolved index is exactly `n` — later candidates never mask an earlier hit. -/
theorem resolveIndex_first (cfg : DirConfig) (dirPath : List String)
    (pre : List String) (n : String) (post : List String)
    (hpre : ∀ m ∈ pre, cfg.existsFile (dirPath ++ [m]) = false)
    (hn : cfg.existsFile (dirPath ++ [n]) = true)
    (hidx : cfg.indexNames = pre ++ n :: post) :
    resolveIndex cfg dirPath = some n := by
  unfold resolveIndex
  rw [hidx]
  exact find?_first (fun m => cfg.existsFile (dirPath ++ [m])) pre n post hpre hn

/-! ## HTML rendering -/

/-- Minimal HTML entity escaping (RFC 9110 hygiene against markup injection in an
entry name): neutralize the five markup-significant characters. -/
def htmlEscape (s : String) : String :=
  (s.toList.map (fun c =>
    match c with
    | '&' => "&amp;"
    | '<' => "&lt;"
    | '>' => "&gt;"
    | '"' => "&quot;"
    | '\'' => "&#39;"
    | c => String.singleton c)).foldl (· ++ ·) ""

/-- The URL an entry links to: the request path extended by the entry name,
rendered as an absolute path. -/
def entryHref (reqTarget : List String) (name : String) : String :=
  "/" ++ String.intercalate "/" (entryTarget reqTarget name)

/-- One `<li>` link row for a directory entry. -/
def entryRow (reqTarget : List String) (name : String) : String :=
  "<li><a href=\"" ++ entryHref reqTarget name ++ "\">" ++ htmlEscape name ++ "</a></li>"

/-- The listing's link rows — exactly one per entry, in directory order. -/
def listingRows (reqTarget : List String) (entries : List String) : List String :=
  entries.map (entryRow reqTarget)

/-- Render the directory listing as an HTML document: a heading naming the
request path, then one link row per entry. -/
def renderIndexHtml (reqTarget : List String) (entries : List String) : Bytes :=
  let title := "/" ++ String.intercalate "/" reqTarget
  strBytes
    ("<!doctype html><html><head><title>Index of " ++ title ++
     "</title></head><body><h1>Index of " ++ title ++ "</h1><ul>" ++
     (listingRows reqTarget entries).foldl (· ++ ·) "" ++
     "</ul></body></html>")

/-! ## The directory-index response -/

/-- The response the directory-index stage selects. -/
inductive DirResp where
  /-- Index precedence: serve the regular file at this resolved path (`200`). -/
  | serveFile (path : List String)
  /-- Autoindex: an HTML listing of `entries` for `reqTarget`, with its body. -/
  | listing (reqTarget : List String) (entries : List String) (html : Bytes)
  /-- Neither a directory nor a servable index. -/
  | notFound
deriving Repr

/-- Whether a response is a generated listing (the mutation-detector for
precedence: a served index must NOT be a listing). -/
def DirResp.isListing : DirResp → Bool
  | .listing _ _ _ => true
  | _ => false

/-- **The directory-index stage.** Resolve the target under the root; if it is a
directory, serve the first present index file, else render a listing; a
non-directory is `notFound` (the regular-file handler owns files). -/
def serveDir (cfg : DirConfig) (reqTarget : List String) : DirResp :=
  let dirPath := resolveDir cfg reqTarget
  if cfg.isDir dirPath then
    match resolveIndex cfg dirPath with
    | some n => .serveFile (dirPath ++ [n])
    | none =>
      let entries := cfg.readDir dirPath
      .listing reqTarget entries (renderIndexHtml reqTarget entries)
  else .notFound

/-! ## Theorem 1 — index precedence -/

/-- **`autoindex_index_precedence`.** When the directory contains an index file
(the ordered probe resolves to `n`), the stage serves that file — the resolved
index path — and the result is provably NOT a generated listing. An index masks
the autoindex page (RFC 9110 §7.1 directory-index fallback). -/
theorem autoindex_index_precedence (cfg : DirConfig) (reqTarget : List String)
    (n : String)
    (hdir : cfg.isDir (resolveDir cfg reqTarget) = true)
    (hidx : resolveIndex cfg (resolveDir cfg reqTarget) = some n) :
    serveDir cfg reqTarget = .serveFile (resolveDir cfg reqTarget ++ [n]) ∧
    (serveDir cfg reqTarget).isListing = false := by
  have hserve : serveDir cfg reqTarget = .serveFile (resolveDir cfg reqTarget ++ [n]) := by
    unfold serveDir
    simp only [hdir, if_true, hidx]
  refine ⟨hserve, ?_⟩
  rw [hserve]; rfl

/-! ## Theorem 2 — listing -/

/-- Every entry name in the directory appears as its own link row in the
listing. Pure content lemma (`List.mem_map`). -/
theorem entry_in_listingRows (reqTarget : List String) (entries : List String)
    (name : String) (hmem : name ∈ entries) :
    entryRow reqTarget name ∈ listingRows reqTarget entries :=
  List.mem_map_of_mem hmem

/-- **`autoindex_lists_dir`.** A directory with no index file renders an HTML
listing of its entries: the stage returns `listing` carrying exactly the
directory's entries and the rendered document, and every entry name in the
directory shows up as its own link row in that listing. -/
theorem autoindex_lists_dir (cfg : DirConfig) (reqTarget : List String)
    (hdir : cfg.isDir (resolveDir cfg reqTarget) = true)
    (hnoidx : resolveIndex cfg (resolveDir cfg reqTarget) = none) :
    serveDir cfg reqTarget
      = .listing reqTarget (cfg.readDir (resolveDir cfg reqTarget))
          (renderIndexHtml reqTarget (cfg.readDir (resolveDir cfg reqTarget))) ∧
    (∀ name ∈ cfg.readDir (resolveDir cfg reqTarget),
      entryRow reqTarget name
        ∈ listingRows reqTarget (cfg.readDir (resolveDir cfg reqTarget))) := by
  have hserve : serveDir cfg reqTarget
      = .listing reqTarget (cfg.readDir (resolveDir cfg reqTarget))
          (renderIndexHtml reqTarget (cfg.readDir (resolveDir cfg reqTarget))) := by
    unfold serveDir
    simp only [hdir, if_true, hnoidx]
  refine ⟨hserve, ?_⟩
  intro name hmem
  exact entry_in_listingRows reqTarget _ name hmem

/-! ## Theorem 3 — no escape -/

/-- **`autoindex_no_escape` (prefix form).** Every link the listing emits points
at `entryTarget reqTarget name`, and resolving that through the file handler's
own discipline keeps the document root as a path prefix — no listed link, for
ANY entry name however adversarial, escapes the root. -/
theorem autoindex_no_escape (cfg : DirConfig) (reqTarget : List String)
    (name : String) :
    cfg.docRoot <+: resolveDir cfg (entryTarget reqTarget name) :=
  Safety.Traversal.serveStatic_root_prefix cfg.docRoot (entryTarget reqTarget name)

/-- **`autoindex_no_escape` under a popping walker.** Even interpreting the
resolved link path with `descend` — which actually pops a component on `..` — a
clean document root stays a prefix. The stage cannot mint an href that climbs out
of the root, because the listed entry is re-resolved by the same dot-segment
stripper before any pop can fire. -/
theorem autoindex_no_escape_descend (cfg : DirConfig) (reqTarget : List String)
    (name : String)
    (hclean : ∀ s ∈ cfg.docRoot, ¬ Route.Path.IsDot s) :
    cfg.docRoot <+: Route.Path.descend [] (resolveDir cfg (entryTarget reqTarget name)) :=
  Safety.Traversal.serveStatic_no_escape cfg.docRoot (entryTarget reqTarget name) hclean

/-! ## Concrete adversarial witness (non-vacuity of no-escape) -/

/-- An adversarial listing entry literally named `..` under `/srv/www`, listed
from `pub`, still resolves under the root: the link target `["pub",".."]` clamps
to `["srv","www"]` — it climbs back to the root but never above it. This is the
listing analogue of `serveStatic_dotdot_confined`. -/
theorem autoindex_dotdot_entry_confined :
    resolveDir ⟨["srv", "www"], fun _ => false, fun _ => true, fun _ => [], []⟩
        (entryTarget ["pub"] "..")
      = ["srv", "www"] := by decide

/-- A listing whose entry name would traverse (`..`) resolves strictly under the
root when the current path has depth: from `a/b`, an entry `..` links to
`["a","b",".."]` which clamps to `["srv","www","a"]` — one level up, still under
root. -/
theorem autoindex_dotdot_entry_confined_deep :
    resolveDir ⟨["srv", "www"], fun _ => false, fun _ => true, fun _ => [], []⟩
        (entryTarget ["a", "b"] "..")
      = ["srv", "www", "a"] := by decide

/-! ## HTML-escaping hygiene (bonus) -/

/-- `htmlEscape` neutralizes a raw `<` (markup-injection guard for entry names). -/
theorem htmlEscape_neutralizes_lt :
    htmlEscape "<script>" = "&lt;script&gt;" := by decide

/-! ## Concrete listing witness (the renderer actually runs) -/

/-- A concrete two-entry directory produces exactly two link rows, one per entry,
each an `<li><a …>` naming the entry — the renderer computes real HTML. -/
theorem listingRows_example :
    listingRows ["docs"] ["a.txt", "sub"] =
      ["<li><a href=\"/docs/a.txt\">a.txt</a></li>",
       "<li><a href=\"/docs/sub\">sub</a></li>"] := by decide

end Reactor.Stage.Autoindex
