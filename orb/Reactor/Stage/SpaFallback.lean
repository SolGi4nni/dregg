/-
# Reactor.Stage.SpaFallback — single-page-application fallback (PARITY-LEDGER h1.sfb / rt.7)

A sans-IO model of the SPA (single-page-application) serving discipline layered on
top of the static-file handler (`StaticFile`, `Safety.Traversal`). A single-page
app ships one `index.html` plus a client router; the server must therefore answer
a request for a *navigable route* that is not itself a file (e.g. `/dashboard`,
`/users/42`) by serving the application `index` with `200 OK`, so the client
router can take over — rather than the `404` a plain static handler would return.

The two invariants that make this safe and correct:

  * **Fallback, not 404** — an unmatched target that resolves to no regular file
    is served the SPA index with status `200`, where a plain static serve would
    have produced `404`. This is the whole point of the row.
  * **No escape** — the served path (the real file OR the fallback index) always
    keeps the configured document root as a prefix, even under a filesystem
    interpreter that actually pops a component on `..` (`Route.Path.descend`). The
    fallback cannot be steered outside the root: the target is resolved through
    the escape-safe `Safety.Traversal.serveStatic` before the fallback decision,
    and the index is a configured clean path under the root.
  * **Real files win** — an existing file is served directly and identically to a
    plain static serve; the fallback never masks or rewrites a real asset.

The filesystem is the boundary: `isFile : List String → Bool` (does a regular
file exist at a resolved path) is an uninterpreted total field of `Config`, so the
theorems hold uniformly over every real disk. The theorems are about the
response-selection state, not about any concrete filesystem.

Theorems:
  * `spa_fallback_serves_index` — a non-existent, non-file target under the SPA
    root is served the index with status `200`, while a plain serve `404`s.
  * `spa_fallback_no_escape`    — the served path never escapes the document root
    under a `..`-popping walker, in either branch.
  * `spa_real_file_served`      — an existing file is served directly (status
    `200`), identically to a plain static serve.

Selftest is drorb-native (the model, no real disk / no real socket) — the
filesystem `isFile` boundary is uninterpreted; wiring the fallback onto the live
`StaticFile.serveDeployed` embedded FS is the named residual.
-/

import Safety.Traversal

namespace Reactor.Stage.SpaFallback

open Route.Path (IsDot descend)

/-! ## The response -/

/-- The response the SPA handler selects. `ok path` is a `200 OK` serving the file
at a resolved `path`; `notFound` is the `404` a plain static serve would emit. -/
inductive Resp where
  | ok (path : List String)
  | notFound
deriving Repr, DecidableEq

/-- The numeric status line. -/
def Resp.status : Resp → Nat
  | .ok _ => 200
  | .notFound => 404

/-! ## Configuration (the filesystem boundary) -/

/-- SPA static configuration. `docRoot` is the configured document root (clean
directory segments); `isFile` is the uninterpreted filesystem boundary (a regular
file exists at a resolved path); `indexRel` is the SPA index path *relative to the
root* (e.g. `["index.html"]`). -/
structure Config where
  /-- The configured document root, as clean directory segments. -/
  docRoot : List String
  /-- Whether a regular file exists at a resolved path (the filesystem boundary). -/
  isFile : List String → Bool
  /-- The SPA index, relative to the document root (e.g. `["index.html"]`). -/
  indexRel : List String

/-- The absolute served path of the SPA index: the document root joined with the
configured relative index. -/
def Config.indexPath (cfg : Config) : List String := cfg.docRoot ++ cfg.indexRel

/-! ## Response selection -/

/-- **Path resolution**: decode the raw request target once and clamp it under the
document root through the escape-safe traversal discipline (`Safety.Traversal`).
Whatever the target, the result keeps `docRoot` as a prefix. -/
def resolveTarget (cfg : Config) (rawReq : List String) : List String :=
  Safety.Traversal.serveStatic cfg.docRoot rawReq

/-- The absolute path the SPA handler serves: the resolved target if it is a
regular file, otherwise the SPA index (the fallback). -/
def spaServedPath (cfg : Config) (rawReq : List String) : List String :=
  let p := resolveTarget cfg rawReq
  if cfg.isFile p then p else cfg.indexPath

/-- A plain static serve (no SPA fallback): a resolved regular file is `200 OK`,
anything else is a `404`. This is the baseline the fallback improves on. -/
def plainServe (cfg : Config) (rawReq : List String) : Resp :=
  let p := resolveTarget cfg rawReq
  if cfg.isFile p then .ok p else .notFound

/-- **The SPA serve.** A resolved regular file is served directly (`200`);
otherwise the fallback serves the SPA index (`200`), never `404`. -/
def spaServe (cfg : Config) (rawReq : List String) : Resp :=
  let p := resolveTarget cfg rawReq
  if cfg.isFile p then .ok p else .ok cfg.indexPath

/-- The SPA serve is exactly `ok` of the served path — the response/path bridge. -/
theorem spaServe_eq_servedPath (cfg : Config) (rawReq : List String) :
    spaServe cfg rawReq = .ok (spaServedPath cfg rawReq) := by
  unfold spaServe spaServedPath
  by_cases h : cfg.isFile (resolveTarget cfg rawReq)
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

/-! ## The three ledger theorems (h1.sfb / rt.7) -/

/-- **`spa_fallback_serves_index`.** A request whose resolved target is NOT a
regular file (a navigable SPA route, or any non-existent path under the root) is
served the SPA index with status `200` — precisely where a plain static serve
would have returned `404`. This is the row's defining behavior: the fallback
converts a would-be `404` into a `200` serving `index.html`. -/
theorem spa_fallback_serves_index (cfg : Config) (rawReq : List String)
    (hmiss : cfg.isFile (resolveTarget cfg rawReq) = false) :
    spaServe cfg rawReq = .ok cfg.indexPath ∧
    (spaServe cfg rawReq).status = 200 ∧
    plainServe cfg rawReq = .notFound ∧
    (plainServe cfg rawReq).status = 404 := by
  have hspa : spaServe cfg rawReq = .ok cfg.indexPath := by
    simp only [spaServe, hmiss, Bool.false_eq_true, if_false]
  have hplain : plainServe cfg rawReq = .notFound := by
    simp only [plainServe, hmiss, Bool.false_eq_true, if_false]
  exact ⟨hspa, by rw [hspa]; rfl, hplain, by rw [hplain]; rfl⟩

/-- **`spa_fallback_no_escape`.** The path the SPA handler serves — the real file
in the hit branch, the SPA index in the fallback branch — always keeps the
document root as a prefix, even under a filesystem interpreter that actually pops
a component on `..`. The fallback cannot be steered outside the root: the target
is resolved through the escape-safe `serveStatic` before the fallback decision,
and the configured index is a clean path under the (clean) root. -/
theorem spa_fallback_no_escape (cfg : Config) (rawReq : List String)
    (hroot : ∀ s ∈ cfg.docRoot, ¬ IsDot s)
    (hidx : ∀ s ∈ cfg.indexRel, ¬ IsDot s) :
    cfg.docRoot <+: descend [] (spaServedPath cfg rawReq) := by
  unfold spaServedPath
  by_cases h : cfg.isFile (resolveTarget cfg rawReq)
  · rw [if_pos h]
    exact Safety.Traversal.serveStatic_no_escape cfg.docRoot rawReq hroot
  · rw [if_neg h]
    show cfg.docRoot <+: descend [] cfg.indexPath
    unfold Config.indexPath
    have hno : ∀ s ∈ cfg.docRoot ++ cfg.indexRel, ¬ IsDot s := by
      intro s hs
      rcases List.mem_append.mp hs with hs | hs
      · exact hroot s hs
      · exact hidx s hs
    rw [Route.Path.descend_noDot hno, List.nil_append]
    exact List.prefix_append cfg.docRoot cfg.indexRel

/-- **`spa_real_file_served`.** An existing regular file is served directly with
status `200`, and the response is IDENTICAL to a plain static serve — the fallback
never masks, rewrites, or shadows a real asset. -/
theorem spa_real_file_served (cfg : Config) (rawReq : List String)
    (hhit : cfg.isFile (resolveTarget cfg rawReq) = true) :
    spaServe cfg rawReq = .ok (resolveTarget cfg rawReq) ∧
    (spaServe cfg rawReq).status = 200 ∧
    spaServe cfg rawReq = plainServe cfg rawReq := by
  have hspa : spaServe cfg rawReq = .ok (resolveTarget cfg rawReq) := by
    simp only [spaServe, hhit, if_true]
  have hplain : plainServe cfg rawReq = .ok (resolveTarget cfg rawReq) := by
    simp only [plainServe, hhit, if_true]
  exact ⟨hspa, by rw [hspa]; rfl, by rw [hspa, hplain]⟩

/-! ## Concrete witnesses (non-vacuity: the fallback actually fires) -/

/-- A demonstration config: root `srv/www`, exactly one asset `srv/www/app.js`,
SPA index `index.html`. -/
def demoCfg : Config where
  docRoot := ["srv", "www"]
  isFile := fun p => p == ["srv", "www", "app.js"]
  indexRel := ["index.html"]

/-- A navigable SPA route `/dashboard` is not a file, so it resolves to the index
`srv/www/index.html` with status `200` — not a `404`. -/
theorem demo_route_serves_index :
    spaServe demoCfg ["dashboard"] = .ok ["srv", "www", "index.html"] := by decide

/-- The plain (non-SPA) serve of the same route is a `404` — the exact behavior
the fallback improves on. -/
theorem demo_route_plain_404 :
    plainServe demoCfg ["dashboard"] = .notFound := by decide

/-- The real asset `/app.js` is served directly (`srv/www/app.js`), not the
fallback index. -/
theorem demo_file_served_directly :
    spaServe demoCfg ["app.js"] = .ok ["srv", "www", "app.js"] := by decide

/-- An adversarial `../../etc/passwd` never escapes: it is clamped under the root,
resolves to no file, and falls back to the index — the attacker gets the SPA
shell, never `/etc/passwd`. -/
theorem demo_traversal_confined :
    spaServe demoCfg ["..", "..", "etc", "passwd"] = .ok ["srv", "www", "index.html"] := by decide

end Reactor.Stage.SpaFallback

#print axioms Reactor.Stage.SpaFallback.spa_fallback_serves_index
#print axioms Reactor.Stage.SpaFallback.spa_fallback_no_escape
#print axioms Reactor.Stage.SpaFallback.spa_real_file_served
#print axioms Reactor.Stage.SpaFallback.demo_route_serves_index
#print axioms Reactor.Stage.SpaFallback.demo_traversal_confined
