import Reactor.Pipeline

/-!
# Reactor.BraidCalculus — the braid composition calculus (a proof force-multiplier)

Each braided-serve stage's *composition* proof (that appending a config-gated stage
at the head of the deployed fold is faithful when the marker is off, and genuinely
fires when it is on) was written BESPOKE in `Reactor.Deploy` §8/§8h/§8j: ~30-40 lines
of `prepend_pass`-peeling + `pipeline_gate_status`/`pipeline_stage_effect` plumbing per
stage, repeated for every gate and every transform. `Deploy.prepend_pass` already
generalized the PASS-THROUGH case into one axiom-free lemma. This file generalizes the
other two families and packages the whole pattern, so a NEW braid stage's composition
proof becomes a ONE-LINER (a single application of one of the three lemmas below).

Everything here is **additive and standalone**: it imports only `Reactor.Pipeline`
(the proven calculus kernel) and depends on NOTHING in `Reactor.Deploy`. `Deploy` — and
the braid swarm — will `import Reactor.BraidCalculus` and USE it; the calculus never
reaches back. It re-proves `prepend_pass` locally (2 lines from `pipeline_cons`) so it
carries no `Deploy` dependency.

## The three general lemmas (each SUBSUMES a whole bespoke family)

* `braid_gate` — GENERAL gate composition. A chain `pref ++ G :: rest` where every stage
  in `pref` is transparent-on-`c` and `G` short-circuits with a fixed status: the built
  pipeline status is exactly the gate's, through a status-stable tail. SUBSUMES
  `braided2_conn/stick/slow_denies_status` + `braided3_conditional_304` (4 bespoke).
* `braid_transform` — GENERAL transform composition. A chain `pref ++ T :: rest` with a
  transparent prefix and a passing transform `T`: the built pipeline is `T.onResponse`
  applied at its onion position over the tail. SUBSUMES `braided2_errorpage_maps_404` /
  `braided2_compress_encodes` / `braided3_variants_vary` / `braided3_autoindex_lists`
  (4 bespoke).
* `braided_off_eq_extend` — GENERAL byte-identity-when-off composition. Extending a
  proven-off chain (`runPipeline base = runPipeline target`) with a transparent prefix
  preserves the equality. SUBSUMES `braided_off_eq` / `braided2_off_eq` /
  `braided3_off_eq` (3 bespoke) — the `prepend_pass`-family, mirrored.

Each closes by `rw`/induction over the `Reactor.Pipeline` kernel, so — like the kernel —
it depends on no axioms beyond `{propext, Quot.sound}` (a subset of the allowed
`{propext, Quot.sound, Classical.choice}`); none is vacuous (each is instantiated by the
concrete `Deploy` braid stages — see `Reactor/BraidCalculusDemo.lean`, which re-derives
four bespoke theorems as one-line applications).
-/

namespace Reactor.BraidCalculus

open Reactor.Pipeline
  (Stage Ctx StageStep ResponseBuilder runPipeline
   pipeline_cons pipeline_gate_status pipeline_stage_effect)

/-! ## The transparent-prefix engine -/

/-- A stage is **contextually transparent** on `c` when its request phase passes `c`
unchanged and its response phase is the identity on `c` — the config-gated-OFF shape a
braid stage takes when its per-request marker is absent. This is definitionally the
conjunction the `Deploy` `*BraidStage_off` lemmas already conclude, so those lemmas
supply `Transparent … c` for free. -/
def Transparent (X : Stage) (c : Ctx) : Prop :=
  X.onRequest c = .continue c ∧ ∀ b, X.onResponse c b = b

/-- **`prepend_pass` — the pass-through composition law** (re-proven here, standalone,
from `pipeline_cons` only, so this file carries no `Deploy` dependency). Composing a
transparent stage `X` at the head leaves the built response unchanged. -/
theorem prepend_pass (X : Stage) (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hX : Transparent X c) :
    runPipeline (X :: rest) h c = runPipeline rest h c := by
  rw [pipeline_cons, hX.1]
  exact hX.2 _

/-- **`braid_prefix_pass` — peel a whole transparent prefix.** When every stage in
`pref` is transparent on `c`, the fold over `pref ++ rest` equals the fold over `rest`:
`prepend_pass` peeled `|pref|` times. The engine under all three general lemmas. -/
theorem braid_prefix_pass (pref rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hpref : ∀ X ∈ pref, Transparent X c) :
    runPipeline (pref ++ rest) h c = runPipeline rest h c := by
  induction pref with
  | nil => rfl
  | cons X xs ih =>
    show runPipeline (X :: (xs ++ rest)) h c = runPipeline rest h c
    rw [prepend_pass X (xs ++ rest) h c (hpref X (List.mem_cons_self))]
    exact ih (fun Y hY => hpref Y (List.mem_cons_of_mem _ hY))

/-! ## `hpref` builders (make the transparent-prefix side condition a one-liner) -/

/-- The empty prefix is transparent. -/
theorem nil_transparent (c : Ctx) : ∀ X ∈ ([] : List Stage), Transparent X c := by
  intro X hX; cases hX

/-- Cons a transparent head onto a transparent tail — so a k-stage transparent prefix
is `cons_transparent h₁ (cons_transparent h₂ (… (nil_transparent c)))`. -/
theorem cons_transparent {X : Stage} {xs : List Stage} {c : Ctx}
    (hX : Transparent X c) (hxs : ∀ Y ∈ xs, Transparent Y c) :
    ∀ Z ∈ X :: xs, Transparent Z c := by
  intro Z hZ
  rcases List.mem_cons.mp hZ with rfl | h
  · exact hX
  · exact hxs Z h

/-! ## (1) `braid_gate` — the general gate-composition lemma -/

/-- **`braid_gate` — the GENERAL gate composition law.** For a chain
`pref ++ G :: rest` where every stage in `pref` is transparent on `c`, the gate `G`
short-circuits with a fixed response `r` on `c`, and every stage in `rest` is
status-stable: the BUILT pipeline status is exactly `r.status`. The transparent prefix
is peeled (`braid_prefix_pass`), then the gate's status survives the status-stable inner
onion (`pipeline_gate_status`).

ONE lemma subsuming `braided2_conn_denies_status` (pref `[]`), `braided2_stick_denies_status`
(pref `[conn]`), `braided2_slow_denies_status` (pref `[conn, stick]`), and
`braided3_conditional_304` (pref `[]`) — each becomes a one-line application. -/
theorem braid_gate (pref : List Stage) (G : Stage) (rest : List Stage)
    (h : Ctx → Response) (c : Ctx) (r : Response)
    (hpref : ∀ X ∈ pref, Transparent X c)
    (hg : G.onRequest c = .respond r)
    (hst : ∀ t ∈ rest, Stage.statusStable t) :
    ((runPipeline (pref ++ G :: rest) h c).build).status = r.status := by
  rw [braid_prefix_pass pref (G :: rest) h c hpref]
  exact pipeline_gate_status G rest h c r hg hst

/-! ## (2) `braid_transform` — the general transform-composition lemma -/

/-- **`braid_transform` — the GENERAL transform composition law.** For a chain
`pref ++ T :: rest` where every stage in `pref` is transparent on `c` and the transform
`T` passes the request phase (`.continue c'`): the BUILT pipeline is `T.onResponse c'`
applied at its onion position over the tail fold `runPipeline rest h c'`. The transparent
prefix is peeled (`braid_prefix_pass`), then the transform is placed at the right onion
position (`pipeline_stage_effect`). A stage instantiates by rewriting `T.onResponse c'`
to its concrete effect (its `*BraidStage_on` lemma) and `build_mapResp`/`build_addHeader`.

ONE lemma subsuming `braided2_errorpage_maps_404`, `braided2_compress_encodes`,
`braided3_variants_vary`, and `braided3_autoindex_lists` — each becomes a one-line
application followed by its own byte fact. -/
theorem braid_transform (pref : List Stage) (T : Stage) (rest : List Stage)
    (h : Ctx → Response) (c c' : Ctx)
    (hpref : ∀ X ∈ pref, Transparent X c)
    (hcont : T.onRequest c = .continue c') :
    runPipeline (pref ++ T :: rest) h c = T.onResponse c' (runPipeline rest h c') := by
  rw [braid_prefix_pass pref (T :: rest) h c hpref]
  exact pipeline_stage_effect T rest h c c' hcont

/-! ## (3) `braided_off_eq_extend` — the general byte-identity-when-off composition -/

/-- **`braided_off_eq_extend` — the GENERAL off-composition law.** Extending a
proven-off chain (`runPipeline base h c = runPipeline target h c`) with a transparent
prefix `pref` preserves the equality: `runPipeline (pref ++ base) h c = runPipeline
target h c`. So a new marker-gated stage's `off_eq` is `braided_off_eq_extend [newStage]
oldChain target … (transparent-prefix) (old off_eq)` — a one-line instantiation.

ONE lemma subsuming `braided_off_eq`, `braided2_off_eq`, and `braided3_off_eq` (the
`prepend_pass`-family, mirrored): each peels its transparent head stages then defers to
the smaller off-equality. -/
theorem braided_off_eq_extend (pref base target : List Stage) (h : Ctx → Response) (c : Ctx)
    (hpref : ∀ X ∈ pref, Transparent X c)
    (hbase : runPipeline base h c = runPipeline target h c) :
    runPipeline (pref ++ base) h c = runPipeline target h c := by
  rw [braid_prefix_pass pref base h c hpref, hbase]

/-! ## The `braid_stage` tactic bundle

A thin tactic wrapper over the lemma bundle (named honestly — a **bundle + macro**, not
a goal-inspecting elaborator: the caller supplies the explicit prefix, since
`?pref ++ ?G :: ?rest` against a `def`-folded chain is higher-order and Lean will not
guess the split). It reduces a braided gate-status goal to its three obligations in one
line:

```
theorem my_gate_denies (c) (hfind) : ((runPipeline myChain h c).build).status = S := by
  braid_gate_close [aStage, bStage]
    (cons_transparent (aStage_off c ha) (cons_transparent (bStage_off c hb) (nil_transparent c)))
    (gStage_denies c nv hfind)
    (fun t ht => myChain_statusStable t (by …))
```

For transforms, apply `braid_transform` directly (the goal is an equation to `rw` with,
then finish with the stage's own byte fact). -/
macro "braid_gate_close" pref:term hpref:term hg:term hst:term : tactic =>
  `(tactic| exact braid_gate $pref _ _ _ _ _ $hpref $hg $hst)

end Reactor.BraidCalculus
