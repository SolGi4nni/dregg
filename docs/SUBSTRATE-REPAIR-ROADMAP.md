# Substrate-Soundness Repair Roadmap

From a driving-first audit (2026-07-12) + the offering/game lanes' findings. Each item was found because an offering
or game had to WORK AROUND it. Fix at the root; retire the workarounds. (STATUS updated as lanes land.)

## CONFIRMED (code-evidenced), ranked by load-bearing × cheap
1. **Bazaar pair — vacuous self-modifying gate + clamp-hidden underflow** (MUST fix together). The scene compiler's
   pre->post lift (`spween-dregg/src/compiler.rs:444-475`) collapses `{gold>=50} ~ gold-=50` to `FieldGte(slot,0)`
   (always true) when the spend meets the threshold; `world.rs:292` CLAMPS an underflowing Modify at 0 instead of
   refusing — so an ineligible spend commits. Fix: world.rs rejects on underflow; the compiler stops encoding a
   pre-state floor via a clamped post-state threshold. App-level, cheap. → IN FLIGHT (spween lane).
2. **Le/Lt over-strict clamp** (`compiler.rs:458-466`) — same threshold-clamp root, opposite direction (spurious
   false rejection of eligible plays). Fold into #1. → IN FLIGHT (spween lane).
3. **Passage entry-effect re-run** — `Driver::advance`/`flush` (`world.rs:591-623`) commit a destination passage's
   entry effects UNGATED under the choice's method; a cycle back re-seeds state. Fix: a compiler-emitted once/WriteOnce
   guard on entry-effect slots (the re-run is external `spween::Runtime` behavior). → IN FLIGHT (spween lane).
4. **Scene-compiler dispatch-default-deny — dead heap hatch.** `compile_scene` (`compiler.rs:175-224`) builds
   `CellProgram::Cases` with only per-choice `MethodIs` cases + NO `Always` catch-all, so `apply_raw` (the >16-slot
   heap-collection escape hatch, `world.rs:333`) matches no case -> refused (`NoTransitionCaseMatched`). apply_raw/
   read_heap have ZERO test coverage. Fix: compiler emits an `Always`-guarded catch-all (or a heap-method case). Cheap.
   → TODO (fold into the spween lane / a follow-up; pin with a 5-line apply_raw repro first).

## SUSPECTED (mechanism evidenced, needs a driven repro)
5. **AffineLe-quorum aliasing in collective-choice** (SECURITY). Quorum = `AffineLe{M·RESOLVED − ΣTALLY ≤ 0}` with
   TALLY slots carrying ONLY `Monotonic` (`collective-choice/src/lib.rs:520-540`) — no per-turn delta cap, no per-voter
   actor binding. If `vote.rs` doesn't bind writer->distinct voter + cap the increment to +1, ONE actor can inflate a
   TALLY slot to M and arm RESOLVED — a forged quorum (the exact weakness `CountGe` was minted to replace, see
   `cell/src/program/types.rs:688-694`). Affects /council + the liquidity vote. Fix: migrate to `CountGe`, or add
   per-turn delta caps + per-slot actor binding. → IN FLIGHT (quorum lane).

## KERNEL + CIRCUIT (coordinate with metatheory/circuit — do NOT ship Rust ahead of the Lean/AIR twin)
K1. **HeapAtom has no exact-delta twin + no cross-key relation** (`cell/src/program/types.rs:468-489`). `DeltaBounded`
    bounds |Δ| but doesn't PIN it; every HeapAtom is single-key (no heap `FieldLteOther`). So heap-keyed quantities
    can't carry exact conservation teeth — the Bazaar hoisted its purse into fixed slots to get FieldDelta. Fix: add
    `HeapAtom::DeltaEquals{d}` + a cross-key relational atom, each an append-only variant WITH its Lean twin
    (`metatheory/Dregg2/Exec/Program.lean`) + the circuit AIR. → HELD (schedule when the circuit swarm settles).

## VERIFIED-FIXED (do NOT re-open)
- dregg-doc `three_way` now consumes its base (`graph.rs:399-440`) — fixed this session.
- The dispatch-default-deny KERNEL guard is correct (`eval.rs:101-129` + the `is_method_dispatching` carve-out).
- `starbridge-apps/nameservice` + `escrow-market` carry an `Always` invariants case (no default-deny). NOTE: the
  BROKEN one is `starbridge-nameservice` (what dreggnet-names wraps), being fixed separately.
- collective-choice's PROGRAM is a pure `Always` invariants program (no default-deny) — the exposure is #5's TALLY
  binding, not the dispatch.

## STATUS (2026-07-12, after the repair swarm)
FIXED + committed:
- #1/#2/#3-compiler (Bazaar pair) — spween-dregg/compiler.rs: the clamp-defeated lift now emits a companion FieldDelta;
  the broke buyer is REFUSED. Driven 153/0 (dungeon-on-dregg 118 incl. dice-combat + the workarounds).
- #5 (quorum aliasing, SECURITY) — collective-choice: RESOLVED gated on CountGe (>=M distinct committed voters, actor-
  bound commitment); a single-actor tally-inflation forge is REFUSED. Driven 11/0; /council + the liquidity vote inherit.
- nameservice dispatch-default-deny — starbridge-nameservice name_cell_program -> a flat Predicate; the app's own 6
  integration tests pass again; teeth still bite.
PENDING an ember action:
- #3-runtime (BUG 2, passage re-entry re-run) — FIXED on disk in the EXTERNAL ~/dev/spween (effects_executed HashSet),
  but breadstuffs pins emberian/spween@afb5b1f, so it lands only by committing+pushing spween + bumping the rev in
  spween-dregg/Cargo.toml. The test retreat_into_seed_room_does_not_reseed is #[ignore]d until then.
STILL TODO (app-level, cheap):
- #4 (dead heap hatch) — compile_scene (spween-dregg/compiler.rs) still emits Cases with NO Always catch-all, so apply_raw
  (the >16-slot heap-inventory hatch) is refused by dispatch-default-deny. NOT addressed by the Bazaar-pair fix. A
  follow-up: emit an Always-guarded catch-all (pin with a 5-line apply_raw repro first).
- NEW: wasm/src/bindings_card.rs:1263 has its OWN independent Monotonic-tally poll_program with the SAME quorum-aliasing
  shape as #5 — apply the CountGe fix there too (the quorum lane flagged it).
HELD (coordinated kernel pass): K1 (HeapAtom::DeltaEquals + a cross-key relational atom) — Rust + Lean twin + AIR, with
the metatheory/circuit terminal.
