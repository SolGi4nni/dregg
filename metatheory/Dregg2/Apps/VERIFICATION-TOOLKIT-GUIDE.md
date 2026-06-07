# Userspace App Verification Toolkit — Author's Guide

`Dregg2/Apps/VerificationToolkit.lean` is a reusable framework for verifying starbridge
userspace apps. Before it, every app (`StorageGatewayMandate`, `CompartmentWorkflowMandate`,
`NameserviceGated`, …) hand-rolled the same five proofs. The toolkit proves that pattern
**once**, parametrically; a new app author supplies a spec and inherits the verification.

This guide shows what you supply and what you get.

---

## 1. The mental model

At the executor boundary, an app's userspace state move is a **scalar slot write** `old → new`
on one `FieldName` of the app's mandate cell:

- a workflow's `step_cursor` advancing `c → c+1`;
- a storage gateway's `last_op` recording an op code;
- a subscription's monotone sequence head;
- a governed namespace's `version`.

All the rich off-line logic — clearance graphs, DAG prerequisites, key-prefix strings, op
allowlists — is **folded by you, the author, into a `Bool` predicate** before it reaches that
scalar boundary:

```
admit : Int → Int → Bool      -- "may this slot move old → new?"
```

This is exactly what the existing apps already do (`cwmAdvanceAdmits` folds DAG+clearance into a
cursor-keyed `Bool`; `sgmOpAdmitted` folds the op-allowlist+clearance into an op-code `Bool`). The
toolkit's generic admission unit is this `admit`.

---

## 2. What you supply: an `AppSpec`

```lean
structure AppSpec where
  slot     : FieldName        -- your app's scalar state slot
  cell     : CellId           -- the cell carrying your mandate program
  admit    : Int → Int → Bool -- your folded admission predicate
  oldRange : List Int         -- the committed values your cell ranges over
  newRange : List Int         -- the written values your cell ranges over
```

`oldRange`/`newRange` are the finite grid the toolkit bakes the admit-table over. Outside the
grid the executor is fail-closed by absence — which is **sound** (it never admits more than your
`admit`). Pick a grid that covers every transition your app actually performs.

Example (the CWM charter, `review → redact → sign`):

```lean
def cwmSpec : AppSpec where
  slot     := stepCursorSlot
  cell     := 0
  admit    := fun old new =>
    decide (new = old + 1) && decide (0 ≤ old) && cwmAdvanceAdmits charterMandate3 old.toNat
  oldRange := [0, 1, 2, 3]
  newRange := [1, 2, 3, 4]
```

That is the **entire** author-supplied input. The toolkit derives everything below.

---

## 3. What you get, generically (no re-proof)

The toolkit installs `sp.caveats` (an `.admitTable` baked from your `admit`) on the cell, and
gives you these theorems — each is a one-line instantiation, proven once over **any** `AppSpec`:

| You instantiate | You get |
|---|---|
| `caveatsAdmit_eq_table sp …` | the executor's `caveatsAdmit` on your slot == your admit-table membership |
| `caveatsAdmit_iff_admit sp …` | the executor's caveat gate admits **iff** `sp.admit old new` |
| `app_commit_iff_admit sp …` | **COMMIT-IFF-ADMIT**: `stateStepGuarded` commits iff `admit` ∧ authority — over the WHOLE post-state, not a projection |
| `app_violation_rejected sp …` | **THE TOOTH**: an `admit`-false transition is rejected `= none` by the executor |
| `app_commit_conserves sp …` | committed write preserves total balance (your slot ≠ `balance`) |
| `app_commit_no_amplify sp …` | committed write leaves the authority graph fixed — **no capability minted** |
| `app_commit_authorized sp …` | committed write implies the actor held authority over the cell |
| `app_commit_field_written sp …` | after commit, the slot reads back exactly the written value |

`app_commit_iff_admit` is the headline. It generalizes every per-app `*_commit_iff_admit`
(CWM/SGM) into one parametric theorem; you no longer re-prove the executor↔predicate plumbing.

### Re-deriving your app's named theorems

Wrap the generic theorems behind your app's names so callers see a clean surface:

```lean
theorem myapp_illegal_advance_rejected (s : RecChainedState)
    (hprog : s.kernel.slotCaveats 0 = mySpec.caveats) (actor : CellId) (c : Int)
    (hcur : mySpec.committed s.kernel = c)
    (hold : c ∈ mySpec.oldRange) (hnew : (c+1) ∈ mySpec.newRange)
    (hbad : mySpec.admit c (c+1) = false) :
    stateStepGuarded s mySpec.slot actor 0 (c+1) = none :=
  app_violation_rejected mySpec s hprog actor (c+1) (by rw [hcur]; exact hold) hnew
    (by rw [hcur]; exact hbad)
```

See `cwm_*_via_toolkit` and `sgm_op_*_via_toolkit` in `VerificationToolkit.lean` for two worked
re-derivations (CompartmentWorkflowMandate and StorageGatewayMandate's op-leg).

---

## 4. Non-vacuity discipline (REQUIRED)

A generic theorem is worthless if your instance is trivial. Every app MUST prove its instance is
**non-vacuous** with `#guard` witnesses showing:

1. a **legal** transition is admitted (the commit half is reachable): `#guard mySpec.admit a b`;
2. an **illegal** transition is rejected (the tooth bites):
   `#guard mySpec.admit a c == false` and `#guard mySpec.admitTable.contains (a, c) == false`;
3. the admit-table is the expected size (it is not all-true or all-false):
   `#guard mySpec.admitTable.length == N`.

The toolkit's own `§DEMO` blocks do exactly this (the CWM table has length 3 = the legal
advances; the no-clearance GET is absent from the guest op-table). Pin `#assert_axioms` over
every named theorem your app exposes.

---

## 5. The Rust-side differential corpus (mirror-drift tooth)

Your Rust admission mirror (`starbridge-apps/<app>/src/lib.rs::<app>_admit`) is a hand-port of
`mySpec.admit`. A hand-port can silently drift (drop a clearance leg, flip a `≤`). The toolkit
gives you `AppSpec.diffCorpus` to pin both sides against:

```lean
def AppSpec.diffCorpus (sp : AppSpec) : List Bool :=   -- row-major over oldRange × newRange
  sp.oldRange.flatMap fun old => sp.newRange.map fun new => sp.admit old new

def AppDiffPinned (sp : AppSpec) (v : List Bool) : Prop := sp.diffCorpus = v
```

**Lean side** — pin the literal decision vector:

```lean
#guard AppDiffPinned mySpec
  [ false, true, true,   -- old = oldRange[0]: new = newRange[0], [1], [2]
    … ]                  -- (must contain BOTH true and false to be non-vacuous)
```

**Rust side** — `starbridge-apps/<app>/tests/<app>_lean_differential.rs` enumerates the
**identical grid** through the Rust mirror and asserts the **same vector**, copied verbatim from
the Lean `#guard`:

```rust
#[rustfmt::skip]
const APP_LEAN_DECISIONS: [bool; N] = [ /* paste the Lean #guard literal here */ ];

#[test]
fn app_admit_matches_lean_corpus() {
    let mut rust = Vec::new();
    for &old in &OLD_RANGE {
        for &new in &NEW_RANGE {
            rust.push(app_admit(old, new));   // your Rust mirror
        }
    }
    assert_eq!(rust.as_slice(), &APP_LEAN_DECISIONS[..],
        "Rust app_admit DRIFTED from the proven Lean mySpec.admit");
}
```

Drift on **either** side fails:

- Rust mirror changes → Rust vector ≠ `APP_LEAN_DECISIONS` literal → `cargo test` fails;
- Lean `admit` changes → the `#guard AppDiffPinned …` trips at Lean build → forced re-pin that
  re-exposes any Rust drift.

(Template: `compartment-workflow-mandate/tests/cwm_lean_differential.rs`,
`storage-gateway-mandate/tests/sgm_lean_differential.rs`.)

---

## 6. Checklist for a new verified app

1. Fold your app's admission logic into `admit : Int → Int → Bool`.
2. Define `mySpec : AppSpec` (slot, cell, admit, grid).
3. Install `mySpec.caveats` on the cell at factory-mint time.
4. Re-export the toolkit theorems behind your app's names (commit-iff-admit, tooth,
   conservation, non-amplification).
5. `#guard` the non-vacuity witnesses (legal admitted, illegal rejected, table size).
6. `#guard AppDiffPinned mySpec [...]` and write the matching Rust differential test.
7. `#assert_axioms` every named theorem.

That is the whole verification surface — derived, not hand-rolled.
