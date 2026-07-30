# Route B — dregg's semantics emitted into Kimchi

*Sibling of `MINA-VERIFIES-DREGG-FRI-SIZE.md`, which prices route A. Read that one for
A's numbers; this file does not restate them, it compares against them.*

Dated 2026-07-30. Every figure below is either **MEASURED** in this session (marked) or
**PROJECTED** from a measured marginal (marked). Nothing here is quoted from a design doc.

---

## 0. The two routes, and why they are not substitutes

| | **A — witness a foreign proof** | **B — semantic re-interpretation** |
|---|---|---|
| what Mina consumes | a dregg STARK proof | a dregg state transition |
| what it establishes | *dregg's chain says this* | *this transition is VALID* |
| membership in dregg's chain | **YES** — the proof binds to a committed root | **NO.** Nothing. |
| soundness floor inherited | Kimchi/IPA **plus** dregg's undischarged FRI/STARK floor | Kimchi/IPA **only** |
| coverage of dregg's semantics | all 1,093 root-AIR constraints, by construction | only what has been re-emitted — **today, 14 of one effect's 35 constraints** |
| cost | ~2.86 × 10⁷ rows, 521–596 Pickles steps (MEASURED marginals, `MINA-VERIFIES-DREGG-FRI-SIZE.md` §3.8/§4) | ~1.05 × 10⁴ rows per effect row (PROJECTED, §3 below) |
| fits in one Pickles step | **no** — needs a ~520-step chain | **yes** — ~5 effect rows per step |

The row-count gap is ~2,700×, and it is the least interesting line in the table. **The
interesting line is "membership".** Route B proves a well-formed transition is valid. It
does not, and cannot without more machinery, prove that dregg's chain contains it. Anyone
can present a transition that never happened and B will accept it, correctly, because
validity is all B was asked about.

So B is not a cheap A. It is a different assertion that happens to cost less.

---

## 1. What landed

`metatheory/Dregg2/Circuit/Emit/KimchiEffectIncNonce.lean` — the `incrementNonceA` EffectVM
row, emitted to Kimchi from the same Lean source the BabyBear descriptor descends from.

```
incNonceHeadsBound : List Head            -- THE ONE SOURCE, 14 polynomial heads
   |                                   |    (13 row gates + the selector binding)
   | headToExpr                        | lowerHeadGens ; packGen
   v                                   v
incNonceRowGates                       incNonceKimchiRows (30 Kimchi Generic rows)
  ++ selectorGates 53 (deployed)
   |                                   |
   | incNonceVm_faithful               | kimchi_rows_force_heads
   |   (needs IncNonceRowCanon)        |   (arbitrary CommRing, no envelope over Z)
   v                                   v
        IncNonceRowIntent  ->  intent_to_cellSpec  ->  CellIncNonceSpec
                                                       ^^^^^^^^^^^^^^^^
                                                       ONE Lean def
```

The three theorems that make this a weld rather than a differential:

* **`heads_denote_deployed_gates`** — head-for-head, at EVERY assignment, `evalH` of the
  source equals `EmittedExpr.eval` of the gate body the deployed descriptor already
  carries. The source is not a third copy; it denotes the deployed list.
* **`kimchi_rows_force_heads`** — any assignment satisfying the emitted rows makes every
  source head vanish, at arbitrary `CommRing`, stated over the ACTUAL emitted list.
* **`two_emissions_one_def`** — both arrows land on `CellIncNonceSpec pre post`.

And the head that makes the claim be about `incrementNonceA` rather than about a shape:
**`selectorBindHead`**, welded by `selectorBindHead_denotes` to the deployed
`selectorGateBody 53` (which `selectorGate_in_descriptor` shows really is in
`incrementNonceVmDescriptor.constraints`). `kimchi_forces_selector` then proves the emitted
circuit forces `sel[53] = 1` on a non-NoOp row. Over ℤ that needs no primality argument at all,
where the BabyBear reading of the same gate (`selectorGate_holds_iff`) must invoke that
`2013265921` is prime to split the product — one more place the Kimchi obligation is lighter.

Plus, at the deployed field: **`kimchi_pallas_forces_cellSpec`** over `ZMod` at the Pallas
base modulus, under `KimchiRowCanon` — which the o1js circuit *discharges* with
`Gadgets.rangeCheck32` rather than assumes.

Anti-vacuity: `incNonceKimchiRows_satisfiable` exhibits a satisfying assignment (the honest
row, bal 100→100, nonce 5→6). `tamper_moved_balance_refused` and
`tamper_frozen_nonce_refused` prove **no assignment whatever** satisfies the circuit over a
row that moves value or freezes the nonce — the general statement, not a sample.

---

## 2. MEASURED — the o1js run

`cd bridge/mina-zkapp && npm run incnonce-native`, o1js 2.15.0, Node 26.4.0, this laptop.

```
witness weld vs Lean satAssign          : AGREES on all 45 intermediates
driver row vs Lean goodIncNonceRow      : IDENTICAL

solver goodIncNonceRow             : SATISFIED
solver badIncNonceRow              : VIOLATED at sub-gates [3]   <- the bal_lo freeze head's isZero
solver staleNonceIncNonceRow       : VIOLATED at sub-gates [12]  <- the nonce tick head's isZero
solver wrong selector (col 53 = 0) : VIOLATED at sub-gates [58]  <- the selector head's isZero

core rows (transcribed sub-gates only)  : 30
core gate histogram                     : {"Generic":30}
full method rows                        : 263
compile                                 : 6.40s
prove  (goodIncNonceRow)                : 4.12s
verify                                  : true in 0.35s
tamper badIncNonceRow                   : REFUSED
tamper staleNonceIncNonceRow            : REFUSED
tamper wrong selector (right shape)     : REFUSED
re-pointed public input verifies        : false
```

**30 predicted, 30 measured.** `packGen_length` says `ceil(59/2) = 30` and snarky's own
constraint system reports 30 `Generic` gates. Two compilers that were not told each other's
answer agree on the row count.

The 263-row full method decomposes (by subtraction from the measurement): 30 emitted core +
52 for 26 `rangeCheck32` (2 rows each) + 29 equality bindings + ~152 for the Mina-Poseidon
claim digest (27 fields ⇒ 14 permutations at ~11 rows). So **the semantic core is 11% of
the deployed circuit** and the rest is binding and canonicality — which is the usual shape
and worth knowing before extrapolating from 30.

---

## 3. PROJECTED — what a full turn costs under B

The marginals, all measured:

| item | rows | source |
|---|---|---|
| Poseidon2-BabyBear w16 permutation | **2,600.5** | `npm run poseidon2-rows`, re-measured today; 2,602 as a ZkProgram method |
| `hash_4_to_1` | **1 permutation** | `circuit/src/poseidon2.rs:349-362` — one `permute()`, no absorb loop |
| 14 gates of one effect (13 row + selector) | **30** | §2 |
| `rangeCheck32` | **2** | measured, `MINA-VERIFIES-DREGG-FRI-SIZE.md` §o1js-2.15 note |

One EffectVM row of `incrementNonce` (`incrementNonceVmDescriptor`) is **35 constraints**
(13 per-row gates + 14 transition + 4 first-row PI + 3 last-row PI + 1 selector), **4 hash
sites**, **2 range checks**.

| component | rows | basis |
|---|---|---|
| per-row gates + selector binding (14) | 30 | MEASURED |
| transition + boundary (21 gates) | ~45 | PROJECTED at the measured ~2.1 rows/gate |
| canonicality range checks (26 cells) | 52 | MEASURED marginal |
| **`state_commit` — 4 × `hash_4_to_1`** | **10,402** | MEASURED marginal × 4 |
| **total per effect row** | **≈ 1.05 × 10⁴** | |

**The commitment hashing is 98.8% of it.** Route B does not escape the thing that makes
route A expensive; it just pays it 2,700× fewer times.

Consequences:

* **~5 effect rows per Pickles step** (5 × 10,534 = 52,670 against ~55,000 usable). A
  small turn is ONE step. Route A's smallest honest geometry is a ~520-step chain.
* **Break-even against A is ≈ 2,700 effect rows.** If one dregg proof covers N turns of k
  effects each, B is cheaper while `N·k < 2,700`.
* ⚑ **And B does NOT scale to a dregg trace.** The 1.05 × 10⁴ is per *semantic* effect row,
  because B checks the SPEC and skips the trace entirely — no memory table, no hash table,
  no padding, none of the other six root tables. If you instead re-emitted dregg's AIR row
  by row, you would pay (trace rows) × (per-row cost) — and dregg's root tables run to
  `degree_bits = 15`, i.e. 32,768 rows each. Even at 100 Kimchi rows per trace row and no
  hashing that is ~3 × 10⁶ per table, and seven tables puts you back at A's order with none
  of A's coverage. **B is cheap only because it is small, and it is small only because it
  checks less.**

---

## 4. ⚑ What makes B untrustworthy, named

This section is worth more than the demo. Every item is a real gap in what landed, not a
future-work wish.

### 4.1 The Kimchi emission covers 14 of the descriptor's 35 constraints

`incNonceHeadsBound` denotes `incNonceRowGates ++ selectorGates 53`. The deployed
`incrementNonceVmDescriptor.constraints` also carries `transitionAll` (14),
`boundaryFirstPins` (4) and `boundaryLastPins` (3). Those 21 are not emitted to Kimchi.

`transitionAll` is cross-row (`next[sb+hi] = this[sa+lo]`) and this emission is single-row,
so **the Kimchi circuit checks one row in isolation and nothing chains it to a neighbour.**
A sequence of individually-valid rows is not thereby a valid trace. The boundary PI pins are
what tie a row's nonce to `PI[ACTOR_NONCE]`, also absent.

⚑ *Was worse, and is now fixed:* until `selectorBindHead` landed this section also read "the
circuit never checks that this is an `incrementNonce` row" — it checked the SHAPE and any
effect with that shape passed. `selectorGates 53` is now emitted, `kimchi_forces_selector` is
the theorem, and `tamper wrong selector` in §2 is the exhibit.

### 4.2 The commitment binding is absent — this is the big one

`incrementNonceVmDescriptor.hashSites` has 4 GROUP-4 sites folding the after-state into
`state_commit`. The Kimchi emission has **none**. So the circuit proves a relation between
two *bare* 13-tuples of field elements. It does not prove they are the pre-image of any
commitment, and therefore does not prove they are a dregg cell at all.

This is exactly where §3 says all the cost is (10,402 of ~10,530 rows), so the cheap number
in §3 is a number for the *complete* thing while what actually ran is the 30-row core.
Both are stated; do not read one for the other.

Until the hash sites land, "route B checks a dregg transition" should be read as "route B
checks a dregg transition's ARITHMETIC".

### 4.3 The Lean forcing lemma covers 30 of the 263 deployed rows

The theorem is about `incNonceKimchiRows`. The compiled circuit is 263 rows: the 30, plus
`rangeCheck32`s, plus column bindings, plus a Mina-Poseidon digest — all emitted by o1js,
none of them in the Lean model.

Soundness survives this trivially (a satisfying assignment for 248 rows satisfies the 27,
so the forcing applies), and that argument is stated here rather than proved. What does
NOT survive automatically is *completeness*: the extra 233 rows could in principle make
honest transitions unprovable. They do not — §2 proved one — but that is an exhibit, not a
theorem.

⚑ Note the extra rows include `RangeCheck0`, `Zero` and `Lookup` gates, and
`KimchiTarget.holds` models `Lookup` as **`False`**. So the deployed circuit contains rows
the Lean target model calls unsatisfiable. That is a modelling gap, not a defect in the
circuit — but it means `rowsHold` is *not* a model of the compiled artifact, only of the
sub-list the compiler emitted.

### 4.4 The o1js side reaches into o1js internals

`kimchi-raw-gates.ts` deep-imports `Gates.generic` past o1js's `exports` map, because the
supported alternative (writing `Field` arithmetic and letting o1js lower it) would make the
measured row count o1js's compiler's decision rather than the Lean lowering's — and then
comparing it to 30 would mean nothing. Pinned at 2.15.0; the resolver **refuses** rather
than falling back. Named seam.

### 4.5 `lowerHeadsGens` has no freshness theorem

Chaining the lowering across 14 heads threads a watermark. `lowerHead_sound` needs no
freshness (each sub-gate forces its output from its inputs), so **soundness is unaffected**
by a watermark bug. Completeness is not: overlapping watermarks would make honest
instances unsatisfiable. `incNonceKimchiRows_satisfiable` rules that out for this
instance, by exhibit. There is no general lemma.

### 4.6 The TypeScript witness solver is an independent implementation

It reads only the emitted coefficients and never learns which dregg gate anything came
from. It is welded to Lean's own witness (`honestFresh`, all 45 intermediates checked
before any measurement runs). A solver bug is a liveness failure, not a soundness one —
the emitted gates are the authority either way.

### 4.7 Where the two sides are asymmetric — and it runs the *other* way

The fear worth having is "the BabyBear forcing lemma is weaker than the Kimchi one, so the
shared-source argument leaks". Measured: **it is the BabyBear side that is weaker.**

`incNonceVm_faithful` reads its gates through `holdsVm`, i.e. `≡ 0 [ZMOD 2013265921]`, so
it needs the full `IncNonceRowCanon` envelope *including* `nonce_before + 1 < p`. The
Kimchi side over ℤ needs no envelope at all; over Pallas it needs `KimchiRowCanon`, which
drops the overflow hypothesis and widens the per-cell box to `2^32`.
`kimchiRowCanon_of_incNonceRowCanon` proves the implication;
`kimchi_envelope_strictly_weaker` exhibits a row satisfying the Kimchi envelope and not the
BabyBear one.

There is a second asymmetry in the same direction: `holdsVm` makes `.gate` **`True`** on
the last row (`isLast = true`), so the deployed BabyBear AIR does not bind the wrap row.
The Kimchi emission has no such notion and binds unconditionally.

So the shared-source argument is sound in the direction that matters. It is bounded by
§4.1 and §4.2 — by *how much* of the semantics has been emitted — not by a strength
mismatch between the two forcing lemmas.

---

## 5. The answer to the question B was built to answer

**Are the two emissions provably the same semantics?**

For the thirteen per-row gates of `incrementNonceA` plus its selector binding: **yes, and it
is a theorem, not a test.** One `def`-generated `List Head`; a denotational identity to the
deployed BabyBear gate bodies at every assignment; a forcing lemma on each side; both landing
on one Lean `def`. That is a stronger tie than route A's own extraction seam
(`to_dag`/`to_dag_full`, which is checked differentially and whose header says so).

For the rest of the descriptor — the transition continuity, the boundary pins, and above all
the commitment sites — **there is no second emission at all yet**, so the question does not
arise there and must not be answered by extension.

**What does B establish that A does not?**

* Validity **without inheriting dregg's FRI/STARK floor.** B consumes no proof, so nothing
  in it rests on the undischarged soundness of dregg's FRI parameters. Its floor is
  Kimchi/IPA over Pasta, which is a shallower and better-understood stack.
* A transition Mina can check **in one Pickles step**, at ~10⁴ rows rather than ~10⁷ — so
  a Mina-side contract can gate on a dregg transition without a 520-step aggregation tree
  existing first.
* Something checkable **before dregg has proved anything**: B applies to a proposed
  transition, A only to a finished proof.

**What does A establish that B does not?**

* **That dregg's chain contains it.** This is the whole difference and it should not be
  blurred. B says "this is a valid transition". A says "dregg proved this". A well-formed
  transition that never happened passes B and fails A.
* **Coverage.** A verifies a proof about all 1,093 constraints of dregg's seven root
  tables, whatever they say, without anyone re-emitting them. B covers exactly what has
  been re-emitted — 14 constraints of 35, of one effect out of 54 — and every extension is
  fresh work with a fresh chance to diverge.
* **Independence from the re-emission itself.** A cannot drift from dregg's semantics,
  because it does not restate them. B is a second statement of the same thing, and
  §4.1–§4.2 are what that costs.

---

## 6. Reproduce

```
# Lean — build the module and re-emit the artifact
scripts/hbuild <lane> bash -c 'cd metatheory && lake build Dregg2.Circuit.Emit.KimchiEffectIncNonce \
    && lake env lean --run EmitKimchiIncNonce.lean'   # > bridge/mina-zkapp/src/generated/kimchi-incnonce-b.json

# o1js — compile, prove, verify, tamper
cd bridge/mina-zkapp && npm run incnonce-native
```

Complete root build (`lake build Dregg2`) ran on hbox lane `kimchi-semb`: VERDICT PASS, 0
errors, floor-ratchet OK (2,103 grandfathered carriers over 34 refuted floors; baseline
2,227, slack 124).
