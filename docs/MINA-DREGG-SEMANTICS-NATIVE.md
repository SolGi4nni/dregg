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
| coverage of dregg's semantics | all 1,093 root-AIR constraints, by construction | only what has been re-emitted — **today, 14 of one effect's 35 constraints PLUS its 4 GROUP-4 commitment sites** |
| cost | ~2.86 × 10⁷ rows, 521–596 Pickles steps (MEASURED marginals, `MINA-VERIFIES-DREGG-FRI-SIZE.md` §3.8/§4) | **1.00 × 10⁴ rows per effect row (MEASURED, §3 below)** |
| fits in one Pickles step | **no** — needs a ~520-step chain | **yes** — **6 effect rows per step** (MEASURED; the projection said ~5) |

The row-count gap is ~2,850×, and it is the least interesting line in the table. **The
interesting line is "membership".** Route B proves a well-formed transition is valid. It
does not, and cannot without more machinery, prove that dregg's chain contains it. Anyone
can present a transition that never happened and B will accept it, correctly, because
validity is all B was asked about.

⚑ **The GROUP-4 commitment binding landed on 2026-07-30 and it does NOT move that line.**
Before it, B related two bare 13-tuples and did not prove they were the pre-image of any
commitment — i.e. did not prove they were a dregg *cell*. Now it does. But "a valid
transition of a real, well-formed cell" is still not "a transition dregg's chain contains":
you may invent a 13-tuple, hash it honestly with the deployed `hash_4_to_1` tree, and
present the pair. The binding closed the gap between *arithmetic* and *cell*. It closed
nothing between *cell* and *membership*, and it is worth being explicit that it could not
have.

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

### 1.1 And, since 2026-07-30, the COMMITMENT BINDING

`metatheory/Dregg2/Circuit/Emit/KimchiCellCommit.lean` — the four GROUP-4 `hash_4_to_1` sites
the deployed descriptor carries, emitted, so the circuit proves the 13-tuples are the pre-image
of a named commitment rather than two bare tuples.

```
incNonceHashSites : List VmHashSite       -- THE DEPLOYED site list (= transferHashSites)
   |                                   |
   | siteHoldsAll (ASSUMED)            | inColsGo ; h4Gen = KimchiPoseidon2.permGen ; renderOps
   v                                   v
the BabyBear hash layer                commitRows (10,570 emitted rows; 10,010 in snarky)
   |                                   |
   | transferHash_binds                | commit_rows_force_siteHoldsAll  [DigestCarrier]
   v                                   v
          cellCommitOf hash a  =  state_after.state_commit
          ^^^^^^^^^^^^^^^^^^^
          ONE Lean def
```

Same discipline: the four permutations are `def`-generated (141 S-boxes, none spelled out), the
WIRING is computed from the deployed site list rather than restated, and the o1js side
transcribes the instruction stream and the Lean-computed witness. `two_emissions_one_commit` is
the apex; `tamper_non_preimage_refused` is the general tooth. §4.2 is the full account,
including the one undischarged carrier and the three defects of the emitted object that stand
between it and a proof.

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

## 3. MEASURED — what one effect row costs under B

*Was PROJECTED until 2026-07-30. The four GROUP-4 hash sites are now emitted
(`metatheory/Dregg2/Circuit/Emit/KimchiCellCommit.lean`) and compiled, so the number below is
a measurement of the thing, not an extrapolation from a marginal.*

The four `hash_4_to_1` sub-circuits are `KimchiPoseidon2.permGen` — the Lean `def`-generator
folded over the imported round constants — wired by `inColsGo`, which COMPUTES the absorbed
columns from the deployed `incNonceHashSites` rather than restating them:

```
site 0   H4(sa.bal_lo, sa.bal_hi, sa.nonce, sa.field0)          cols [76,77,78,79]  -> aux 98
site 1   H4(sa.field1..4)                                       cols [80,81,82,83]  -> aux 99
site 2   H4(sa.field5, .field6, .field7, sa.cap_root)           cols [84,85,86,87]  -> aux 100
site 3   H4(inter1, inter2, inter3, record_digest)              cols [98,99,100,186] -> sa.state_commit = 88
```

| component | rows | basis |
|---|---:|---|
| per-row gates + selector binding (14) | 30 | MEASURED (§2) |
| **`state_commit` — 4 × `hash_4_to_1` + the 4 digest pins** | **10,010** | **MEASURED, `npm run cellcommit-native`** |
| **total per effect row (Kimchi rows)** | **≈ 1.00 × 10⁴** | |
| transition + boundary (21 gates), still unemitted | ~45 | PROJECTED, not in the total |
| canonicality range checks (26 cells) | 52 | MEASURED marginal, o1js-side, not in the total |

**The commitment hashing is 99.7% of it** (10,010 of 10,040). The old projection said 98.8%
of ~10,534; it is slightly *more* dominant than projected because the arithmetic core came in
at 30 rows and the projection had allowed ~127 for gates route B does not emit.

**Against the projection: −5% (10,010 measured against 10,402 projected for the four sites).**
The projection multiplied a measured o1js marginal (2,600.5 rows per permutation) by four; the
generated tree comes in under it because it replaces `inputLanes`' 16 range-check rows per
permutation with 4 (the absorbed columns) plus a handful of constant pins.

### 3.1 ⚑ The Lean row count is CONSERVATIVE by exactly 560 rows — a one-line packing decision

| | Lean `commitRowCount` | snarky `Provable.constraintSystem` |
|---|---:|---:|
| generic rows | 6,154 | 5,594 |
| `RangeCheck0` rows | 4,416 | 4,416 |
| **total** | **10,570** | **10,010** |

The emission is 11,188 generic sub-gates and 4,416 range checks. Perfectly packed two-to-a-row,
the generics need `⌈11188/2⌉ = 5,594` rows — which is **exactly** what snarky reports. Lean
reports 560 more because `KimchiLower.renderOpsGo` **flushes a pending generic half-row before
every `rc0`**, and snarky's double-generic packing carries the pending half across the range
check to the next generic sub-gate.

This is a real, provable optimisation and it is NOT a modelling error: the Lean count is an
*upper bound* the deployed circuit beats, which is the safe direction for a cost model. The fix
is to let `renderOpsGo` keep its `pending` across a non-generic op; its correctness statement is
the same `packGen_holds_iff`-shaped one the pure-generic backend already carries. Not done here
— an optimisation whose equivalence is unproved is exactly what `KimchiLower` exists not to do.

### 3.2 Consequences

* **6 effect rows per Pickles step**, not the ~5 the projection gave: `65,536 / 10,040 = 6.5`,
  and on the usable ~55,000 after `zk_rows` and the wrapper it is 5.4. "5 to 6" is the honest
  reading and **6 is the ceiling**. The re-price does not move the geometry — a small turn is
  still one step.
* **Break-even against A is ≈ 2,850 effect rows.** If one dregg proof covers N turns of k
  effects each, B is cheaper while `N·k < 2,850`.
* ⚑ **And B still does NOT scale to a dregg trace.** The 10⁴ is per *semantic* effect row,
  because B checks the SPEC and skips the trace entirely — no memory table, no hash table, no
  padding, none of the other six root tables. If you instead re-emitted dregg's AIR row by row,
  you would pay (trace rows) × (per-row cost), and dregg's root tables run to
  `degree_bits = 15`. **B is cheap only because it is small, and it is small only because it
  checks less.**

### 3.3 The o1js run, for real

```
snarky rows for the commitment binding  : 10010   (Lean predicted 10570, delta -560)
compile                                 : 24.94s
honest cell: prove                      : OK   (24.34s)
honest cell: verify                     : OK   (0.74s)

-- substituted commitment (a valid transition, someone else's commitment)
   arithmetic emission                 : 0 violated — STILL FULLY SATISFIED
   prove()                             : REFUSED
-- swapped authority residue (aux 96 — the fourth GROUP-4 input)
   arithmetic emission                 : 0 violated — STILL FULLY SATISFIED
   prove()                             : REFUSED
-- forged intermediate digest (aux 8 = inter1)
   arithmetic emission                 : 0 violated — STILL FULLY SATISFIED
   prove()                             : REFUSED
```

⚑ **The `0 violated` line on each tamper is the point.** Every one of those three witnesses
satisfies the arithmetic emission completely — they are perfectly valid `incrementNonceA`
transitions. Before the hash sites landed they were **indistinguishable from the honest
instance**, because nothing in the circuit read column 88, aux 96 or aux 8. That is the
separation the binding buys, exhibited against a real `prove()` rather than argued.

---

## 4. ⚑ What makes B untrustworthy, named

This section is worth more than the demo. Every item is a real gap in what landed, not a
future-work wish.

### 4.1 The Kimchi emission covers 14 of the descriptor's 35 constraints (plus all 4 hash sites)

`incNonceHeadsBound` denotes `incNonceRowGates ++ selectorGates 53`. The deployed
`incrementNonceVmDescriptor.constraints` also carries `transitionAll` (14),
`boundaryFirstPins` (4) and `boundaryLastPins` (3). Those 21 are not emitted to Kimchi.
(The descriptor's 4 `hashSites` are a separate field, not part of the 35, and they ARE now
emitted — §4.2.)

`transitionAll` is cross-row (`next[sb+hi] = this[sa+lo]`) and this emission is single-row,
so **the Kimchi circuit checks one row in isolation and nothing chains it to a neighbour.**
A sequence of individually-valid rows is not thereby a valid trace. The boundary PI pins are
what tie a row's nonce to `PI[ACTOR_NONCE]`, also absent.

⚑ *Was worse, and is now fixed:* until `selectorBindHead` landed this section also read "the
circuit never checks that this is an `incrementNonce` row" — it checked the SHAPE and any
effect with that shape passed. `selectorGates 53` is now emitted, `kimchi_forces_selector` is
the theorem, and `tamper wrong selector` in §2 is the exhibit.

### 4.2 The commitment binding LANDED — and here is exactly what it does and does not say

*Until 2026-07-30 this section read "the commitment binding is absent — this is the big one",
and it was right: the emission had none of `incrementNonceVmDescriptor.hashSites`' four GROUP-4
sites, so the circuit proved a relation between two **bare** 13-tuples and did not prove they
were the pre-image of any commitment — did not prove they were a dregg cell at all.*

**What landed.** `metatheory/Dregg2/Circuit/Emit/KimchiCellCommit.lean`. Four `hash_4_to_1`
sub-circuits generated by `KimchiPoseidon2.permGen`, wired by `inColsGo` from the DEPLOYED site
list, each digest pinned into the deployed digest column, site 3 landing on
`saCol state.STATE_COMMIT`. Same two-arrows shape as the arithmetic:

```
cellCommitOf hash a                        -- THE ONE def: the RHS of transferHash_binds verbatim
   ^                                          ^
   |  babybear_forces_cellCommit              |  kimchi_forces_cellCommit
   |                                          |
siteHoldsAll hash env incNonceHashSites    commitRows (10,570 emitted Kimchi rows)
   (ASSUMED by the BabyBear descriptor)       (DERIVED: commit_rows_force_siteHoldsAll)
```

⚑ **The asymmetry runs the same way as §4.7's.** On the BabyBear side `siteHoldsAll` is an
*assumption about the deployed trace*: the descriptor carries `VmHashSite`s whose denotation is
"the digest column holds the hash of these inputs", and **no gate in
`incrementNonceVmDescriptor.constraints` establishes it** — the Poseidon2 chip is outside the
constraint list. On the Kimchi side it is DERIVED, because the emitted circuit contains the
permutation.

**The teeth.** `tamper_non_preimage_refused` is general, not sampled: **no assignment whatever**
satisfies the emitted circuit while carrying a `state_commit` that is not `cellCommitOf hash` of
its own after-state. Three instances of it were refused by a real `prove()` in §3.3, each of
them a *perfectly valid* `incrementNonceA` transition under the arithmetic emission.

**What it still does not say — and this is not a narrowing of §0.** B now checks a *cell*. It
does not check *membership*. Nothing ties `state_commit` to a root dregg's chain published. The
`piBinding` that would (`boundaryLastPins`: `saCol STATE_COMMIT = pi.NEW_COMMIT`) is still
unemitted, and even it would only name a public input the same prover chose. **A well-formed
transition of a cell that never existed passes every row.**

### 4.2a ⚑ The one undischarged leg of the binding: `DigestCarrier`

`kimchi_forces_cellCommit` carries a hypothesis, and it is named rather than folded into a
definition. `DigestCarrier hash A` says: at each of the four emitted permutation sub-circuits, a
satisfying `A` puts `hash` of the absorbed columns in the digest lane. That is
`KimchiPoseidon2`'s own §5 remainder (`permGen_forces`) specialised to four sites, and it is not
proved.

⚠ **It is worse than unproved: at the emitted object it needs repairs before it could be true.**
Three, found while wiring this:

1. **`bbRange64` leaves its two 12-bit COPY columns unpinned.** It allocates them as fresh
   variables holding `0` and emits **no gate** forcing them, so the emitted `RangeCheck0`
   recomposition bounds its value by ~2⁸⁸ rather than 2⁶⁴. Fix: one shared pinned-zero variable,
   one sub-gate for the whole circuit.
2. **`bbReduce`'s remainder carries a TRACKED bound of `2³¹` while the emitted check is the
   64-bit one.** The `2³¹` is load-bearing, not cosmetic: the S-box chain's Pasta safety is
   `35·2³¹ = 2³⁶·¹³` into `x⁷ < 2²⁵³·²`, and at a `2³²` lane it is `2²⁵⁹·⁹ > p_Pasta` — unsound
   rather than slow, which `KimchiPoseidon2`'s own §2 says. A genuine 31-bit check is two
   crumbs-only `RangeCheck0` rows plus a boolean sub-gate, and it costs rows.
3. **The four 12-bit plookup columns are constrained by the lookup ARGUMENT**, which
   `KimchiTarget.holds` models as `False` and no forcing lemma may therefore assume. A real
   statement takes the lookup as a hypothesis, as `rc0PlookupCols`' own docstring says.

What IS established over the emitted object, through the compiler
(`scripts/check-kimchi-cellcommit.sh`, which exits nonzero and is mutation-proved red): every
one of the 10,570 rows is satisfied by the honest cell's witness; each site's digest lane
carries exactly `hash4to1Real` of the columns the deployed site absorbs — i.e.
**`DigestCarrier hash4to1Real` HOLDS at the honest instance**, so the hypothesis demands nothing
an honest cell does not supply; and the last lane is `841295468`, which is `cellCommitOf
hash4to1Real` of that cell, the felt `cell_state.rs::compute_commitment` produces.

⚑ **Where those checks run, and why it is not `#guard`.** The emitted object is 15,604
instructions, 76,489 witness values and 10,570 rows. `#guard` evaluates at ELABORATION time
through `whnf`, which materialises the whole `List KRow` as an expression: measured on hbox, the
module went past 20 GB resident, still climbing, and had to be killed. The same trap took a
`length` lemma into the kernel's "deep recursion detected" — projecting `.1` through the fold
step destructures `h4Gen`'s pair, so `whnf` had to reduce four Poseidon2 permutations to learn a
list's length. Removing it took the module's build from 3 minutes and 21.5 GB to **1.7 s**. The
checks therefore run compiled, in `CheckKimchiCellCommit.lean`, and `EmitKimchiCellCommit`
refuses to write an artifact unless the same `emissionChecksHold` is true.

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

For the four GROUP-4 commitment sites: **yes, in the same shape**, as of 2026-07-30 —
`two_emissions_one_commit` lands both arrows on `cellCommitOf`, the Kimchi side DERIVING the
`siteHoldsAll` the BabyBear side assumes, under one named and exhibited-satisfiable carrier
(§4.2a).

For the rest of the descriptor — the transition continuity and the boundary pins — **there is
no second emission at all yet**, so the question does not arise there and must not be answered
by extension.

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
  blurred. B now says "this is a valid transition **of a real, well-formed cell**" — the
  commitment binding of §4.2 bought the second half of that sentence. A says "dregg proved
  this". A well-formed transition of a cell that never existed passes B and fails A, and the
  commitment binding could not have changed that: hashing a tuple you invented is as easy as
  inventing it.
* **Coverage.** A verifies a proof about all 1,093 constraints of dregg's seven root
  tables, whatever they say, without anyone re-emitting them. B covers exactly what has
  been re-emitted — 14 constraints of 35 plus the 4 commitment sites, of one effect out of
  54 — and every extension is fresh work with a fresh chance to diverge.
* **Independence from the re-emission itself.** A cannot drift from dregg's semantics,
  because it does not restate them. B is a second statement of the same thing, and
  §4.1–§4.2 are what that costs.

---

## 6. Reproduce

```
# Lean — the ARITHMETIC emission
scripts/hbuild <lane> 'cd metatheory && lake build Dregg2.Circuit.Emit.KimchiEffectIncNonce \
    && lake env lean --run EmitKimchiIncNonce.lean'   # > bridge/mina-zkapp/src/generated/kimchi-incnonce-b.json

# Lean — the GROUP-4 COMMITMENT emission, its GATE, and its artifact
scripts/check-kimchi-cellcommit.sh                    # builds, then runs the gate; exits nonzero when red
scripts/hbuild <lane> 'cd metatheory && lake env lean --run EmitKimchiCellCommit.lean' \
    > bridge/mina-zkapp/src/generated/kimchi-cellcommit-b.json

# o1js — compile, prove, verify, tamper
cd bridge/mina-zkapp && npm run incnonce-native       # the 30-row arithmetic core
cd bridge/mina-zkapp && npm run cellcommit-native     # the 10,010-row commitment binding
```

Timings measured 2026-07-30 (hbox lane `kimchi-emit` for Lean, laptop for o1js): module build
1.7 s; gate 4.7 s; emit 7.4 s (2.2 MB artifact); o1js constraint system 4.0 s, compile 24.9 s,
prove 24.3 s, verify 0.74 s, whole `cellcommit-native` run 66 s.

Complete root build (`lake build Dregg2`) ran on hbox lane `kimchi-semb`: VERDICT PASS, 0
errors, floor-ratchet OK (2,103 grandfathered carriers over 34 refuted floors; baseline
2,227, slack 124).
