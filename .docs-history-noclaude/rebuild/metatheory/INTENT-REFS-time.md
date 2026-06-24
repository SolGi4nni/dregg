# INTENT-REFS — Relativistic Time-Typing (causal vs frame)

**Pillar:** the formalism behind *"time SPLITS — there is no global `now`. A deadline is either a
**lightcone fact** on the lace (`causal_after(E)`, frame-invariant, internal, provable) or a **frame
convention** (`frame_within(authority, T, ±δ)`, an attested predicate carrying an explicit skew bound)."*
**Companion to:** [`INTENT-AS-CO-RECEIPT.md`](./INTENT-AS-CO-RECEIPT.md) §4 (the relativistic time-typing
innovation; this doc grounds it).
**Siblings:** [`INTENT-REFS-resources.md`](./INTENT-REFS-resources.md) (the resource face),
[`INTENT-REFS-optics.md`](./INTENT-REFS-optics.md) (the solver/optic face),
[`EXTERNAL-LEAN-REFERENCES.md`](./EXTERNAL-LEAN-REFERENCES.md) (the Lean-library landscape).
**Research date:** 2026-06-03. Status: reference map + a Lean formalization recommendation, not a spec.

> The one sentence: **causal order is the only frame-invariant time** (Lamport 1978), it **literally IS a
> discrete causal set** (Bombelli–Lee–Meyer–Sorkin 1987), a **consistent cut is a spacelike
> hypersurface** (Mattern 1989), and wall-clock time is **irreducibly an interval `[earliest, latest]`
> with bounded uncertainty `ε`/`δ`, never a point** (Spanner/TrueTime 2012) computed by a **fault-tolerant
> approximate-agreement protocol** (Lamport–Melliar-Smith 1985 / Dolev–Halpern–Strong 1986). §4's
> `causal_after` / `frame_within(F,T,±δ)` split is not an aesthetic — it is what every one of these sources
> says you are *forced* to do.

---

## TL;DR ranking

| # | Reference | Gives us | §4 hook |
|---|---|---|---|
| **1** | **Lamport, *Time, Clocks, and the Ordering of Events*** (CACM 1978) | happens-before `→` = the causal partial order = the only frame-invariant "time"; *invariant clock condition*; the impossibility of a meaningful global total order without an external frame | THE anchor for `causal_after`; the *reason* §4 refuses `expiry: u64` |
| **2** | **Bombelli–Lee–Meyer–Sorkin, *Space-time as a causal set*** (PRL 1987) | spacetime ITSELF is a discrete partial order; causal-interval "volume" = element **count** | grounds "a blocklace IS a causal set; **lace-depth = causal-interval cardinality**" |
| **3** | **Mattern, *Virtual Time and Global States*** (1989) | vector clocks (`a → b ⇔ V(a) < V(b)`); a **consistent cut = a spacelike hypersurface** = a candidate "now" | per-cell proper time = the cell's vector-clock coordinate; "choosing a simultaneity surface" made precise |
| **4** | **Spanner / TrueTime** (Corbett et al., OSDI 2012) | wall-clock time as an **interval `[earliest, latest]`, uncertainty `ε`**, never a point; `commit-wait` makes external consistency *causal* by paying out `2ε` | the engineering proof that `frame_within` must **carry δ explicitly, never assume it 0**; commit-wait = "buy a causal guarantee with skew" |
| **5** | **Lamport–Melliar-Smith, *Synchronizing Clocks in the Presence of Faults*** (JACM 1985) | interactive-convergence / interactive-consistency: `f`-fault-tolerant **approximate common frame within bounded skew** | this IS the `frame_within(authority, ±δ)` *issuer*: the time-authority is a fault-tolerant clock-sync quorum |
| **6** | **Dolev–Halpern–Strong, *On the possibility and impossibility of clock synchronization*** (JCSS 1986) | the **bounds**: synchronization to within any skew is *impossible* with `n ≤ 3f` (unauthenticated); possible (any skew) with signed messages for any `n>f` | the honest §8 trust-assumption ledger: *how many faults* the frame-authority survives, and that unforgeable signatures buy the bound — exactly our credential model |
| **7** | **Kulkarni–Demirbas–Madappa–Avva–Leone, *Logical Physical Clocks (HLC)*** (OPODIS 2014) | one 64-bit timestamp that is **causal AND within bounded physical drift `ε`** of NTP; `l` (logical) ≥ `pt`, `c` breaks ties | the *practical unification* object: HLC = "carry causal order + a bounded-skew frame reading in one stamp" — the concrete shape of a §4 receipt's time field |
| **8** | **Einstein, *On the Electrodynamics of Moving Bodies*** (1905) | relativity of simultaneity — the physics root: "simultaneous" is frame-relative | the physical *why* there is no global `now`; cite once, in the motivating paragraph |

PDFs pulled this session (validated `%PDF`, in `/Users/ember/dev/breadstuffs/pdfs/`): #1, #3, #4, #5, #7,
and the open Sorkin causal-set review that subsumes #2. See the [PDFs pulled](#pdfs-pulled-this-session)
table at the bottom.

---

## 1. Lamport — *Time, Clocks, and the Ordering of Events in a Distributed System* — **THE anchor**

- **Author / year / venue:** Leslie Lamport, *Communications of the ACM* **21**(7):558–565, July 1978.
  (Turing-Award-cited; the founding paper of distributed time.)
- **PDF:** `lamport-time-clocks-ordering-1978.pdf` `[PULLED]` (Lamport's own MSR copy,
  `lamport.azurewebsites.net/pubs/time-clocks.pdf`). DOI `10.1145/359545.359563`.
- **What it gives us + map onto §4.** The "happens-before" relation `→` — the smallest transitive
  relation with: same-process events are ordered, and `send → receive` — is a **partial order**, and
  Lamport's decisive argument is that **this causal order is the only ordering of events that is
  *intrinsic* to the system** (independent of any clock or observer). Events with neither `a → b` nor
  `b → a` are **concurrent** — there is *no fact of the matter* about their order without imposing an
  external frame. He then closes with the **explicit relativity analogy** (§"Physical Clocks", final
  pages): the causal partial order is the **invariant content** of relativistic spacetime; a *total*
  order requires choosing a frame (his "physical clocks" + the *Clock Condition* `a → b ⇒ C(a) < C(b)`)
  and is therefore *conventional*, not intrinsic. This is the entire spine of §4:
  - **`causal_after(E)` = `E → (this event)` in Lamport's `→`.** A lightcone fact, frame-invariant,
    needs no trust — *exactly* his happens-before. Our lace's `precedes`/`≺` (`Authority/Blocklace.lean`)
    is a concrete, content-addressed `→`.
  - **Why `expiry: u64` is a fiction (§4, §6 item 1).** A raw timestamp deadline asks "did `a` happen
    before clock-tick `T`?" — but `T` lives in *some frame's physical clock*, and comparing it to a
    distributed event presupposes the global simultaneity Lamport proves does not intrinsically exist.
    The honest replacement is *either* a causal predicate (`causal_after`) *or* an explicitly-framed one
    (`frame_within`), never a bare `u64`.
  - **Anti-frontrunning = a causal constraint (§4, §5).** "No one may fill before I reveal" is `reveal →
    fill`, a happens-before fact on the lace — *provably* enforced, not a timestamp gamble. MEV-as-
    control-of-the-simultaneity-surface (§5) is the precise dual: there is no intrinsic total order to
    capture, so a class of MEV is structurally impossible.
- **Read:** the whole paper is 8 pages; §"The Partial Ordering" + §"Physical Clocks" are load-bearing.
- **Lean status.** We already *have* Lamport's `→`: `Blocklace.precedes` is the transitive closure of the
  ack relation `pointed` (`a ← b`), with `incomparable` = his concurrency `∥`. The monotonicity facts
  we need for `causal_after` are proved (`Blocklace.attested_mono`, the `precedes` order). **No new
  theory** — `causal_after` is a thin definition over the existing `precedes`.

## 2. Bombelli, Lee, Meyer, Sorkin — *Space-time as a causal set* — **the causal-set grounding**

- **Authors / year / venue:** Luca Bombelli, Joohan Lee, David Meyer, Rafael D. Sorkin, *Physical Review
  Letters* **59**(5):521–524, 1987. DOI `10.1103/PhysRevLett.59.521`. (The PRL is paywalled and 4 pages;
  the **open** companion we pulled is Sorkin's review, which states and develops the same content.)
- **PDF (open companion):** `sorkin-causal-sets-discrete-gravity-grqc0309009.pdf` `[PULLED]` — Sorkin,
  *Causal Sets: Discrete Gravity* (Valdivia lectures, arXiv `gr-qc/0309009`, 2003): the canonical OA
  exposition of the 1987 program.
- **What it gives us + map onto §4.** The causal-set thesis: **spacetime is, fundamentally, a discrete
  set with a partial order `≺` (causality) — "Order + Number = Geometry."** Two facts transfer verbatim:
  - **The partial order IS the causal structure** — `x ≺ y` means "`x` is in the causal past of `y`",
    i.e. a signal *could* go from `x` to `y`. This is *definitionally* our `Blocklace.precedes`: a block
    `a ≺ b` iff `b` (transitively) acks `a`, i.e. `a` is in `b`'s causal past. **A blocklace IS a causal
    set.** (The byzantine-repelling fork-detection of `Blocklace.equivocation_detectable` is then a
    statement *about the causal set's order* — two `≺`-incomparable same-author blocks.)
  - **Volume = count (the central discreteness slogan).** In causal-set theory the spacetime *volume* of
    a causal interval (an "Alexandrov set" `{z : x ≺ z ≺ y}`) is, up to a Planck constant, the **number
    of elements it contains** — continuum geometry is recovered by *counting*. This grounds §4's
    "**lace-depth = causal-interval cardinality**": the "amount of causal time" between two events is the
    *count of lace elements causally between them*, a frame-invariant integer, never a wall-clock
    duration. (Cordial-Miners' `rounds` = DAG depth, `Proof/CordialMiners.lean`, is exactly such a count.)
- **Read:** Sorkin review §1–§3 (the order ≅ causal structure; the volume-as-count "fundamental
  theorem"); the 1987 PRL itself if you want the original 4-page statement.
- **Lean status.** The "interval cardinality as causal duration" is a *new, small* definition worth
  adding: `laceDepth B a b := #{z ∈ B | precedes B a z ∧ precedes B z b}` (a `Finset.card` over the
  Alexandrov interval), with a monotonicity lemma (`a ≺ a' ⇒` interval shrinks) as the keystone. It
  reuses the existing `precedes`; it is the formal content of "causal time is counted, not clocked."

## 3. Mattern — *Virtual Time and Global States of Distributed Systems* — **consistent cut = spacelike surface**

- **Author / year / venue:** Friedemann Mattern, in *Parallel and Distributed Algorithms* (Cosnard et
  al., eds.), North-Holland, 1989, pp. 215–226. (Independently with Fidge; the canonical **vector
  clock** paper.)
- **PDF:** `mattern-virtual-time-global-states-1989.pdf` `[PULLED]` (ETH VS copy; metadata title/subject
  confirm "Virtual Time and Global States… / vector clocks").
- **What it gives us + map onto §4.** Mattern builds the **vector clock** `V` with the *characterization*
  `a → b ⇔ V(a) < V(b)` (componentwise; `‖` iff incomparable) — i.e. vector time **is exactly** Lamport's
  causal order, now *faithfully* represented (a scalar Lamport clock only gives one direction). Then the
  pivotal geometric move:
  - **A consistent cut = a spacelike hypersurface = a candidate "now".** A *cut* assigns each process a
    local state; it is **consistent** iff it is *closed downward under `→`* (if `b` is in the cut and
    `a → b`, then `a` is too — no message received before it was sent crosses the surface). Mattern draws
    this *literally* as a **relativistic spacelike surface** through the space-time diagram: a consistent
    cut is a set of pairwise-concurrent events, one "simultaneity surface" — and the snapshot/global-state
    problem (Chandy–Lamport) is *choosing* one. This is §4's **per-cell proper time** and "comparing two
    cells' proper times requires choosing a simultaneity surface", made exact:
    - **per-cell proper time** = a cell's *own* vector-clock component (its worldline coordinate; advances
      monotonically along the cell's receipt chain — our `RecChainedState` index / `log.length`);
    - **a "now" across cells** = a *consistent cut* = a *frame* (a spacelike surface). There are many;
      none is canonical — which is precisely why a global `block_height` (§4, §6) is a frame convention.
  - **Distributed snapshot ↔ simultaneity-surface correspondence** is the operational content of "there
    is no global now, only chosen consistent cuts." A `frame_within` predicate is, geometrically, an
    *assertion that an event lies below a particular chosen spacelike surface*.
- **Read:** the vector-clock construction + the "consistent cut as a spacelike surface" figure and its
  discussion (the heart of the paper, ~pp. 218–223).
- **Lean status.** Per-cell proper time is *already there*: the living cell's trajectory index in
  `Proof/Temporal.lean` (`trajA … n`) and the monotone `log.length` (`always_logMono`) ARE a cell's
  worldline proper-time, with monotonicity **proved**. A vector-clock / consistent-cut layer is a future
  add (only needed when we compare *two* cells' times — i.e. cross-cell `JointTurn` time).

## 4. Corbett et al. — *Spanner: Google's Globally-Distributed Database* (TrueTime) — **carry δ, never assume 0**

- **Authors / year / venue:** James C. Corbett, Jeffrey Dean, Michael Epstein, … Wilson Hsieh et al.,
  *OSDI 2012* (10th USENIX Symp. on Operating Systems Design and Implementation), pp. 251–264; journal
  version *ACM TOCS* 31(3), 2013.
- **PDF:** `spanner-truetime-osdi2012.pdf` `[PULLED]` (Google Research archive copy).
- **What it gives us + map onto §4.** Spanner's **TrueTime** API is the engineering vindication of "carry
  δ explicitly": `TT.now()` returns **not a timestamp but an interval `[earliest, latest]`** with bounded
  uncertainty `ε = (latest − earliest)/2` (typically ~1–7 ms, backed by GPS + atomic clocks). Time is
  *never a point*; the system *knows it does not know* the exact instant. Two consequences are §4 verbatim:
  - **`frame_within(authority, T, ±δ)` IS `TT.now()`.** The "time authority" is TrueTime's clock fleet;
    `δ` is `ε`; the attested predicate "`T` lies within the frame's bound" is "`T ∈ [earliest, latest]`".
    Terrestrially `δ ≈ ms` and fine — but the model *carries it* and refuses to collapse the interval.
  - **commit-wait = buying a *causal* guarantee with skew.** To make commit order match real-time order
    ("external consistency"), Spanner assigns a commit timestamp `s` then **waits until `TT.after(s)` is
    true** — i.e. waits out `2ε` so that *no later transaction's interval can overlap*. This is the
    sharpest possible statement of the §4 duality: **a frame predicate (`frame_within`) is *converted into*
    a causal fact (`causal_after`) by paying `δ` of real waiting.** Our `frame_within` ⊃ `causal_after`
    bridge is Spanner's commit-wait. (And it is *why* a lending deadline that must be causally final, not
    just clock-stamped, costs skew.)
- **Read:** §3 (TrueTime API + the `ε` interval) and §4.1.2 (commit-wait / external consistency). Short
  and decisive.
- **Lean status.** This is the *shape* for `frame_within`: a predicate `frameWithin (auth) (T : Time)
  (δ : Time)` over an issuer's attested interval, with the **bridge lemma** `frameWithin auth T δ ∧
  waited(2δ) → causalAfter …` as the commit-wait keystone. The `δ` is a first-class field, never erased.

## 5. Lamport & Melliar-Smith — *Synchronizing Clocks in the Presence of Faults* — **the frame issuer**

- **Authors / year / venue:** Leslie Lamport & P. M. Melliar-Smith, *Journal of the ACM* **32**(1):52–78,
  1985 (preliminary version PODC 1984). DOI `10.1145/2455.2457`.
- **PDF:** `lamport-melliarsmith-synchronizing-clocks-faults-1985.pdf` `[PULLED]` (Lamport's MSR copy).
- **What it gives us + map onto §4.** The foundational *algorithms* for `f`-fault-tolerant clock
  synchronization: **Interactive Convergence (CNV)** and **Interactive Consistency (COM/CSM)**. Each lets
  `n` clocks, up to `f` of them arbitrarily Byzantine (lying, two-faced), **converge to within a bounded
  skew `δ` of a common frame**, given `n ≥ 3f + 1`. This is *literally* §4's
  `frame_within(authority, ±δ)` **issuer**: "Byzantine clock-sync is *nodes computing an approximate
  common frame within bounded skew*" (§4, verbatim). The "time authority" is **not** a single trusted
  oracle — it is a **quorum running CNV/COM**, whose output is an attested clock value *with* a proven
  worst-case skew `δ`. What is *provable* (and what we can carry as a Lean law if we model the protocol):
  **agreement within `δ`** (two correct clocks differ by `≤ δ`) and **accuracy** (the synchronized clock
  tracks real time within a rate bound). What stays a **§8 trust-assumption**: that *at most `f`* of the
  authority's clocks are faulty, and that the messages are authentic.
- **Read:** §2–§3 (the fault model + CNV), and the bound `n ≥ 3f+1` with its skew analysis.
- **Lean status.** This is the model behind a `TimeAuthority` credential issuer: its attestation stream
  carries proven *monotonicity* + *bounded skew* (provable from the convergence law) but rests on an
  honest-majority §8 assumption (≤ `f` faulty). The natural Lean shape reuses
  `Authority.Credential` (issuer + attestation + revocation) with the *issuer* being a clock-sync quorum
  and the *claim* being a framed interval.

## 6. Dolev, Halpern, Strong — *On the Possibility and Impossibility of Achieving Clock Synchronization* — **the bounds + the signature lever**

- **Authors / year / venue:** Danny Dolev, Joseph Y. Halpern, H. Raymond Strong, *Journal of Computer and
  System Sciences* **32**(2):230–250, 1986 (preliminary STOC 1984). DOI `10.1016/0022-0000(86)90028-0`.
- **PDF:** not pulled here (JCSS, paywalled; OA preprints exist via the authors' pages / STOC'84). Cited
  as the **bounds** complement to #5.
- **What it gives us + map onto §4.** The matching *impossibility/possibility* frontier — the honest
  trust-assumption ledger for a frame authority:
  - **Impossibility:** with **arbitrary (Byzantine) faults and *unauthenticated* messages**, clock
    synchronization to *any* bounded skew is **impossible unless `n > 3f`** (fewer than a third faulty) —
    the clock-sync analogue of the BFT one-third bound.
  - **Possibility with signatures:** if messages are **authenticated (unforgeable signatures)**,
    synchronization to a bounded skew is achievable for **any `n > f`**. *Signing buys the bound.*
  - This is *exactly* dregg's posture: the frame-authority's attestations are **signed credentials**
    (`Authority.Credential` / `ThirdPartyDischarge`), so the relevant regime is the authenticated one —
    `frame_within` survives Byzantine clocks *because* the reading is a verifiable attestation, and the
    honest §8 line we must declare is precisely *"≤ f of the time-quorum are faulty"* and *"signatures
    unforgeable"* (the latter already our standing §8 crypto seam).
- **Read:** the impossibility theorem (`n ≤ 3f`, unauthenticated) and the authenticated-possibility
  result (`n > f`).
- **Lean status.** Not modeled; it is the **§8 trust-assumption text** for the time-authority — name it
  in the "what's a portal, not a theorem" section so the `frame_within` issuer's fault tolerance is
  honest rather than hand-waved.

## 7. Kulkarni, Demirbas, Madappa, Avva, Leone — *Logical Physical Clocks (HLC)* — **the practical unification object**

- **Authors / year / venue:** Sandeep S. Kulkarni, Murat Demirbas, Deepak Madappa, Bharadwaj Avva,
  Marcelo Leone, *OPODIS 2014* (Principles of Distributed Systems), LNCS 8878, pp. 17–32. arXiv preprint
  `1407.3561` (titled *Logical Physical Clocks and Consistent Snapshots in Globally Distributed
  Databases*).
- **PDF:** `hybrid-logical-clocks-2014.pdf` `[PULLED]` (arXiv `1407.3561`).
- **What it gives us + map onto §4.** **HLC** is the single object that **does the §4 split inside one
  64-bit timestamp**: it combines a *logical* component `l` (which dominates physical time, `l ≥ pt`,
  capturing **causality** — `e hb f ⇒ HLC(e) < HLC(f)`) with a tie-break counter `c`, and stays **within a
  bounded `ε` of the NTP physical clock** (`|l − pt| ≤ ε`). So a single HLC stamp simultaneously gives you
  (a) the **causal order** (use it like a Lamport/vector clock for happens-before) and (b) a **physical
  reading within bounded skew** (use it as a wall-clock approximation). This is the *concrete data shape*
  for a §4 receipt's time field: **carry both a causal coordinate and a bounded-skew frame reading,
  unified** — `causal_after` reads the `l`/`c` (logical) part, `frame_within(±δ=ε)` reads the `pt` part.
  HLC is backward-compatible with NTP's 64-bit `timestamp`, which is why it is *deployable* (it underpins
  CockroachDB, MongoDB) — the pragmatic answer to "how do you actually store a §4 time?".
- **Read:** §III (the HLC algorithm + the `l`/`c` update rules) and the bounded-drift theorem.
- **Lean status.** The cleanest *carrier type* for a unified time field: `structure HLC where logical :
  Nat; counter : Nat; physical : Nat` with the invariant `logical ≥ physical` and a `≤`-order that
  refines `precedes` (causal) while exposing `physical ± ε` (frame). Optional but high-leverage if/when a
  receipt needs *one* time stamp instead of two predicates.

## 8. Einstein — *On the Electrodynamics of Moving Bodies* — **the physics root (cite once)**

- **Author / year / venue:** Albert Einstein, *Annalen der Physik* **17**:891–921, 1905 (the special-
  relativity paper). English translations OA (e.g. via Fourmilab / `einsteinpapers.press.princeton.edu`).
- **What it gives us + map onto §4.** §1 (*Definition of Simultaneity*) is the physical root of the whole
  doc: **simultaneity is frame-relative** — two events simultaneous in one inertial frame are *not* in
  another. This is *why* there is no global `now` and *why* a `block_height` / `expiry: u64` presupposes a
  surface that does not exist. Cite once, in §4's motivating paragraph, as the ground truth that Lamport
  (#1) imported into distributed systems and Mattern (#3) drew as the spacelike cut. Not a formalization
  target — the *reason* the formalization is shaped the way it is.

---

## How to formalize the two deadline types in Lean — recommendation

The headline: **`causal_after` is nearly free** (it is a thin predicate over the *already-proved*
`Blocklace.precedes` partial order), and **`frame_within(F, T, ±δ)` is a `WitnessedPredicate` carrying
`δ` over a time-authority credential issuer** (reusing `Authority.Predicate` + `Authority.Credential` +
`Authority.ThirdPartyDischarge`). The split is *syntactic*: a `Deadline` is a sum type whose two
constructors force the author to declare which kind of promise was made — so the relativistic honesty is
load-bearing, exactly as §4 demands.

### What already exists (REUSE — do not rebuild)

| §4 concept | Existing Lean object | File | Status |
|---|---|---|---|
| `causal_after(E)` (lightcone fact) | `Blocklace.precedes` (`≺`, transitive closure of ack `←`), `incomparable` = concurrency `∥` | `Dregg2/Authority/Blocklace.lean` | **PROVED** order; `attested_mono` (finality never regresses) |
| causal monotonicity along a worldline | `Proof/Temporal.always_logMono` (`□`(log never shrinks)), `always_revoked_persists` (`□`(once revoked, always)) | `Dregg2/Proof/Temporal.lean` | **PROVED** on the real 46-effect executor |
| per-cell **proper time** | living-cell trajectory index `trajA … n` + monotone `log.length` (the cell's worldline coordinate) | `Dregg2/Proof/Temporal.lean` | **PROVED** monotone |
| `frame_within` as an attested predicate | `Authority.Predicate` registry (`WitnessedKind`, `Verifiable`, `registry_sound`) — a `Temporal` kind already exists | `Dregg2/Authority/Predicate.lean` | **PROVED** soundness-by-verification |
| the frame **issuer** (a time authority) | `Authority.Credential` (issuer + `attestation : Proof` + revocation) | `Dregg2/Authority/Credential.lean` | **PROVED** verify-iff-issued-and-not-revoked |
| third-party freshness / skew window | `ThirdParty` discharge with `MAX_DISCHARGE_AGE = 300` freshness gate | `Dregg2/Authority/ThirdPartyDischarge.lean` | the *current raw wall-clock check* — the thing §4 retypes |
| causal-set **count** (lace-depth) | Cordial-Miners `rounds` (DAG depth) | `Dregg2/Proof/CordialMiners.lean` | **PROVED** structure |

> Note the live tension `ThirdPartyDischarge.lean` already encodes: `0 ≤ now − created_at ≤ 300` is a
> **bare wall-clock freshness check** — a `frame_within` *without* a declared `δ` and *without* a
> declared frame. §4's discipline is to **retype it** as a `frame_within(time-authority, created_at,
> ±δ=300)` so the skew is explicit and the authority named. This is the single most concrete
> "before/after §4" example in the codebase.

### The deadline type (the syntactic forcing)

```lean
/-- A §4 deadline FORCES the causal-vs-frame distinction at the type level. -/
inductive Deadline (B : Lace) (Time : Type) where
  /-- A LIGHTCONE FACT: "this event must causally follow `E`." Frame-invariant, on the lace,
      NO trust. Discharged by `Blocklace.precedes B E ·`. -/
  | causalAfter (E : Block) : Deadline B Time
  /-- A FRAME CONVENTION: "the time-authority `F` attests `T` within skew ±δ." An attested
      predicate carrying δ EXPLICITLY; discharged by a verified credential from `F`, NEVER δ=0. -/
  | frameWithin (F : TimeAuthority) (T : Time) (δ : Time) : Deadline B Time
```

A `Deadline` *cannot be written* without choosing a constructor — so "a court can always tell which kind
of promise was made" (§4) is a type-checker fact, not documentation.

### `causal_after` — the lightcone face (provable, no trust)

- **Definition:** `causalAfter B E e := Blocklace.precedes B E e` (the event `e` observes `E`; `E` is in
  `e`'s causal past). Anti-frontrunning's "no fill before reveal" is `causalAfter B revealBlock fillBlock`.
- **What's provable (reuse the existing order):**
  - *frame-invariance* — `precedes` is defined with no reference to any clock/frame (already so);
  - *monotone / append-only* — `attested_mono` and the `precedes` transitivity give "a causal deadline,
    once met, stays met" (a `□` via `Temporal.always_of_step_invariant`);
  - *frontrunning-exclusion* — a fill block that does NOT have `revealBlock` in its causal past is
    `incomparable` or earlier, and the gate rejects it: a *theorem*, not a timestamp race.
- **New work:** ~one definition + 2–3 lemmas, all over the existing `precedes`. The optional causal-set
  **`laceDepth`** (Alexandrov-interval `Finset.card`, ref #2) gives "causal duration = count."

### `frame_within(F, T, ±δ)` — the frame face (attested predicate, honest §8 trust)

- **Definition:** a `frameWithin` deadline is discharged iff a **credential from the time-authority `F`**
  verifies (via `Authority.Credential.verify` — issued ∧ not-revoked) AND its attested interval contains
  `T` within `δ`: i.e. a `WitnessedPredicate` of kind `Temporal` (the kind already in the
  `Authority.Predicate` registry) whose statement is `(T, δ, F-root)` and whose witness is `F`'s signed
  reading. `registry_sound` gives soundness-by-verification for free.
- **What's provable:**
  - *soundness-by-verification* — an accepted attestation discharges the framed predicate
    (`registry_sound` / `crypto_kind_routes_to_oracle`), already proved;
  - *bounded-skew agreement* — IF we model the clock-sync protocol (ref #5), the convergence law gives
    "two correct readings differ by ≤ δ" as a Lean lemma; *monotonicity* of the authority's stream
    (timestamps non-decreasing) is provable like `always_logMono`;
  - *the commit-wait bridge (ref #4)* — `frameWithin F T δ ∧ waited(2δ) → causalAfter …`: converting a
    frame predicate into a lightcone fact by paying `δ`. This is the one genuinely new keystone worth
    proving, and it *unifies* the two deadline kinds (Spanner's external consistency, in Lean).
- **What stays an honest §8 trust-assumption (NOT a Lean theorem):**
  - **the authority is honest** — that ≤ `f` of the time-quorum are Byzantine (refs #5, #6). This is the
    *exact* analogue of the BFT honest-majority and the `CryptoKernel`/`cryptoSound` portals: declare it
    in §8, never fake it as proved.
  - **the skew bound `δ` is real** — that `F`'s clocks actually converge to within `δ` (refs #5, #6);
    Lean proves the protocol *implies* `δ`-agreement *given* the fault bound, but the fault bound itself
    is the assumption.
  - **signatures unforgeable** — already our standing §8 crypto seam (ref #6 shows this is *exactly* what
    buys the synchronization bound for `n > f`).

### Summary of provable vs portal

| Property | Provable in Lean? | Where / how |
|---|---|---|
| `causal_after` is frame-invariant & a partial order | **YES** | `Blocklace.precedes` (already proved) |
| causal deadline, once met, stays met (`□`) | **YES** | `Temporal.always_of_step_invariant` + `attested_mono` |
| frontrunning-exclusion (causal reveal-order) | **YES** | `incomparable` / `precedes` gate (§4, §7 auction proof (b)) |
| per-cell proper time is monotone | **YES** | `Temporal.always_logMono` (worldline `log.length`) |
| `frame_within` soundness-by-verification | **YES** | `Predicate.registry_sound` (kind `Temporal`) |
| frame reading monotone / non-decreasing | **YES** | same shape as `always_logMono` |
| bounded-skew agreement (`δ`) of two correct readings | **YES, given the fault bound** | model CNV/COM (ref #5) → convergence lemma |
| commit-wait bridge `frame ∧ wait(2δ) → causal` | **YES (new keystone)** | the Spanner external-consistency lemma (ref #4) |
| **the time-authority is honest (≤ f faulty)** | **NO — §8 portal** | the honest trust-assumption (refs #5, #6) |
| **the skew `δ` is physically real** | **NO — §8 portal** | clock-drift assumption (refs #4, #6) |
| **signatures unforgeable** | **NO — §8 portal** | standing `CryptoKernel`/`cryptoSound` seam (ref #6) |

**Net:** the causal half of §4 is essentially *already proved infrastructure* (the lace IS a causal set);
the frame half is *built from existing credential/predicate machinery* with the trust narrowed to a
single, named, well-understood assumption (an honest fault-bounded clock authority), exactly as the BFT
and crypto portals already are. The deadline sum type makes the distinction un-skippable, and the
commit-wait bridge is the one new theorem that ties the two faces together (and is the formal content of
"anti-frontrunning is a causal type, not a timestamp race").

---

## PDFs pulled this session (validated `%PDF`, in `/Users/ember/dev/breadstuffs/pdfs/`)

| File | Source | Ref | Role |
|---|---|---|---|
| `lamport-time-clocks-ordering-1978.pdf` | Lamport MSR (`time-clocks.pdf`) | #1 | happens-before = the only frame-invariant time (THE anchor) |
| `sorkin-causal-sets-discrete-gravity-grqc0309009.pdf` | arXiv `gr-qc/0309009` (open companion to PRL 1987) | #2 | spacetime = a causal set; volume = element count |
| `mattern-virtual-time-global-states-1989.pdf` | ETH VS copy | #3 | vector clocks; consistent cut = spacelike hypersurface |
| `spanner-truetime-osdi2012.pdf` | Google Research archive | #4 | time as interval `[earliest,latest]` ± ε; commit-wait |
| `lamport-melliarsmith-synchronizing-clocks-faults-1985.pdf` | Lamport MSR (`clocks.pdf`) | #5 | f-fault-tolerant approximate common frame (the issuer) |
| `hybrid-logical-clocks-2014.pdf` | arXiv `1407.3561` | #7 | HLC = causal + bounded-skew in one stamp |

**Not pulled (paywalled / OA-elsewhere):** Bombelli–Lee–Meyer–Sorkin PRL 1987 (#2 — paywalled 4-pager;
the open Sorkin review covers it); Dolev–Halpern–Strong JCSS 1986 (#6 — paywalled; OA preprints via STOC
'84 / authors' pages); Einstein 1905 (#8 — translations OA, not a formalization target).
