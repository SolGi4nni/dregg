# Candidate: SOUND AGM — reduce t-SDH to q-DLOG (Fuchsbauer–Kiltz–Loss)

**Status:** local scratch, nothing filed/pushed. Mechanized against a fresh scratch copy of
ArkLib @ `d72f8392` (`/private/tmp/arklib-agmsound`, Lean `v4.31.0`). Companion artifact:
`AgmSound.lean` in this directory (compiles clean, `sorry`-free, axiom-clean —
`[propext, Classical.choice, Quot.sound]`).

**Model:** AGM (algebraic group model), reducing to q-DLOG.

**One-line verdict:** the AGM restriction does **not** produce a self-contained uninhabitable
statement, and it gives **no number**. What it *does* give — soundly and mechanizably — is a
tight reduction **t-SDH(algebraic) → q-DLOG**. It relocates the hardness onto q-DLOG; it does
not eliminate it. The honest place a *number* or an *uninhabitable* statement can live is the
q-DLOG floor under a generic-group (GGM) or resource-bounded class — not the representation
field. This confirms, mechanically, the hard-won insight that naïve AGM does not close the hole.

---

## 1. The two forms, and why the naïve one is still dead

### 1a. AGM as a *bounded assumption* — STILL FALSE below 1 (mechanized, `AgmSound.lean` Part 2)

The naïve AGM move is: give the adversary an extra output — a coefficient vector
`a = (a₀,…,a_D) ∈ (ZMod p)^(D+1)` — and add the **representation-validity** obligation

```
h = ∏ᵢ (srs.1[i]) ^ (aᵢ).val          -- i.e. h = g₁ ^ a(τ),  a(X) = Σ aᵢ Xⁱ
```

then state `tSdhAgmAssumption D error := ∀ algebraic adversary, Pr[win ∧ ReprValid] ≤ error`.

**This is still false for every `error < 1`.** `Classical.choice` inhabits a full algebraic
winner: it reads `g₂^τ` from the verifier leg, recovers `τ` (the same `dlogOf` used in
`KzgVacuity.not_tSdhAssumption`), outputs `c = 0`, `h = g₁^((1/τ).val)`, **and** the coefficient
vector `a = (1/τ, 0, …, 0)`. That vector is a *genuinely valid* representation of `h` — only the
`i = 0` factor is nontrivial, and it reconstructs `g₁^((1/τ).val) = h`. The representation is
**free data** the choice-adversary supplies at no cost.

`AgmSound.lean` mechanizes exactly this new obligation, `sorry`-free:

```lean
def ReprValid {D} (srs1 : Vector G₁ (D+1)) (h : G₁) (a : Fin (D+1) → ZMod p) : Prop :=
  h = ∏ i, (srs1[i]) ^ (a i).val

theorem repr_valid_of_extraction (D : ℕ) (τ : ZMod p) :
    ReprValid (Groups.PowerSrs.tower g₁ τ D) (g₁ ^ ((1 / τ).val))
      (fun i => if i = 0 then 1 / τ else 0)
```

Since the representation predicate is an *extra conjunct* that the trapdoor-extracting
adversary satisfies identically, the existing `tSdhExperiment_tauExtractingAdversary = 1` proof
carries over unchanged: the AGM game is won with probability 1, and the bounded assumption is
refuted below 1 by the *same* attack. **So the assumption form is BROKEN — a judge can still
inhabit it.** This is not a defect of our encoding; it is the theorem that naïve AGM ≠ a fix.

### 1b. AGM as a *reduction* — SOUND, and this is the real content (mechanized, Part 1)

The correct AGM statement is not a bounded `Prop`; it is a **construction + inequality**:

> For every algebraic t-SDH adversary `A`, the explicit reduction `B := reduction A` is a
> q-DLOG adversary with `Adv_qDLOG(B) ≥ Adv_tSDH^AGM(A)` (tight — no advantage loss).

The reduction receives a q-DLOG challenge `(g, g^x, …, g^(x^D))`, forwards it verbatim as the
t-SDH SRS (so `τ = x`), runs `A`, and on a winning `(c, h, a)` forms

```
P(X) := a(X)·(X + c) − 1.
```

Because winning means `h = g₁^(1/(τ+c))` and validity means `h = g₁^(a(τ))`, in the
prime-order exponent we get `a(τ)·(τ + c) = 1`, hence `P(τ) = 0`. And `P` is a **nonzero**
polynomial of degree `≤ D+1` (were `P = 0`, then `a·(X+c) = 1`, impossible on degrees). So `τ`
is a root of a known nonzero low-degree polynomial; the reduction factors `P` (≤ `D+1` roots),
tests each against the q-DLOG instance, and returns `τ = x`. This is the FKL core, mechanized
`sorry`-free:

```lean
noncomputable def extractPoly (a : (ZMod p)[X]) (c : ZMod p) : (ZMod p)[X] := a * (X + C c) - 1

theorem extractPoly_root_and_ne_zero
    (a : (ZMod p)[X]) (τ c : ZMod p) (hwin : a.eval τ * (τ + c) = 1) :
    (extractPoly a c).eval τ = 0 ∧ extractPoly a c ≠ 0
      ∧ (extractPoly a c).natDegree ≤ a.natDegree + 1

theorem tau_mem_roots (a : (ZMod p)[X]) (τ c : ZMod p) (hwin : a.eval τ * (τ + c) = 1) :
    τ ∈ (extractPoly a c).roots
```

`tau_mem_roots` packages recoverability: `τ` is literally an element of the (finite, `≤ D+1`)
root multiset the reduction enumerates.

---

## 2. Survives-the-attack — the honest, nuanced answer

The gate is: can `Classical.choice` still inhabit a winner?

- **Assumption form (1a): NO improvement — PROVEN still inhabited.** `repr_valid_of_extraction`
  shows the representation is free, so the exact trapdoor-extracting attack still wins w.p. 1.
  This form is **BROKEN**, mechanically demonstrated (not hand-waved).

- **Reduction form (1b): survives, but by *relocation*, not by uninhabitability.** The reduction
  is unconditionally true and non-vacuous. Under the exact attack it does the honest thing: it
  **transports** the `Classical.choice` t-SDH winner into a `Classical.choice` q-DLOG winner
  (feed the choice-winner's `(c,a)` into `extractPoly`, factor, recover `τ`). It never claims the
  winner is uninhabitable — it claims *if you can inhabit a t-SDH winner you can inhabit a q-DLOG
  winner*, which is exactly right and exactly what a reduction should say. The security therefore
  **rests entirely on q-DLOG** being hard for the real adversary class.

So AGM does **not**, by itself, make `Classical.choice` unable to inhabit a t-SDH winner (the
representation is free); it moves the uninhabitability requirement down to q-DLOG. If q-DLOG is
stated the same broken `∀`-way, it too is false below 1 (`Classical.choice` reads `g^x` and takes
the dlog). **A number or an uninhabitable statement must therefore live at the q-DLOG floor —
which needs GGM (Boneh–Boyen ~`q²/p`) or a resource-bounded class.** No free lunch.

**Reported honestly:** `survives_attack = PROVEN` that naïve-AGM-as-assumption is **BROKEN**
(the failure mode, mechanized); the reduction form **ARGUED-survives** by relocation to q-DLOG
(FKL polynomial core + representation-freeness are mechanized; the full probabilistic
`Adv ≤ Adv` threaded through ArkLib's game monad is not).

---

## 3. Numeric vs reduction, and what it rests on

- **`gives_numeric_bound = false`.** The reduction yields a *relation*, not a number:
  `Adv_tSDH^AGM(A) ≤ Adv_qDLOG(B)`, tight (advantage-preserving; the `D+1` roots cost the
  reduction *time*, not *advantage*). Nothing to falsify on its own.

- **`rests_on = q-DLOG`.** To turn the reduction into a t-SDH number you must supply a q-DLOG
  number, and a sound q-DLOG number itself rests on **GGM** (generic-group boundary, ~`q²/p`)
  or an assumed resource-bounded q-DLOG hardness. AGM buys the *reduction* (a mechanizable,
  advantage-tight relocation); it does not buy the floor.

---

## 4. Invasiveness

The `AgmSound.lean` artifact is **additive scratch** — one ~150-line file, imports ArkLib,
touches nothing in `Binding.lean`/`HardnessAssumptions.lean`. But adopting the *reduction form
as ArkLib's actual statement* is the genuinely invasive **option (A)** flagged in `../REPAIR.md`:
define an algebraic-adversary type carrying `Vector (ZMod p) (D+1)`, thread `ReprValid` into
`tSdhGame`/`tSdhExperiment`, define a q-DLOG game/assumption (ArkLib has none), and prove the
probabilistic reduction. That is new infrastructure + a game rewrite — maintainers' call, not a
drive-by. The minimal mergeable fix remains option (B) (`../REPAIR.md`, `binding-repair.patch`):
restate binding as the reduction bound it already proves; AGM→q-DLOG is the *heavier, more
textbook* direction this file scopes and de-risks.

---

## 5. Mechanizability ledger

**Compiled, `sorry`-free, axiom-clean** (`[propext, Classical.choice, Quot.sound]`):

| Lemma | Content |
|---|---|
| `extractPoly_root_and_ne_zero` | valid representation + win ⇒ nonzero poly of deg ≤ D+1 vanishing at τ (FKL core) |
| `tau_mem_roots` | τ is a member of the (≤ D+1)-element root multiset ⇒ recoverable |
| `repr_valid_of_extraction` | the naïve AGM representation is **free/valid data** for the choice-adversary ⇒ assumption form still inhabited |

**Not mechanized (named honestly):**
- The full probabilistic reduction inequality `Adv_tSDH^AGM ≤ Adv_qDLOG` threaded through
  ArkLib's `StateT … ProbComp` game monad — needs the algebraic-adversary type wired into
  `tSdhGame` (the invasive option-A infra).
- The group-to-exponent step `h = g₁^(a(τ))` from the *vector* representation — Part 1 works
  over an abstract `Polynomial (ZMod p)` `a` with `a.eval τ` as the exponent; connecting that to
  the `Vector (ZMod p) (D+1)` product-over-SRS form is routine but unwritten.
- **q-DLOG itself is not defined in ArkLib.** Getting a *number* out of this reduction is
  MONTHS-away-shaped: it needs a q-DLOG game + a GGM proof (or an assumed bound), neither of
  which VCVio/ArkLib currently carry.

**Artifact dir:** `/private/tmp/arklib-agmsound/AgmSound.lean` (scratch build) and this
directory's `AgmSound.lean` (committed copy).
