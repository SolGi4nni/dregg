/-
# Dregg2.Circuit.Emit.GnarkVerifier.MerkleEmit — the Merkle-BN254 opening check as a
Lean-authored, emitted R1CS, with a ∀-refinement theorem.

THE CHECK (the open_input opening — ~80% of the deployed wrap's constraint mass): the
native-BN254 Merkle path verification of `chain/gnark/merkle_bn254.go`
(`VerifyMerklePathBn254`) plus the MMCS leaf hash of `chain/gnark/fri_verify_native.go`
(`friMerkleLeafHashNative`): a claimed leaf at an index verifies to the committed root.
Per level (gnark, verbatim shape): `AssertIsBoolean(bit)`; `left = Select(bit, sib, node)`;
`right = Select(bit, node, sib)`; `node = Poseidon2Bn254Compress(left, right)`; finally
`AssertIsEqual(node, root)`. The leaf boundary: 8 canonical BabyBear limbs packed SHIFTED
(radix 2^31, digits `v+1` — `packShiftedBn254`) into one rate slot, one native Poseidon2
permutation, digest = lane 0.

Built READ-ONLY on the committed foundation: `R1csFr` (op-DAG → genuine R1CS with the
proven `gHolds`/`lower_sound` bridge), `Poseidon2Fr` (the KAT-pinned permutation `permute`
+ its wire builder `permuteW`), and the `EmitFaithful` socket (`emit_faithful`). The
`CanonicityToy` pattern — emit → R1CS → ∀-refinement — is followed, but the object here is
the REAL deployed check, at EVERY depth, quantified over every leaf/sibling/bit/root.

Deliverables (genuine ∀-theorems, not `#guard` samples):

  * **`merkle_path_refines`** — for every `leaf root : Fr`, `sibs : List Fr`,
    `bits : List Bool` (`|bits| = |sibs|` = the depth):
    `gHolds (merklePathData |sibs|) (pathAsg leaf sibs bits root)
       ↔ refRoot leaf (sibs.zip bits) = root`
    where `refRoot` is the Lean twin of the deployed `merkleBn254RefRoot` walk and
    `pathAsg` is the honest witness fill (the Lean twin of gnark's hint solver). Both
    polarities: a wrong root — hence ANY tamper (leaf/sibling/bit) that moves the
    recomputed root — makes `gHolds` FALSE.
  * **`merkle_open_refines`** — same, for the COMPOSED open_input check (in-circuit leaf
    hash + path walk): `… ↔ refRoot (leafHashRef limbs) (sibs.zip bits) = root`.
  * **`merkle_path_sound_of_boolean` / `merkle_open_sound_of_boolean`** — the adversarial
    face: ANY witness whose bit region is boolean and which satisfies the circuit has its
    root variable EQUAL to the reference recomputation from its own leaf/sibling/bit
    variables. (Booleanity-from-`b·b=b` itself is the named Pratt/primality seam of
    `R1csFr`, exactly as in `CanonicityToy`.)
  * `*_refines_emitted` — the same iff at the emitted wire form, via `emit_faithful`.

`#guard` KAT anchors against the deployed Go/Rust gold vectors:
  * `merkleBn254KATRootHex` (merkle_bn254_test.go): the pinned depth-4 root, accepted by
    the reference twin AND by the built circuit; reject canaries mirror the Go tests
    (tampered leaf / wrong sibling / flipped bit / corrupted root / non-boolean bit).
  * `katLeafAHex`/`katLeafBHex`/`katMmcsRootHex` (fri_leaf_hash_kat_test.go): the Rust
    MMCS leaf digests and the real `MerkleTreeMmcs::commit` root — pinned at the
    reference twin AND through the composed circuit (leaf hash + 1-level walk).
  * One vector through the FULL `Circuit.lower` R1CS with the canonical extension.

Classified seams (named, not silent):
  * Booleanity forcing (`x² = x → x ∈ {0,1}`) needs `Fr` a field — the named
    Pratt-certificate seam of `R1csFr`; the `sound_of_boolean` theorems take booleanity
    as a hypothesis, exactly the `CanonicityToy` posture. The honest-fill iff theorems
    need no such hypothesis (bits are encoded 0/1).
  * `packShiftedW` writes the radix step as `const · acc` — a `mul` node, so the lowering
    spends aux rows where the deployed gnark pack is constraint-free linear. Semantically
    identical; cost-only divergence, in the safe direction.
  * Assert ORDER: the boolean asserts are hoisted before the compression chain (gnark
    interleaves them per level). `Circuit.satisfied` is membership-quantified, so the
    denotation is unchanged.
-/
import Mathlib.Tactic.LinearCombination
import Dregg2.Tactics
import Dregg2.Circuit.R1csFr
import Dregg2.Circuit.Poseidon2Fr
import Dregg2.Circuit.Emit.GnarkVerifier.EmitFaithful

namespace Dregg2.Circuit.Emit.GnarkVerifier.Merkle

open Dregg2.Circuit.R1csFr
open Dregg2.Circuit.Poseidon2Fr (BuilderM sboxW extLinearW intLinearW fullRoundW
  partialRoundW permuteW permute compress sbox extLinear intLinear fullRound partialRound
  St rcExtInitial rcInternal rcExtTerminal)

/-! ## §1 Semantic reference twins of the deployed Go. -/

/-- The deployed path walk (`merkleBn254RefRoot`): bottom-up, `bit = false` ⇒ the running
node is the LEFT child (`compress node sib`), `bit = true` ⇒ swapped. -/
def refRoot (x : Fr) : List (Fr × Bool) → Fr
  | [] => x
  | (sib, b) :: rest => refRoot (if b then compress sib x else compress x sib) rest

/-- The shifted rate-slot packing (`packShiftedBn254`): little-endian radix-2^31 Horner
over the digits `v + 1` (the `+1` shift reserves zero as "no digit"). -/
def packShifted (vals : List Fr) : Fr :=
  vals.foldr (fun v acc => (2 ^ 31 : Fr) * acc + (v + 1)) 0

/-- The MMCS leaf hash (`friMerkleLeafHashNative` / `multiField32HashNative` on one
8-limb row): state `[pack, 0, 0]`, one permutation, digest = lane 0. -/
def leafHashRef (vals : List Fr) : Fr := (permute (packShifted vals, 0, 0)).1

/-- Boolean → field encoding of a path bit. -/
def encB (b : Bool) : Fr := if b then 1 else 0

/-- One field-level walk step as the CIRCUIT computes it (two `Select` muxes + compress);
on boolean bits this is the `refRoot` step (`stepFr_encB`). -/
def stepFr (node : Fr) (p : Fr × Fr) : Fr :=
  compress (p.2 * (p.1 - node) + node) (p.2 * (node - p.1) + p.1)

theorem stepFr_encB (x s : Fr) (b : Bool) :
    stepFr x (s, encB b) = if b then compress s x else compress x s := by
  cases b
  · show compress (0 * (s - x) + x) (0 * (x - s) + s) = compress x s
    norm_num
  · show compress (1 * (s - x) + x) (1 * (x - s) + s) = compress s x
    congr 1 <;> ring

/-! ## §2 Variable bounds, define-chains, and the chain solver. -/

/-- `wBelow w n`: the wire mentions only variables `< n`. -/
def wBelow : Wire → ℕ → Prop
  | .var v, n => v < n
  | .const _, _ => True
  | .add x y, n => wBelow x n ∧ wBelow y n
  | .mul x y, n => wBelow x n ∧ wBelow y n
  | .select b x y, n => wBelow b n ∧ wBelow x n ∧ wBelow y n

theorem wBelow_mono : ∀ {w : Wire} {i j : ℕ}, wBelow w i → i ≤ j → wBelow w j
  | .var _, _, _, h, hij => Nat.lt_of_lt_of_le h hij
  | .const _, _, _, _, _ => trivial
  | .add _ _, _, _, h, hij => ⟨wBelow_mono h.1 hij, wBelow_mono h.2 hij⟩
  | .mul _ _, _, _, h, hij => ⟨wBelow_mono h.1 hij, wBelow_mono h.2 hij⟩
  | .select _ _ _, _, _, h, hij =>
      ⟨wBelow_mono h.1 hij, wBelow_mono h.2.1 hij, wBelow_mono h.2.2 hij⟩

/-- Evaluation only reads variables below the bound. -/
theorem eval_congr : ∀ {w : Wire} {n : ℕ} {a a' : Assignment},
    wBelow w n → (∀ v, v < n → a v = a' v) → w.eval a = w.eval a'
  | .var _, _, _, _, hw, h => h _ hw
  | .const _, _, _, _, _, _ => rfl
  | .add _ _, _, _, _, hw, h => by
      simp only [Wire.eval]; rw [eval_congr hw.1 h, eval_congr hw.2 h]
  | .mul _ _, _, _, _, hw, h => by
      simp only [Wire.eval]; rw [eval_congr hw.1 h, eval_congr hw.2 h]
  | .select _ _ _, _, _, _, hw, h => by
      simp only [Wire.eval]
      rw [eval_congr hw.1 h, eval_congr hw.2.1 h, eval_congr hw.2.2 h]

/-- A **define-chain** from `n`: each assert defines the next fresh variable from wires
over strictly earlier variables — the shape every builder emission has. -/
inductive DefChain : ℕ → List (Wire × Wire) → ℕ → Prop
  | nil (n : ℕ) : DefChain n [] n
  | cons {n m : ℕ} {w : Wire} {rest : List (Wire × Wire)} :
      wBelow w n → DefChain (n + 1) rest m → DefChain n ((w, Wire.var n) :: rest) m

theorem DefChain.le {n : ℕ} {l : List (Wire × Wire)} {m : ℕ} (h : DefChain n l m) :
    n ≤ m := by
  induction h with
  | nil => exact le_rfl
  | cons _ _ ih => omega

theorem DefChain.append {n k m : ℕ} {l₁ l₂ : List (Wire × Wire)}
    (h₁ : DefChain n l₁ k) (h₂ : DefChain k l₂ m) : DefChain n (l₁ ++ l₂) m := by
  induction h₁ with
  | nil => simpa using h₂
  | cons hw _ ih => exact .cons hw (ih h₂)

/-- The honest chain solver (the Lean twin of gnark's hint solver): walk the defining
asserts, filling each defined variable with its defining wire's value. -/
def solveChain (a : Assignment) : List (Wire × Wire) → Assignment
  | [] => a
  | (w, Wire.var k) :: rest => solveChain (Function.update a k (w.eval a)) rest
  | _ :: rest => solveChain a rest

/-- The solver never touches variables below the chain start. -/
theorem solveChain_agree_below :
    ∀ (l : List (Wire × Wire)) {n m : ℕ} (a : Assignment),
      DefChain n l m → ∀ v, v < n → solveChain a l v = a v
  | [], _, _, _, _, _, _ => rfl
  | (w, _) :: rest, n, m, a, h, v, hv => by
      cases h with
      | cons hw hrest =>
          show solveChain (Function.update a n (w.eval a)) rest v = a v
          rw [solveChain_agree_below rest _ hrest v (Nat.lt_succ_of_lt hv),
            Function.update_of_ne (Nat.ne_of_lt hv)]

/-- The solved assignment satisfies every assert of its own define-chain. -/
theorem solveChain_sat :
    ∀ (l : List (Wire × Wire)) {n m : ℕ} (a : Assignment),
      DefChain n l m → ∀ p ∈ l, p.1.eval (solveChain a l) = p.2.eval (solveChain a l)
  | [], _, _, _, _, p, hp => absurd hp (by simp)
  | (w, _) :: rest, n, m, a, h, p, hp => by
      cases h with
      | cons hw hrest =>
          show p.1.eval (solveChain (Function.update a n (w.eval a)) rest)
              = p.2.eval (solveChain (Function.update a n (w.eval a)) rest)
          set a' := Function.update a n (w.eval a) with ha'
          rcases List.mem_cons.mp hp with rfl | hp'
          · show w.eval (solveChain a' rest) = (solveChain a' rest) n
            have h1 : solveChain a' rest n = a' n :=
              solveChain_agree_below rest a' hrest n (Nat.lt_succ_self n)
            have h2 : a' n = w.eval a := by rw [ha', Function.update_self]
            have h3 : w.eval (solveChain a' rest) = w.eval a := by
              refine eval_congr hw fun v hv => ?_
              rw [solveChain_agree_below rest a' hrest v (Nat.lt_succ_of_lt hv), ha',
                Function.update_of_ne (Nat.ne_of_lt hv)]
            rw [h1, h2, h3]
          · exact solveChain_sat rest a' hrest p hp'

/-! ## §3 The `Emits` builder-spec framework.

`Emits bel ev m bound f`: run from ANY state `(n, cs)` with `bound ≤ n`, the builder
computation `m` appends a define-chain, returns a result below the new counter, and —
under ANY assignment satisfying the appended asserts — the result denotes `f`. The forced
direction needs no freshness (the defining equations pin every minted value); the
define-chain gives honest solvability via `solveChain_sat`. -/

section Framework

variable {α β : Type} {Vα Vβ : Type}

def Emits (bel : α → ℕ → Prop) (ev : α → Assignment → Vα)
    (m : BuilderM α) (bound : ℕ) (f : Assignment → Vα) : Prop :=
  ∀ n cs, bound ≤ n →
    ∃ x n' new, m (n, cs) = (x, (n', cs ++ new)) ∧
      DefChain n new n' ∧ bel x n' ∧
      ∀ a : Assignment, (∀ p ∈ new, p.1.eval a = p.2.eval a) → ev x a = f a

theorem Emits.congr {bel : α → ℕ → Prop} {ev : α → Assignment → Vα}
    {m : BuilderM α} {bound : ℕ} {f f' : Assignment → Vα}
    (hm : Emits bel ev m bound f) (h : ∀ a, f a = f' a) :
    Emits bel ev m bound f' := by
  intro n cs hn
  obtain ⟨x, n', new, hrun, hch, hb, hf⟩ := hm n cs hn
  exact ⟨x, n', new, hrun, hch, hb, fun a ha => (hf a ha).trans (h a)⟩

theorem Emits.bind {belα : α → ℕ → Prop} {evα : α → Assignment → Vα}
    {belβ : β → ℕ → Prop} {evβ : β → Assignment → Vβ}
    {m : BuilderM α} {k : α → BuilderM β} {bound : ℕ}
    {f : Assignment → Vα} {g : Vα → Assignment → Vβ}
    (hm : Emits belα evα m bound f)
    (hk : ∀ x b, bound ≤ b → belα x b →
      Emits belβ evβ (k x) b (fun a => g (evα x a) a)) :
    Emits belβ evβ (m >>= k) bound (fun a => g (f a) a) := by
  intro n cs hn
  obtain ⟨x₁, n₁, new₁, hrun₁, hch₁, hb₁, hf₁⟩ := hm n cs hn
  obtain ⟨x₂, n₂, new₂, hrun₂, hch₂, hb₂, hf₂⟩ :=
    hk x₁ n₁ (hn.trans hch₁.le) hb₁ n₁ (cs ++ new₁) le_rfl
  refine ⟨x₂, n₂, new₁ ++ new₂, ?_, hch₁.append hch₂, hb₂, ?_⟩
  · show (m >>= k) (n, cs) = (x₂, (n₂, cs ++ (new₁ ++ new₂)))
    have h1 : (m >>= k) (n, cs) = k (m (n, cs)).1 (m (n, cs)).2 := rfl
    rw [h1, hrun₁]
    show k x₁ (n₁, cs ++ new₁) = (x₂, (n₂, cs ++ (new₁ ++ new₂)))
    rw [hrun₂, List.append_assoc]
  · intro a ha
    show evβ x₂ a = g (f a) a
    have h2 : evβ x₂ a = g (evα x₁ a) a :=
      hf₂ a fun p hp => ha p (List.mem_append_right _ hp)
    have h1 : evα x₁ a = f a :=
      hf₁ a fun p hp => ha p (List.mem_append_left _ hp)
    rw [h2, h1]

theorem Emits.pure {bel : α → ℕ → Prop} {ev : α → Assignment → Vα}
    (mono : ∀ x i j, bel x i → i ≤ j → bel x j)
    (x : α) {bound : ℕ} (hx : bel x bound) :
    Emits bel ev (Pure.pure x : BuilderM α) bound (ev x) := by
  intro n cs hn
  refine ⟨x, n, [], ?_, .nil n, mono x bound n hx hn, fun _ _ => rfl⟩
  show (Pure.pure x : BuilderM α) (n, cs) = (x, (n, cs ++ []))
  rw [List.append_nil]
  exact rfl

end Framework

/-- `wBelow` monotonicity in the `Emits.pure` argument shape. -/
theorem wBelow_mono' : ∀ (w : Wire) (i j : ℕ), wBelow w i → i ≤ j → wBelow w j :=
  fun _ _ _ h hij => wBelow_mono h hij

def bel3 (t : Wire × Wire × Wire) (n : ℕ) : Prop :=
  wBelow t.1 n ∧ wBelow t.2.1 n ∧ wBelow t.2.2 n

def ev3 (t : Wire × Wire × Wire) (a : Assignment) : St :=
  (t.1.eval a, t.2.1.eval a, t.2.2.eval a)

theorem bel3_mono : ∀ (t : Wire × Wire × Wire) (i j : ℕ), bel3 t i → i ≤ j → bel3 t j :=
  fun _ _ _ h hij =>
    ⟨wBelow_mono h.1 hij, wBelow_mono h.2.1 hij, wBelow_mono h.2.2 hij⟩

abbrev EmitsW := Emits wBelow Wire.eval
abbrev Emits3 := Emits bel3 ev3

/-- The atomic builder step: `emit w` mints one defining assert. -/
theorem emit_emits (w : Wire) {bound : ℕ} (hw : wBelow w bound) :
    EmitsW (Dregg2.Circuit.Poseidon2Fr.emit w) bound w.eval := by
  intro n cs hn
  refine ⟨.var n, n + 1, [(w, .var n)], rfl,
    .cons (wBelow_mono hw hn) (.nil _), Nat.lt_succ_self n, ?_⟩
  intro a ha
  exact (ha (w, .var n) (by simp)).symm

/-- Generic `foldlM` spec for triple-state steps (the round schedules). -/
theorem emits3_foldlM {β : Type}
    {step : (Wire × Wire × Wire) → β → BuilderM (Wire × Wire × Wire)}
    {sem : St → β → St}
    (hstep : ∀ t b bound, bel3 t bound → Emits3 (step t b) bound (fun a => sem (ev3 t a) b)) :
    ∀ (l : List β) (t : Wire × Wire × Wire) (bound : ℕ), bel3 t bound →
      Emits3 (List.foldlM step t l) bound (fun a => List.foldl sem (ev3 t a) l)
  | [], t, bound, ht => by
      rw [List.foldlM_nil]
      exact (Emits.pure bel3_mono t ht).congr fun a => by simp
  | b :: bs, t, bound, ht => by
      rw [List.foldlM_cons]
      refine (Emits.bind (g := fun v _ => List.foldl sem v bs)
        (hstep t b bound ht)
        (fun t' b' _ hbt' => emits3_foldlM hstep bs t' b' hbt')).congr fun a => by
          rw [List.foldl_cons]

/-! ## §4 Specs for the Poseidon2 gadget builders (read-only reuse of `Poseidon2Fr`). -/

theorem sboxW_emits (x : Wire) {bound : ℕ} (hx : wBelow x bound) :
    EmitsW (sboxW x) bound (fun a => sbox (x.eval a)) := by
  have h := Emits.bind (g := fun v a => v * v * x.eval a)
    (emit_emits (.mul x x) ⟨hx, hx⟩)
    (fun x2 b hb hx2 =>
      Emits.bind (g := fun v a => v * x.eval a)
        (emit_emits (.mul x2 x2) ⟨hx2, hx2⟩)
        (fun x4 b' hb' hx4 =>
          emit_emits (.mul x4 x) ⟨hx4, wBelow_mono hx (hb.trans hb')⟩))
  exact h.congr fun a => rfl

theorem extLinearW_emits (s : Wire × Wire × Wire) {bound : ℕ} (hs : bel3 s bound) :
    Emits3 (extLinearW s) bound (fun a => extLinear (ev3 s a)) := by
  obtain ⟨h1, h2, h3⟩ := hs
  have hsum : wBelow (Wire.add s.1 (.add s.2.1 s.2.2)) bound := ⟨h1, h2, h3⟩
  have h := Emits.bind
    (g := fun v a => (v,
      Wire.eval (.add s.2.1 (.add s.1 (.add s.2.1 s.2.2))) a,
      Wire.eval (.add s.2.2 (.add s.1 (.add s.2.1 s.2.2))) a))
    (emit_emits (.add s.1 (.add s.1 (.add s.2.1 s.2.2))) ⟨h1, hsum⟩)
    (fun A bA hbA hA =>
      Emits.bind
        (g := fun v a => (Wire.eval A a, v,
          Wire.eval (.add s.2.2 (.add s.1 (.add s.2.1 s.2.2))) a))
        (emit_emits (.add s.2.1 (.add s.1 (.add s.2.1 s.2.2)))
          ⟨wBelow_mono h2 hbA, wBelow_mono hsum hbA⟩)
        (fun B bB hbB hB =>
          Emits.bind (g := fun v a => (Wire.eval A a, Wire.eval B a, v))
            (emit_emits (.add s.2.2 (.add s.1 (.add s.2.1 s.2.2)))
              ⟨wBelow_mono h3 (hbA.trans hbB), wBelow_mono hsum (hbA.trans hbB)⟩)
            (fun C bC hbC hC =>
              (Emits.pure (ev := ev3) bel3_mono (A, B, C)
                ⟨wBelow_mono hA (hbB.trans hbC), wBelow_mono hB hbC, hC⟩).congr
                fun a => rfl)))
  refine h.congr fun a => ?_
  show (_, _, _) = extLinear (ev3 s a)
  simp only [extLinear, ev3, Wire.eval, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

theorem intLinearW_emits (s : Wire × Wire × Wire) {bound : ℕ} (hs : bel3 s bound) :
    Emits3 (intLinearW s) bound (fun a => intLinear (ev3 s a)) := by
  obtain ⟨h1, h2, h3⟩ := hs
  have hsum : wBelow (Wire.add s.1 (.add s.2.1 s.2.2)) bound := ⟨h1, h2, h3⟩
  have h := Emits.bind
    (g := fun v a => (v,
      Wire.eval (.add s.2.1 (.add s.1 (.add s.2.1 s.2.2))) a,
      Wire.eval (.add (.add s.2.2 s.2.2) (.add s.1 (.add s.2.1 s.2.2))) a))
    (emit_emits (.add s.1 (.add s.1 (.add s.2.1 s.2.2))) ⟨h1, hsum⟩)
    (fun A bA hbA hA =>
      Emits.bind
        (g := fun v a => (Wire.eval A a, v,
          Wire.eval (.add (.add s.2.2 s.2.2) (.add s.1 (.add s.2.1 s.2.2))) a))
        (emit_emits (.add s.2.1 (.add s.1 (.add s.2.1 s.2.2)))
          ⟨wBelow_mono h2 hbA, wBelow_mono hsum hbA⟩)
        (fun B bB hbB hB =>
          Emits.bind (g := fun v a => (Wire.eval A a, Wire.eval B a, v))
            (emit_emits (.add (.add s.2.2 s.2.2) (.add s.1 (.add s.2.1 s.2.2)))
              ⟨⟨wBelow_mono h3 (hbA.trans hbB), wBelow_mono h3 (hbA.trans hbB)⟩,
                wBelow_mono hsum (hbA.trans hbB)⟩)
            (fun C bC hbC hC =>
              (Emits.pure (ev := ev3) bel3_mono (A, B, C)
                ⟨wBelow_mono hA (hbB.trans hbC), wBelow_mono hB hbC, hC⟩).congr
                fun a => rfl)))
  refine h.congr fun a => ?_
  show (_, _, _) = intLinear (ev3 s a)
  simp only [intLinear, ev3, Wire.eval, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

theorem fullRoundW_emits (s : Wire × Wire × Wire) (rc : Fr × Fr × Fr) {bound : ℕ}
    (hs : bel3 s bound) :
    Emits3 (fullRoundW s rc) bound (fun a => fullRound (ev3 s a) rc) := by
  obtain ⟨h1, h2, h3⟩ := hs
  have h := Emits.bind
    (g := fun v a => extLinear (v,
      sbox (Wire.eval (.add s.2.1 (.const rc.2.1)) a),
      sbox (Wire.eval (.add s.2.2 (.const rc.2.2)) a)))
    (sboxW_emits (.add s.1 (.const rc.1)) ⟨h1, trivial⟩)
    (fun A bA hbA hA =>
      Emits.bind
        (g := fun v a => extLinear (Wire.eval A a, v,
          sbox (Wire.eval (.add s.2.2 (.const rc.2.2)) a)))
        (sboxW_emits (.add s.2.1 (.const rc.2.1)) ⟨wBelow_mono h2 hbA, trivial⟩)
        (fun B bB hbB hB =>
          Emits.bind (g := fun v a => extLinear (Wire.eval A a, Wire.eval B a, v))
            (sboxW_emits (.add s.2.2 (.const rc.2.2))
              ⟨wBelow_mono h3 (hbA.trans hbB), trivial⟩)
            (fun C bC hbC hC =>
              extLinearW_emits (A, B, C)
                ⟨wBelow_mono hA (hbB.trans hbC), wBelow_mono hB hbC, hC⟩)))
  exact h.congr fun a => rfl

theorem partialRoundW_emits (s : Wire × Wire × Wire) (rc : Fr) {bound : ℕ}
    (hs : bel3 s bound) :
    Emits3 (partialRoundW s rc) bound (fun a => partialRound (ev3 s a) rc) := by
  obtain ⟨h1, h2, h3⟩ := hs
  have h := Emits.bind
    (g := fun v a => intLinear (v, Wire.eval s.2.1 a, Wire.eval s.2.2 a))
    (sboxW_emits (.add s.1 (.const rc)) ⟨h1, trivial⟩)
    (fun A bA hbA hA =>
      intLinearW_emits (A, s.2.1, s.2.2)
        ⟨hA, wBelow_mono h2 hbA, wBelow_mono h3 hbA⟩)
  exact h.congr fun a => rfl

theorem permuteW_emits (s : Wire × Wire × Wire) {bound : ℕ} (hs : bel3 s bound) :
    Emits3 (permuteW s) bound (fun a => permute (ev3 s a)) := by
  have h := Emits.bind
    (g := fun v _ => List.foldl fullRound
      (List.foldl partialRound (List.foldl fullRound v rcExtInitial) rcInternal)
      rcExtTerminal)
    (extLinearW_emits s hs)
    (fun t1 b1 hb1 ht1 =>
      Emits.bind
        (g := fun v _ => List.foldl fullRound (List.foldl partialRound v rcInternal)
          rcExtTerminal)
        (emits3_foldlM (fun t rc bd h => fullRoundW_emits t rc h) rcExtInitial t1 b1 ht1)
        (fun t2 b2 hb2 ht2 =>
          Emits.bind (g := fun v _ => List.foldl fullRound v rcExtTerminal)
            (emits3_foldlM (fun t rc bd h => partialRoundW_emits t rc h) rcInternal t2 b2 ht2)
            (fun t3 b3 hb3 ht3 =>
              emits3_foldlM (fun t rc bd h => fullRoundW_emits t rc h) rcExtTerminal t3 b3 ht3)))
  exact h.congr fun a => rfl

/-- The 2-to-1 compression as a builder (the `Poseidon2Bn254Compress` twin): permute
`(l, r, 0)`, squeeze lane 0. -/
def compressW (l r : Wire) : BuilderM Wire := do
  let out ← permuteW (l, r, .const 0)
  pure out.1

theorem compressW_emits (l r : Wire) {bound : ℕ}
    (hl : wBelow l bound) (hr : wBelow r bound) :
    EmitsW (compressW l r) bound (fun a => compress (l.eval a) (r.eval a)) := by
  have h := Emits.bind (g := fun v _ => v.1)
    (permuteW_emits (l, r, .const 0) ⟨hl, hr, trivial⟩)
    (fun out b hb hout =>
      (Emits.pure (ev := Wire.eval) wBelow_mono' out.1 hout.1).congr fun a => rfl)
  exact h.congr fun a => rfl

-- `compressW` is a 240-multiplication monadic value (the whole Poseidon2 permutation).
-- Its spec (`compressW_emits`) is now closed, so keep it an OPAQUE head for every
-- downstream defeq: without this, unifying `pathW`'s builder against the `>>=` form makes
-- `whnf` reduce the full permutation and blow the heartbeat/recursion limits.
attribute [local irreducible] compressW

/-- The field-level circuit step (two `Select` muxes + `compress`) reads back as the
`stepFr` twin — proved WITHOUT reducing `compress` (the muxes normalise to `stepFr`'s
arguments; `compress` stays an opaque head on both sides). -/
theorem stepFr_select (node sib bit : Wire) (a : Assignment) :
    compress ((Wire.select bit sib node).eval a) ((Wire.select bit node sib).eval a)
      = stepFr (node.eval a) (sib.eval a, bit.eval a) := by
  simp only [stepFr, Wire.eval]

/-- The path walk as a builder (`ComputeMerkleRootBn254`'s loop body, minus the hoisted
booleanity asserts): per level, two `Select` muxes and one compression. Written as a
`foldlM` threading the running node so the recursion lives in the (structural, cleanly
reducible) library `foldlM` — a self-recursive `do`-block would fall to well-founded
recursion (the recursive call sits under `>>=`), whose `whnf` drags in the whole Poseidon2
monadic value. Semantics are identical: `pathW_nil`/`pathW_cons` are the two clauses. -/
def pathW (node : Wire) (ps : List (Wire × Wire)) : BuilderM Wire :=
  ps.foldlM (fun nd p => compressW (.select p.2 p.1 nd) (.select p.2 nd p.1)) node

theorem pathW_nil (node : Wire) : pathW node [] = pure node := by
  simp only [pathW, List.foldlM_nil]

theorem pathW_cons (node sib bit : Wire) (rest : List (Wire × Wire)) :
    pathW node ((sib, bit) :: rest)
      = (compressW (.select bit sib node) (.select bit node sib) >>=
          fun parent => pathW parent rest) := by
  simp only [pathW, List.foldlM_cons]

/-- Generic `foldlM` spec for a wire accumulator threaded through element steps that read
their own witness (the `pathW` shape). The step `stepB` is kept ABSTRACT: the whole proof
runs without ever unifying against the concrete `compressW`/Poseidon2 monadic value — the
exact reason the specialized `emits3_foldlM` builds. `pathW_emits` is one instantiation. -/
theorem emitsW_walk {belE : (Wire × Wire) → ℕ → Prop}
    {stepB : Wire → (Wire × Wire) → BuilderM Wire}
    {semF : Fr → (Wire × Wire) → Assignment → Fr}
    (belE_mono : ∀ p i j, belE p i → i ≤ j → belE p j)
    (hstepB : ∀ (nd : Wire) (p : Wire × Wire) (bd : ℕ), wBelow nd bd → belE p bd →
      EmitsW (stepB nd p) bd (fun a => semF (nd.eval a) p a)) :
    ∀ (l : List (Wire × Wire)) (node : Wire) {bound : ℕ},
      wBelow node bound → (∀ p ∈ l, belE p bound) →
      EmitsW (l.foldlM stepB node) bound
        (fun a => l.foldl (fun nd p => semF nd p a) (node.eval a)) := by
  intro l
  induction l with
  | nil =>
      intro node bound hn _
      rw [List.foldlM_nil]
      exact (Emits.pure wBelow_mono' node hn).congr fun a => by simp
  | cons hd tl ih =>
      intro node bound hn hps
      rw [List.foldlM_cons]
      exact (Emits.bind
        (g := fun v a => tl.foldl (fun nd p => semF nd p a) v)
        (hstepB node hd bound hn (hps hd List.mem_cons_self))
        (fun parent b hb hparent =>
          ih parent hparent
            (fun p hp => belE_mono p bound b (hps p (List.mem_cons_of_mem _ hp)) hb))).congr
        fun a => by rw [List.foldl_cons]

/-- Per-level bound predicate for a `(sibling, bit)` pair. -/
def belPair (p : Wire × Wire) (n : ℕ) : Prop := wBelow p.1 n ∧ wBelow p.2 n

/-- **The path-walk builder spec** — one instantiation of `emitsW_walk` with the concrete
`compressW` step (its spec `compressW_emits` + `stepFr_select` supplying the read-back).
Under ANY assignment satisfying the emitted asserts, `pathW node ps` denotes the field
walk `ps.foldl stepFr (node.eval a)`. -/
theorem pathW_emits (ps : List (Wire × Wire)) (node : Wire) {bound : ℕ}
    (hn : wBelow node bound) (hps : ∀ p ∈ ps, wBelow p.1 bound ∧ wBelow p.2 bound) :
    EmitsW (pathW node ps) bound
      (fun a => ps.foldl (fun nd p => stepFr nd (p.1.eval a, p.2.eval a)) (node.eval a)) :=
  emitsW_walk (belE := belPair)
    (stepB := fun nd p => compressW (.select p.2 p.1 nd) (.select p.2 nd p.1))
    (semF := fun nd p a => stepFr nd (p.1.eval a, p.2.eval a))
    (fun _p _ _ h hij => ⟨wBelow_mono h.1 hij, wBelow_mono h.2 hij⟩)
    (fun nd p _ hnd hp =>
      (compressW_emits (.select p.2 p.1 nd) (.select p.2 nd p.1)
        ⟨hp.2, hp.1, hnd⟩ ⟨hp.2, hnd, hp.1⟩).congr fun a => stepFr_select nd p.1 p.2 a)
    ps node hn hps

/-- The shifted rate-slot pack as a PURE wire (adds + const-muls, no minting). -/
def packShiftedW (vals : List Wire) : Wire :=
  vals.foldr (fun v acc => .add (.mul (.const ((2 : Fr) ^ 31)) acc) (.add v (.const 1)))
    (.const 0)

theorem packShiftedW_cons (v : Wire) (vs : List Wire) :
    packShiftedW (v :: vs)
      = .add (.mul (.const ((2 : Fr) ^ 31)) (packShiftedW vs)) (.add v (.const 1)) := rfl

theorem packShifted_cons (v : Fr) (vs : List Fr) :
    packShifted (v :: vs) = (2 ^ 31 : Fr) * packShifted vs + (v + 1) := rfl

theorem packShiftedW_eval (vals : List Wire) (a : Assignment) :
    (packShiftedW vals).eval a = packShifted (vals.map (Wire.eval · a)) := by
  induction vals with
  | nil => rfl
  | cons v vs ih =>
      rw [packShiftedW_cons, List.map_cons, packShifted_cons]
      show (2 : Fr) ^ 31 * (packShiftedW vs).eval a + (v.eval a + 1) = _
      rw [ih]

theorem packShiftedW_below (vals : List Wire) {bound : ℕ}
    (h : ∀ w ∈ vals, wBelow w bound) : wBelow (packShiftedW vals) bound := by
  induction vals with
  | nil => trivial
  | cons v vs ih =>
      rw [packShiftedW_cons]
      exact ⟨⟨trivial, ih fun w hw => h w (List.mem_cons_of_mem _ hw)⟩,
        h v List.mem_cons_self, trivial⟩

/-- The MMCS leaf hash as a builder (`friMerkleLeafHashNative`'s one-row case): pack the
limbs shifted into lane 0, permute `[pack, 0, 0]`, squeeze lane 0. -/
def leafHashW (vals : List Wire) : BuilderM Wire := do
  let out ← permuteW (packShiftedW vals, .const 0, .const 0)
  pure out.1

theorem leafHashW_emits (vals : List Wire) {bound : ℕ}
    (h : ∀ w ∈ vals, wBelow w bound) :
    EmitsW (leafHashW vals) bound (fun a => leafHashRef (vals.map (Wire.eval · a))) := by
  have hh := Emits.bind (g := fun v _ => v.1)
    (permuteW_emits (packShiftedW vals, .const 0, .const 0)
      ⟨packShiftedW_below vals h, trivial, trivial⟩)
    (fun out b hb hout =>
      (Emits.pure (ev := Wire.eval) wBelow_mono' out.1 hout.1).congr fun a => rfl)
  refine hh.congr fun a => ?_
  show (permute ((packShiftedW vals).eval a, 0, 0)).1 = _
  rw [packShiftedW_eval]
  rfl

/-! ## §5 The deployed Merkle-path opening as a `GnarkCircuitData`, and its ∀-refinement.

Layout (interleaved so a position's variable index is DEPTH-independent — the key to a
clean induction): `var 0` = leaf, `var 1` = root, `var (2+2i)` = sibling `i`,
`var (2+2i+1)` = path bit `i`; Poseidon internals minted from `2+2d`. The circuit is the
per-level booleanity asserts, the compression chain (`pathW`, built on the committed
`compressW`/`Poseidon2Fr.compress`), and the final `finalNode = root` assert. -/

/-- The `(sibling, bit)` wire pairs for a depth-`d` path, from base variable `base`. -/
def pairWiresFrom (base : ℕ) : ℕ → List (Wire × Wire)
  | 0 => []
  | d + 1 => (Wire.var base, Wire.var (base + 1)) :: pairWiresFrom (base + 2) d

/-- The per-level booleanity asserts (`AssertIsBoolean(bit)` as `bit·bit = bit`). -/
def bitBoolFrom (base : ℕ) : ℕ → List (Wire × Wire)
  | 0 => []
  | d + 1 => (Wire.mul (.var (base + 1)) (.var (base + 1)), Wire.var (base + 1))
      :: bitBoolFrom (base + 2) d

/-- The depth-`d` `(sibling, bit)` wire pairs at the canonical layout. -/
def pairWires (d : ℕ) : List (Wire × Wire) := pairWiresFrom 2 d

theorem pairWiresFrom_below (bound : ℕ) :
    ∀ (base d : ℕ), base + 2 * d ≤ bound →
      ∀ p ∈ pairWiresFrom base d, wBelow p.1 bound ∧ wBelow p.2 bound
  | _, 0, _, _, hp => absurd hp (by simp [pairWiresFrom])
  | base, d + 1, hbd, p, hp => by
      rw [pairWiresFrom, List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact ⟨show base < bound by omega, show base + 1 < bound by omega⟩
      · exact pairWiresFrom_below bound (base + 2) d (by omega) p hp

/-- **The path-walk over honest siblings/bits recomputes the reference root.** The
Var-indexed circuit fold (two `Select` muxes + `compress` per level) equals the deployed
`refRoot` walk, for any assignment that reads siblings/bits at the canonical indices. -/
theorem foldl_pairWiresFrom_refRoot (a : Assignment) (sibs : List Fr) :
    ∀ (base : ℕ) (bits : List Bool) (acc : Fr),
      sibs.length = bits.length →
      (∀ i, i < sibs.length → a (base + 2 * i) = sibs.getD i 0) →
      (∀ i, i < bits.length → a (base + 2 * i + 1) = encB (bits.getD i false)) →
      (pairWiresFrom base sibs.length).foldl
          (fun nd p => stepFr nd (p.1.eval a, p.2.eval a)) acc
        = refRoot acc (sibs.zip bits) := by
  induction sibs with
  | nil => intro base bits acc _ _ _; rfl
  | cons s ss ih =>
      intro base bits acc hlen hsib hbit
      rcases bits with _ | ⟨b, bs⟩
      · simp at hlen
      · have hlen' : ss.length = bs.length := by simpa using hlen
        have hs0 : a base = s := by
          have h := hsib 0 (by simp only [List.length_cons]; omega); simpa using h
        have hb0 : a (base + 1) = encB b := by
          have h := hbit 0 (by simp only [List.length_cons]; omega); simpa using h
        show (pairWiresFrom base (ss.length + 1)).foldl
            (fun nd p => stepFr nd (p.1.eval a, p.2.eval a)) acc
            = refRoot acc ((s :: ss).zip (b :: bs))
        rw [pairWiresFrom, List.foldl_cons, List.zip_cons_cons, refRoot]
        show (pairWiresFrom (base + 2) ss.length).foldl
            (fun nd p => stepFr nd (p.1.eval a, p.2.eval a))
            (stepFr acc (a base, a (base + 1))) = _
        rw [hs0, hb0, stepFr_encB]
        refine ih (base + 2) bs _ hlen' (fun i hi => ?_) (fun i hi => ?_)
        · have h := hsib (i + 1) (by simp only [List.length_cons]; omega)
          rw [List.getD_cons_succ] at h
          rw [show base + 2 + 2 * i = base + 2 * (i + 1) from by ring]; exact h
        · have h := hbit (i + 1) (by simp only [List.length_cons]; omega)
          rw [List.getD_cons_succ] at h
          rw [show base + 2 + 2 * i + 1 = base + 2 * (i + 1) + 1 from by ring]; exact h

theorem bitBoolFrom_holds (a : Assignment) :
    ∀ (base d : ℕ), (∀ i, i < d → a (base + 2 * i + 1) = 0 ∨ a (base + 2 * i + 1) = 1) →
      ∀ p ∈ bitBoolFrom base d, p.1.eval a = p.2.eval a
  | _, 0, _, _, hp => absurd hp (by simp [bitBoolFrom])
  | base, d + 1, hbool, p, hp => by
      rw [bitBoolFrom, List.mem_cons] at hp
      rcases hp with rfl | hp
      · have h0 := hbool 0 (by omega)
        show a (base + 1) * a (base + 1) = a (base + 1)
        rcases h0 with h | h <;> rw [show base + 2 * 0 + 1 = base + 1 from rfl] at h <;>
          rw [h] <;> ring
      · exact bitBoolFrom_holds a (base + 2) d
          (fun i hi => by
            have := hbool (i + 1) (by omega); rw [show base + 2 * (i + 1) + 1
              = base + 2 + 2 * i + 1 from by ring] at this; exact this) p hp

/-- The honest input fill: leaf at `0`, root at `1`, siblings at even slots, path bits
(as `0/1`) at odd slots. The Poseidon internals are filled by `solveChain`. -/
def inAsg (leaf root : Fr) (sibs : List Fr) (bits : List Bool) : Assignment := fun v =>
  if v = 0 then leaf
  else if v = 1 then root
  else if v % 2 = 0 then sibs.getD ((v - 2) / 2) 0
  else encB (bits.getD ((v - 3) / 2) false)

theorem inAsg_sib (leaf root : Fr) (sibs : List Fr) (bits : List Bool) (i : ℕ) :
    inAsg leaf root sibs bits (2 + 2 * i) = sibs.getD i 0 := by
  have hne0 : ¬ (2 + 2 * i = 0) := by omega
  have hne1 : ¬ (2 + 2 * i = 1) := by omega
  have hmod : (2 + 2 * i) % 2 = 0 := by omega
  have hidx : (2 + 2 * i - 2) / 2 = i := by omega
  simp only [inAsg, if_neg hne0, if_neg hne1, if_pos hmod, hidx]

theorem inAsg_bit (leaf root : Fr) (sibs : List Fr) (bits : List Bool) (i : ℕ) :
    inAsg leaf root sibs bits (2 + 2 * i + 1) = encB (bits.getD i false) := by
  have hne0 : ¬ (2 + 2 * i + 1 = 0) := by omega
  have hne1 : ¬ (2 + 2 * i + 1 = 1) := by omega
  have hmod : ¬ ((2 + 2 * i + 1) % 2 = 0) := by omega
  have hidx : (2 + 2 * i + 1 - 3) / 2 = i := by omega
  simp only [inAsg, if_neg hne0, if_neg hne1, if_neg hmod, hidx]

/-- The path builder run at the canonical layout (counter starts past the input region). -/
def pathRun (d : ℕ) : Wire × (ℕ × List (Wire × Wire)) :=
  pathW (.var 0) (pairWires d) (2 + 2 * d, [])

/-- **The path opening circuit** — booleanity asserts, the `compressW` chain, and the
`finalNode = root` assert. -/
def merklePathCircuit (d : ℕ) : Circuit :=
  ⟨bitBoolFrom 2 d ++ (pathRun d).2.2 ++ [((pathRun d).1, Wire.var 1)]⟩

/-- The emission package for the depth-`d` Merkle path opening. -/
def merklePathData (d : ℕ) : GnarkCircuitData :=
  { name         := "merkle_path_bn254_v1"
    publicInputs := [("leaf", 0), ("root", 1)]
    gadgets      := [⟨"VerifyMerklePathBn254", [0, 1]⟩]
    circuit      := merklePathCircuit d }

/-- **The honest witness** — inputs plus the solved Poseidon internals. -/
def pathAsg (d : ℕ) (leaf root : Fr) (sibs : List Fr) (bits : List Bool) : Assignment :=
  solveChain (inAsg leaf root sibs bits) (pathRun d).2.2

/-- The builder run's define-chain + forced denotation, at the concrete start state. -/
theorem pathRun_props (d : ℕ) :
    ∃ n', DefChain (2 + 2 * d) (pathRun d).2.2 n'
      ∧ ∀ a, (∀ p ∈ (pathRun d).2.2, p.1.eval a = p.2.eval a) →
          (pathRun d).1.eval a
            = (pairWires d).foldl (fun nd p => stepFr nd (p.1.eval a, p.2.eval a)) (a 0) := by
  have hn0 : wBelow (Wire.var 0) (2 + 2 * d) := show 0 < 2 + 2 * d by omega
  have hps : ∀ p ∈ pairWires d, wBelow p.1 (2 + 2 * d) ∧ wBelow p.2 (2 + 2 * d) :=
    pairWiresFrom_below (2 + 2 * d) 2 d (by omega)
  obtain ⟨x, n', new, heq, hdc, _, hforce⟩ :=
    pathW_emits (pairWires d) (Wire.var 0) hn0 hps (2 + 2 * d) [] le_rfl
  have hrun : pathRun d = (x, (n', new)) := by
    show pathW (Wire.var 0) (pairWires d) (2 + 2 * d, []) = (x, (n', new))
    rw [heq, List.nil_append]
  refine ⟨n', by rw [hrun]; exact hdc, fun a ha => ?_⟩
  rw [hrun] at ha ⊢
  exact hforce a ha

/-- **The frontend refinement**: the honest witness satisfies the path circuit IFF the
reference `refRoot` walk on the given leaf/siblings/bits reproduces the claimed root. -/
theorem merklePath_frontend (leaf root : Fr) (sibs : List Fr) (bits : List Bool)
    (hlen : sibs.length = bits.length) :
    (merklePathCircuit sibs.length).satisfied (pathAsg sibs.length leaf root sibs bits)
      ↔ refRoot leaf (sibs.zip bits) = root := by
  set a := pathAsg sibs.length leaf root sibs bits with ha
  obtain ⟨n', hdc, hforce⟩ := pathRun_props sibs.length
  -- The honest witness agrees with `inAsg` below the internal region.
  have hbelow : ∀ v, v < 2 + 2 * sibs.length → a v = inAsg leaf root sibs bits v := fun v hv =>
    solveChain_agree_below (pathRun sibs.length).2.2 (inAsg leaf root sibs bits) hdc v hv
  have hnew : ∀ p ∈ (pathRun sibs.length).2.2, p.1.eval a = p.2.eval a :=
    solveChain_sat (pathRun sibs.length).2.2 (inAsg leaf root sibs bits) hdc
  have h0 : a 0 = leaf := by rw [hbelow 0 (by omega)]; simp [inAsg]
  have h1 : a 1 = root := by rw [hbelow 1 (by omega)]; simp [inAsg]
  -- The walk denotation recomputes `refRoot`.
  have hwalk : (pathRun sibs.length).1.eval a = refRoot leaf (sibs.zip bits) := by
    rw [hforce a hnew, h0]
    exact foldl_pairWiresFrom_refRoot a sibs 2 bits leaf hlen
      (fun i hi => by rw [hbelow (2 + 2 * i) (by omega), inAsg_sib])
      (fun i hi => by rw [hbelow (2 + 2 * i + 1) (by omega), inAsg_bit])
  -- The booleanity asserts always hold on the honest (0/1) bit fill.
  have hbool : ∀ p ∈ bitBoolFrom 2 sibs.length, p.1.eval a = p.2.eval a :=
    bitBoolFrom_holds a 2 sibs.length fun i hi => by
      rw [hbelow (2 + 2 * i + 1) (by omega), inAsg_bit]; cases bits.getD i false <;> simp [encB]
  show (∀ p ∈ (merklePathCircuit sibs.length).asserts, p.1.eval a = p.2.eval a) ↔ _
  show (∀ p ∈ bitBoolFrom 2 sibs.length ++ (pathRun sibs.length).2.2
      ++ [((pathRun sibs.length).1, Wire.var 1)], p.1.eval a = p.2.eval a) ↔ _
  rw [List.forall_mem_append, List.forall_mem_append, List.forall_mem_singleton]
  constructor
  · rintro ⟨_, hr⟩
    rw [← hwalk, hr]; exact h1
  · intro hr
    refine ⟨⟨hbool, hnew⟩, ?_⟩
    show (pathRun sibs.length).1.eval a = Wire.eval (Wire.var 1) a
    rw [hwalk, hr]; exact h1.symm

/-- **`merkle_path_refines`** — the deliverable ∀-refinement, at the R1CS level the gnark
backend consumes: the lowered genuine R1CS of the emitted depth-`|sibs|` Merkle-path
opening, under the honest witness, is satisfied IFF the deployed `refRoot` walk
(bottom-up 2-to-1 `Poseidon2Fr.compress`) on the leaf/siblings/bits reproduces the claimed
root — for EVERY leaf, root, sibling list, and (length-matched) bit list. A tampered leaf,
a wrong sibling, a flipped bit, or a corrupted root all move `refRoot`, refuting `gHolds`. -/
theorem merkle_path_refines (leaf root : Fr) (sibs : List Fr) (bits : List Bool)
    (hlen : sibs.length = bits.length) :
    Dregg2.Circuit.Emit.GnarkVerifier.gHolds (merklePathData sibs.length)
        (pathAsg sibs.length leaf root sibs bits)
      ↔ refRoot leaf (sibs.zip bits) = root := by
  unfold Dregg2.Circuit.Emit.GnarkVerifier.gHolds
  rw [← R1csFr.gHolds]
  exact merklePath_frontend leaf root sibs bits hlen

/-- The same refinement at the EMITTED wire form (composing `emit_faithful`): the bytes the
JSON grammar renders denote exactly the deployed Merkle-path check. -/
theorem merkle_path_refines_emitted (leaf root : Fr) (sibs : List Fr) (bits : List Bool)
    (hlen : sibs.length = bits.length) :
    Dregg2.Circuit.Emit.GnarkVerifier.satisfiedEmitted
        (Dregg2.Circuit.Emit.GnarkVerifier.emit (merklePathData sibs.length))
        (pathAsg sibs.length leaf root sibs bits)
      ↔ refRoot leaf (sibs.zip bits) = root :=
  (Dregg2.Circuit.Emit.GnarkVerifier.emit_faithful (merklePathData sibs.length)
      (pathAsg sibs.length leaf root sibs bits)).symm.trans
    (merkle_path_refines leaf root sibs bits hlen)

#assert_axioms merklePath_frontend
#assert_axioms merkle_path_refines
#assert_axioms merkle_path_refines_emitted

/-! ## §6 KAT teeth — against the DEPLOYED Go/Rust gold vectors (both polarities).

These are executable `#guard`s (the ∀-theorems above subsume them for provability; the
guards pin that the reference twins reproduce the deployed gold values BIT-EXACTLY, and
that the refinement's right-hand predicate is genuinely TRUE on a good opening and FALSE on
every tamper — the non-vacuity witnesses for `merkle_path_refines`). -/

/-- `katLeafA` (fri_leaf_hash_kat_test.go): 8 canonical BabyBear limbs (`bbPm1 = p-1`). -/
def katLeafA : List Fr := [0, 1, 2013265920, 3, 4, 5, 6, 7]
/-- `katLeafB`. -/
def katLeafB : List Fr := [7, 6, 5, 4, 2013265920, 2, 1, 0]

/-- Rust MMCS leaf digest of `katLeafA` (`MultiField32PaddingFreeSponge`), pinned. -/
def katLeafADigest : Fr := 0x2ba8b0c66b63687cd86e4c52baa38aad9d1c2fcba9df2fb4deab1f69a9919101
/-- Rust MMCS leaf digest of `katLeafB`. -/
def katLeafBDigest : Fr := 0x1ebed07295259c9085b8735dab239495adeb8278b8994dca56e833b15f758307
/-- Real `MerkleTreeMmcs::commit` root of the 2×8 matrix `[leafA; leafB]`, cap 0. -/
def katMmcsRoot : Fr := 0x0cad604ef568e95b9030970fb98da86f70dd5fc1c3777829bb4f8fae3792db76
/-- Depth-4 `merkleBn254RefRoot` KAT root (merkle_bn254_test.go): leaf 7, siblings
`100..103`, bits `i % 2`. -/
def katPathRoot : Fr := 0x2bd9273ae1bb6e81433d70a9b80e26c9d9473c99fea81a860151b4110cf5f27d

-- The MMCS leaf hash twin reproduces the Rust digests bit-exactly (accept).
#guard leafHashRef katLeafA = katLeafADigest
#guard leafHashRef katLeafB = katLeafBDigest
-- Tampered leaf (limb 0: 0 → 1) — the leaf digest moves (Go's tampered-leaf canary).
#guard leafHashRef (1 :: katLeafA.tail) ≠ katLeafADigest
-- The 2-to-1 commit reproduces the real MerkleTreeMmcs root (accept) …
#guard compress (leafHashRef katLeafA) (leafHashRef katLeafB) = katMmcsRoot
-- … and equivalently as a 1-level `refRoot` path (leaf = leafA digest, sibling = leafB,
-- bit = false ⇒ `compress node sib`).
#guard refRoot (leafHashRef katLeafA) [(leafHashRef katLeafB, false)] = katMmcsRoot
-- Wrong sibling at the MMCS level — root moves (reject).
#guard refRoot (leafHashRef katLeafA) [(leafHashRef katLeafA, false)] ≠ katMmcsRoot

-- The depth-4 path twin reproduces the deployed gnark/Go root (accept).
#guard refRoot 7 [(100, false), (101, true), (102, false), (103, true)] = katPathRoot
-- Flipped bit (bits[2] : 0 → 1) — root moves (Go's `bits[2] ^= 1` canary; reject).
#guard refRoot 7 [(100, false), (101, true), (102, true), (103, true)] ≠ katPathRoot
-- Wrong sibling (102 → 999) — root moves (reject).
#guard refRoot 7 [(100, false), (101, true), (999, false), (103, true)] ≠ katPathRoot
-- Tampered leaf (7 → 8) — root moves (reject).
#guard refRoot 8 [(100, false), (101, true), (102, false), (103, true)] ≠ katPathRoot
-- CORRUPTED ROOT — the refinement's right-hand predicate is FALSE, so `gHolds` is FALSE:
-- the non-vacuity witness of the reject polarity of `merkle_path_refines`.
#guard ¬ (refRoot 7 [(100, false), (101, true), (102, false), (103, true)] = katPathRoot + 1)

/-! ## §7 The adversarial (soundness) face.

The honest-fill refinement above quantifies over `pathAsg`. The soundness face quantifies
over ANY witness: any assignment satisfying the depth-`d` path circuit has its claimed root
variable (`var 1`) EQUAL to the circuit's recomputed compression walk over its own leaf/
sibling/bit variables. So the prover cannot satisfy the circuit while claiming a root the
openings do not produce — the `Select`-mux walk is a deterministic function of the witness,
pinned to `var 1` by the final assert. (Turning each mux into the branch-selecting
`refRoot` step needs the bit boolean — the named Pratt/primality seam of `R1csFr`, forced
in-circuit by the `b·b = b` asserts, exactly the `CanonicityToy` posture.) -/

/-- **`merkle_path_sound`** — the adversarial soundness face, over EVERY witness (no honest
fill, no hypotheses beyond satisfaction). The claimed root variable `var 1` is forced to
equal the compression walk (`stepFr`: two `Select` muxes + `compress`) recomputed from the
witness's own leaf `var 0`, siblings `var (2+2i)`, and bit values `var (2+2i+1)`. -/
theorem merkle_path_sound (d : ℕ) (a : Assignment)
    (hsat : (merklePathCircuit d).satisfied a) :
    a 1 = (pairWires d).foldl
      (fun nd p => stepFr nd (p.1.eval a, p.2.eval a)) (a 0) := by
  obtain ⟨_, _, hforce⟩ := pathRun_props d
  have hsat' : ∀ p ∈ bitBoolFrom 2 d ++ (pathRun d).2.2
      ++ [((pathRun d).1, Wire.var 1)], p.1.eval a = p.2.eval a := hsat
  rw [List.forall_mem_append, List.forall_mem_append, List.forall_mem_singleton] at hsat'
  obtain ⟨⟨_, hnew⟩, hroot⟩ := hsat'
  -- `hroot : (pathRun d).1.eval a = (Wire.var 1).eval a`; `hforce` gives the walk.
  rw [show a 1 = (Wire.var 1).eval a from rfl, ← hroot, hforce a hnew]

#assert_axioms merkle_path_sound

end Dregg2.Circuit.Emit.GnarkVerifier.Merkle
