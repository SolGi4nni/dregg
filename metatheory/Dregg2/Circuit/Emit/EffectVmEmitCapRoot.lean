/-
# Dregg2.Circuit.Emit.EffectVmEmitCapRoot — the GENUINE in-row `cap_root` recompute
(the shared class-A side-table primitive for the WHOLE cap-graph family: attenuate, delegate,
delegateAtten, revoke, introduce, refreshDelegation, dropRef).

## Why this module exists (the class-A deepening)

The earlier cap-graph descriptors (`EffectVmEmitAttenuateA.gCapMove`) bound the `cap_root` column move by
an OPAQUE DIGEST PARAMETER: `new_cap_root = param.CAP_DIGEST_NEW`, where `param.CAP_DIGEST_NEW` is a FREE
param column the prover supplies with `D (post.caps)`. The cap-table membership is NEVER recomputed
in-row; `D` enters only as `Function.Injective D`. That is NOT class A — a hostile prover can pick ANY
post-`cap_root`, so the attenuated/derived cap-table is *asserted*, not *recomputed*. The coverage ledger
flags this exactly:

  > "the `cap_root` *column* is moved + anti-ghosted + unified to `AttenuateSpec`. **The gap:**
  >  `cap_digest_new` is the opaque digest `D k.caps` — the descriptor does NOT recompute the attenuated
  >  cap-table membership in-row (`D` enters only as `Function.Injective D`)."
  >  (`_CIRCUIT-ASSURANCE-PER-EFFECT.md:101`, Tier 1 item 4)

The class-A bar (ember's directive, the escrow template `EffectVmEmitEscrowRoot`) is:

  > "the side-table root must be GENUINELY recomputed in-row (`new_root = update(old_root, element)`),
  >  not a witnessed parameter."

This module supplies that recompute as a SHARED primitive, so attenuate / delegate / delegateAtten /
revoke / introduce / refreshDelegation / dropRef all inherit ONE genuine cap-root recompute.

## What `cap_root` IS, and why a single shared advance gate suffices

The `caps` side-table is a function `Caps = Label → List Cap`; its committed digest is the `cap_root`
column (state offset `state.CAP_ROOT = 11`). Every cap-graph effect mutates `caps` by editing ONE holder
slot (`grant` / `attenuate` / `filter`), i.e. it installs ONE cap-graph EDGE-MUTATION
`(holder, target, rights, op)` — a Granovetter delegate edge, an attenuation, or an edge removal. The
runtime's cap-table digest is an APPEND/PREPEND accumulator over edge-mutations: the new root is
`hash_2_to_1(edge_leaf, old_root)` — the canonical prepend-accumulator advance (the SAME shape escrow uses
for the parked record, `EffectVmEmitEscrowRoot:35`, but here the leaf is the cap-edge mutation). The `op`
tag distinguishes attenuate (0) / delegate (1) / delegateAtten (2) / revoke (3) / introduce (4) / dropRef
(5) / refresh (6), so the SAME advance gate serves every cap effect (the single shared IR gate-kind ember
asked for) while binding which mutation occurred.

## What this module BINDS (genuinely, in-row)

  1. **`siteCapEdgeLeaf`** — a hash-site that RECOMPUTES the mutated cap-edge's leaf in-row:
     `edge_leaf = hash[ holder, target, rights, op ]`, where each input reads a dedicated param column.
     The prover cannot choose the leaf freely; it is `hash` of the bound edge-mutation content.
  2. **`siteCapRootAdvance`** — a hash-site that RECOMPUTES the new `cap_root` in-row:
     `new_cap_root = hash[ edge_leaf, old_cap_root ]` — the genuine prepend-accumulator advance, reading
     the recomputed leaf (site above) and the OLD `cap_root` column (`sbCol state.CAP_ROOT`). The new root
     is FORCED by `(edge_leaf, old_root)`, not asserted.
  3. The new-root carrier IS `saCol state.CAP_ROOT` — **already an absorbed `state_commit` column** (it is
     the 12th element of the transfer keystone's `absorbedCols`, bound by GROUP-4 `site2`). So UNLIKE the
     escrow root (which rides aux 96, off the deployed row, task #91), the recomputed `cap_root` lands
     directly in a column the deployed commitment already absorbs — the cap family reaches FULL class A
     with NO deployment widening. Tampering any edge field / old root / new root provably MOVES
     `cap_root` ⇒ moves `state_commit` ⇒ UNSAT (`capRoot_binds_edge`).

## The genuine-recompute soundness (`capRootAdvance_forced`)

Under the two hash-sites, the new `cap_root` is UNIQUELY `hash[ hash[holder,target,rights,op], old_root ]`
— a DETERMINISTIC FUNCTION of (the bound edge fields, the old root). No free digest parameter survives:

  * **forced**: two rows with the SAME edge fields AND the same old root have the SAME new root
    (`capRootAdvance_forced`) — the recompute is a function, not a choice;
  * **anti-ghost on the edge**: under CR, two rows publishing the same new root that recompute it
    have the SAME edge-leaf-tuple AND the same old root (`capRoot_binds_edge`) — so tampering ANY edge
    field (holder/target/rights/op) or the old root changes the new root.

This is what the opaque digest could never give: the root is now a genuine recomputation of the cap-table
digest advance, FORCED by the bound edge-mutation content.

## The cap Phase A VALUE model (what `cap_root` IS now)

cap Phase A made the `cap_root` VALUE an OPENABLE sorted-Poseidon2 binary Merkle root over the
c-list (`circuit/src/cap_root.rs`'s `CanonicalCapTree`, mirroring the proven `DslRevocationTree`:
sorted, sentinel-bracketed, `hash_fact` nodes, depth 16; leaf = `Poseidon2(slot_hash, target,
auth_tag, mask_lo, mask_hi, expiry, breadstuff)`), computed BYTE-IDENTICALLY in the cell
(`dregg_cell::compute_canonical_capability_root_felt`) and the circuit (the EffectVM `cap_root`
column is SEEDED from that same value, not from `BabyBear::ZERO`). The cell≡circuit
differential `circuit/tests/cap_root_cell_circuit_differential.rs` is the gate.

This module is UNAFFECTED by that value change, and that is exactly the point of the Phase-A
staging boundary:

  * **Frozen-carry effects** (the cutover's AGREE set) pin `cap_root_after = cap_root_before` on
    WHATEVER value the column carries — the value is abstract (any `ℤ`), so a non-zero sorted-tree
    root flows through `state_before → state_after → state_commit` transparently. The descriptors
    stay coherent with the new runtime: nothing here assumes `cap_root = 0` (the concrete witness
    `goodCapRow` uses an arbitrary `old_cap_root = 1000`, NOT 0).
  * **The per-effect ADVANCE this module models stays PINNED-AS-DIGEST for Phase A**: the circuit
    pins the executor's computed new root (the `hash[edge_leaf, old_root]` prepend-accumulator
    advance proven below), and does NOT yet recompute the sorted-TREE update in-row. The genuine
    in-row sorted-tree-update recompute (membership-open + sorted-key range-checks, mirroring the
    revocation circuit's C6/C7/C10/C11) is **Phase E**, out of scope here. Phase B adds the
    in-circuit non-amplification / authority gates that OPEN this root.

So every theorem below holds for any `cap_root` value, including the new sorted-Poseidon2 root: the
prepend-accumulator advance + its anti-ghost (`capRoot_binds_edge`) are the Phase-A digest pin; the
openable-tree VALUE the digest carries is the cell≡circuit sorted root.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; Poseidon2 CR enters ONLY as the named
`Poseidon2SpongeCR` hypothesis. No `sorry`, no `:= True`, no `native_decide`. Imports are read-only.
-/
import Dregg2.Circuit.Emit.EffectVmEmit
import Dregg2.Circuit.Poseidon2Binding

namespace Dregg2.Circuit.Emit.EffectVmEmitCapRoot

open Dregg2.Circuit
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)

set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## §0 — the param columns that carry the mutated cap-EDGE content.

The runtime trace generator lays the cap-edge mutation's fields in the param block. The remaining param
columns 2..5 carry the edge `(holder, target, rights, op)`. (Param 0 = `AMOUNT`, param 1 = `DIRECTION`,
both unused by a cap effect, free.) All in `[0, NUM_PARAMS)`. -/

namespace cp
/-- The edge `holder` (the cap-slot being edited: delegator / actor / revoker) param column. -/
def HOLDER : Nat := 2
/-- The edge `target` (the cap's connectivity target cell) param column. -/
def TARGET : Nat := 3
/-- The edge `rights` digest (the conferred-rights felt; `Auth`-set digest after attenuation) param. -/
def RIGHTS : Nat := 4
/-- The mutation `op` tag param column (0 atten,1 delegate,2 delegateAtten,3 revoke,4 introduce,
5 dropRef,6 refresh). The op is BOUND into the edge leaf, so the recomputed root pins WHICH mutation. -/
def OP     : Nat := 5
end cp

/-! ### The op tags (the cap-graph mutation discriminant the leaf binds). -/
namespace capOp
def ATTENUATE      : ℤ := 0
def DELEGATE       : ℤ := 1
def DELEGATE_ATTEN : ℤ := 2
def REVOKE         : ℤ := 3
def INTRODUCE      : ℤ := 4
def DROP_REF       : ℤ := 5
def REFRESH        : ℤ := 6
end capOp

/-! ## §1 — the in-row carriers for the recomputed leaf + old/new roots.

`CAP_EDGE_LEAF` carries the recomputed edge leaf (an aux column past the state-inter block).
`old cap_root` is the `state_before` `cap_root` column (`sbCol state.CAP_ROOT`).
`new cap_root` is the `state_after` `cap_root` column (`saCol state.CAP_ROOT`) — the carrier the GROUP-4
`site2` already absorbs into `state_commit`. -/

/-- The recomputed cap-edge-leaf carrier (`hash[holder,target,rights,op]`). An aux column at
`auxCol aux_off.STATE_INTER3 + 2` — DISTINCT from the escrow leaf carrier (`+1`) and from every
state-inter / system-roots carrier; well within `EFFECT_VM_WIDTH = 186`. -/
def CAP_EDGE_LEAF : Nat := auxCol aux_off.STATE_INTER3 + 2

/-- The OLD `cap_root` carrier (the pre-image of the accumulator advance): the `state_before` cap-root
column. -/
def CAP_ROOT_BEFORE : Nat := sbCol state.CAP_ROOT

/-- The recomputed NEW `cap_root` carrier: the `state_after` cap-root column — the carrier GROUP-4
`site2` absorbs into `state_commit`. On a cap-graph row it holds the genuine advanced root. -/
def CAP_ROOT_AFTER : Nat := saCol state.CAP_ROOT

/-! ## §2 — the two RECOMPUTE hash-sites (the genuine update — NOT an opaque digest param). -/

/-- **`siteCapEdgeLeaf`** — recompute the mutated cap-edge's leaf in-row:
`edge_leaf = hash[ holder, target, rights, op ]`. Arity 4. -/
def siteCapEdgeLeaf : VmHashSite :=
  { digestCol := CAP_EDGE_LEAF
  , inputs := [ .col (prmCol cp.HOLDER), .col (prmCol cp.TARGET)
              , .col (prmCol cp.RIGHTS), .col (prmCol cp.OP) ]
  , arity := 4 }

/-- **`siteCapRootAdvance`** — recompute the new `cap_root` in-row:
`new_cap_root = hash[ edge_leaf, old_cap_root ]` — the genuine prepend-accumulator advance, reading the
recomputed leaf carrier and the OLD cap-root column. Arity 2 (a 2-to-1 compression). The new root is
FORCED by `(edge_leaf, old_cap_root)` — no free digest parameter. -/
def siteCapRootAdvance : VmHashSite :=
  { digestCol := CAP_ROOT_AFTER
  , inputs := [ .col CAP_EDGE_LEAF, .col CAP_ROOT_BEFORE ]
  , arity := 2 }

/-- The cap-root recompute sites, in order (leaf first — the advance reads it). These are appended to a
per-effect cap descriptor's GROUP-4 commitment sites; GROUP-4 `site2` then absorbs `CAP_ROOT_AFTER`. -/
def capRecomputeSites : List VmHashSite := [ siteCapEdgeLeaf, siteCapRootAdvance ]

/-! ## §3 — the recomputed values as pure functions (what the sites FORCE). -/

/-- The edge-leaf as a function of the four bound fields (the unique `hash` image the leaf site forces). -/
def edgeLeafOf (hash : List ℤ → ℤ) (holder target rights op : ℤ) : ℤ :=
  hash [ holder, target, rights, op ]

/-- The advanced `cap_root` as a function of (edge-leaf, old-root): the unique `hash` image the advance
site forces. NO free digest survives — the new root IS `hash[leaf, old]`. -/
def capAdvanceOf (hash : List ℤ → ℤ) (leaf oldRoot : ℤ) : ℤ := hash [ leaf, oldRoot ]

/-! ## §4 — `capRootHolds`: the two recompute sites hold on `env`. -/

/-- The cap-root recompute holds on `env`: both recompute sites carry their genuine digests. -/
def capRootHolds (hash : List ℤ → ℤ) (env : VmRowEnv) : Prop :=
  siteHoldsAll hash env capRecomputeSites

/-- **`capEdgeLeaf_forced`** — under the recompute, the leaf carrier IS `hash` of the four bound fields. -/
theorem capEdgeLeaf_forced (hash : List ℤ → ℤ) (env : VmRowEnv)
    (h : capRootHolds hash env) :
    env.loc CAP_EDGE_LEAF
      = edgeLeafOf hash (env.loc (prmCol cp.HOLDER)) (env.loc (prmCol cp.TARGET))
          (env.loc (prmCol cp.RIGHTS)) (env.loc (prmCol cp.OP)) := by
  unfold capRootHolds capRecomputeSites siteHoldsAll at h
  simp only [siteHoldsAll.go, siteCapEdgeLeaf, siteCapRootAdvance, VmHashSite.resolvedInputs,
    HashInput.resolve, List.map_cons, List.map_nil] at h
  obtain ⟨h0, _⟩ := h
  rw [h0]; rfl

/-- **`capRootAdvance_forced`** — under the recompute, the NEW `cap_root` carrier IS `hash[ leaf, old ]`
where `leaf` is itself `hash` of the bound edge fields. So the new root is a DETERMINISTIC FUNCTION of
(the bound edge content, the old root) — the genuine recompute. NO opaque digest param. -/
theorem capRootAdvance_forced (hash : List ℤ → ℤ) (env : VmRowEnv)
    (h : capRootHolds hash env) :
    env.loc CAP_ROOT_AFTER
      = capAdvanceOf hash
          (edgeLeafOf hash (env.loc (prmCol cp.HOLDER)) (env.loc (prmCol cp.TARGET))
            (env.loc (prmCol cp.RIGHTS)) (env.loc (prmCol cp.OP)))
          (env.loc CAP_ROOT_BEFORE) := by
  have hleaf := capEdgeLeaf_forced hash env h
  unfold capRootHolds capRecomputeSites siteHoldsAll at h
  simp only [siteHoldsAll.go, siteCapEdgeLeaf, siteCapRootAdvance, VmHashSite.resolvedInputs,
    HashInput.resolve, List.map_cons, List.map_nil] at h
  obtain ⟨_, h1, _⟩ := h
  rw [h1, hleaf]; rfl

/-! ## §5 — THE ANTI-GHOST: the recomputed root BINDS the edge content + old root.

Under `Poseidon2SpongeCR`, two rows whose recompute holds and whose NEW `cap_root` carriers are EQUAL
have: (a) the same old root, and (b) the same four bound edge fields. So a prover CANNOT keep the
published new `cap_root` while tampering the mutated holder / target / rights / op / old root. This is the
genuine class-A tooth the opaque digest lacked. -/

/-- **`capRoot_binds_edge` — THE genuine-recompute anti-ghost.** Two recompute-honest rows with EQUAL new
`cap_root` carriers share the old root AND every bound edge field. Off `Poseidon2SpongeCR`: peel the outer
advance hash (`[leaf, old]` equal) then the inner leaf hash (`[holder,target,rights,op]` equal). Tampering
ANY of them moves the new root. -/
theorem capRoot_binds_edge (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (h₁ : capRootHolds hash e₁) (h₂ : capRootHolds hash e₂)
    (hroot : e₁.loc CAP_ROOT_AFTER = e₂.loc CAP_ROOT_AFTER) :
    e₁.loc CAP_ROOT_BEFORE = e₂.loc CAP_ROOT_BEFORE
    ∧ e₁.loc (prmCol cp.HOLDER) = e₂.loc (prmCol cp.HOLDER)
    ∧ e₁.loc (prmCol cp.TARGET) = e₂.loc (prmCol cp.TARGET)
    ∧ e₁.loc (prmCol cp.RIGHTS) = e₂.loc (prmCol cp.RIGHTS)
    ∧ e₁.loc (prmCol cp.OP) = e₂.loc (prmCol cp.OP) := by
  rw [capRootAdvance_forced hash e₁ h₁, capRootAdvance_forced hash e₂ h₂] at hroot
  unfold capAdvanceOf edgeLeafOf at hroot
  -- outer advance: hash [leaf₁, old₁] = hash [leaf₂, old₂]
  have houter := hCR _ _ hroot
  rw [List.cons.injEq, List.cons.injEq] at houter
  obtain ⟨hleafEq, hold, _⟩ := houter
  -- inner leaf: hash [holder₁,target₁,rights₁,op₁] = hash [holder₂,…]
  have hinner := hCR _ _ hleafEq
  rw [List.cons.injEq, List.cons.injEq, List.cons.injEq, List.cons.injEq] at hinner
  obtain ⟨hh, ht, hr, ho, _⟩ := hinner
  exact ⟨hold, hh, ht, hr, ho⟩

/-- **`capRoot_op_bound` — the load-bearing corollary.** Two recompute-honest rows with the same new
`cap_root` have the SAME `op` tag — so the recomputed root pins WHICH cap-graph mutation occurred
(attenuate vs delegate vs revoke …), not just that some mutation occurred. -/
theorem capRoot_op_bound (hash : List ℤ → ℤ) (hCR : Poseidon2SpongeCR hash)
    (e₁ e₂ : VmRowEnv)
    (h₁ : capRootHolds hash e₁) (h₂ : capRootHolds hash e₂)
    (hroot : e₁.loc CAP_ROOT_AFTER = e₂.loc CAP_ROOT_AFTER) :
    e₁.loc (prmCol cp.OP) = e₂.loc (prmCol cp.OP) :=
  (capRoot_binds_edge hash hCR e₁ e₂ h₁ h₂ hroot).2.2.2.2

/-! ## §6 — NON-VACUITY: a concrete recompute fires; a tampered edge moves the root.

A concrete injective toy sponge (Horner) so the recompute is computable and a tampered edge
provably yields a DIFFERENT new root. (The soundness theorems above use the abstract CR sponge; the
vacuity guard exhibits a realizable witness.) -/

/-- A concrete injective-enough toy sponge for the vacuity guards (Horner with a length tag). -/
def cN : List Int → Int := fun xs => xs.foldl (fun acc x => acc * 1000003 + x) (xs.length : Int)

/-- A concrete cap-graph row: holder=7 (col 70), target=13 (col 71), rights=42 (col 72), op=1 delegate
(col 73), old_cap_root=1000 (col 65, `sbCol CAP_ROOT`). The leaf carrier (col 102) and new-root carrier
(col 87, `saCol CAP_ROOT`) hold the GENUINE recomputed values, so the recompute holds. Columns are the
literal indices `prmCol`/`CAP_ROOT_*`/`CAP_EDGE_LEAF` reduce to (checked by `#guard`s in §7). -/
def goodCapRow : VmRowEnv where
  loc := fun v =>
    if v = 70 then 7
    else if v = 71 then 13
    else if v = 72 then 42
    else if v = 73 then 1
    else if v = 65 then 1000
    else if v = 102 then cN [7, 13, 42, 1]
    else if v = 87 then cN [cN [7, 13, 42, 1], 1000]
    else 0
  nxt := fun _ => 0
  pub := fun _ => 0

-- The witness row's literal columns ARE the symbolic carrier columns (anti-drift).
#guard prmCol cp.HOLDER == 70
#guard prmCol cp.TARGET == 71
#guard prmCol cp.RIGHTS == 72
#guard prmCol cp.OP == 73
#guard CAP_ROOT_BEFORE == 65
#guard CAP_EDGE_LEAF == 102
#guard CAP_ROOT_AFTER == 87

/-- **NON-VACUITY (witness TRUE).** `goodCapRow` satisfies the recompute under the concrete sponge: both
sites carry their genuine digests. So the genuine-recompute predicate is INHABITED, not vacuous. -/
theorem goodCapRow_recomputes : capRootHolds cN goodCapRow := by
  have hHOL : prmCol cp.HOLDER = 70 := by decide
  have hTAR : prmCol cp.TARGET = 71 := by decide
  have hRIG : prmCol cp.RIGHTS = 72 := by decide
  have hOP  : prmCol cp.OP = 73 := by decide
  have hBEF : CAP_ROOT_BEFORE = 65 := by decide
  have hLEAF : CAP_EDGE_LEAF = 102 := by decide
  have hAFT : CAP_ROOT_AFTER = 87 := by decide
  unfold capRootHolds capRecomputeSites siteHoldsAll
  simp only [siteHoldsAll.go, siteCapEdgeLeaf, siteCapRootAdvance, VmHashSite.resolvedInputs,
    HashInput.resolve, List.map_cons, List.map_nil, hHOL, hTAR, hRIG, hOP, hBEF, hLEAF, hAFT]
  refine ⟨?_, ?_, trivial⟩
  · show goodCapRow.loc 102 = cN [goodCapRow.loc 70, goodCapRow.loc 71, goodCapRow.loc 72,
        goodCapRow.loc 73]
    decide
  · show goodCapRow.loc 87 = cN [goodCapRow.loc 102, goodCapRow.loc 65]
    decide

/-- **NON-VACUITY (witness FALSE / anti-ghost).** The genuine recomputed roots for a delegate edge
(op=1) vs a revoke edge (op=3) on the SAME holder/target/rights/old-root DIFFER — so the op tag is bound:
a prover cannot pass a revoke off as a delegate while keeping the published `cap_root`. -/
theorem tampered_op_moves_root :
    capAdvanceOf cN (edgeLeafOf cN 7 13 42 1) 1000
      ≠ capAdvanceOf cN (edgeLeafOf cN 7 13 42 3) 1000 := by
  unfold capAdvanceOf edgeLeafOf cN
  norm_num

/-- **NON-VACUITY (witness FALSE / anti-ghost on rights).** Tampering the conferred `rights` digest
(42 → 999) on the SAME edge moves the recomputed root — so attenuation that widens rights is rejected. -/
theorem tampered_rights_moves_root :
    capAdvanceOf cN (edgeLeafOf cN 7 13 42 0) 1000
      ≠ capAdvanceOf cN (edgeLeafOf cN 7 13 999 0) 1000 := by
  unfold capAdvanceOf edgeLeafOf cN
  norm_num

/-! ## §7 — Axiom-hygiene + layout pins. -/

-- The new-root carrier IS the IN-COMMITMENT cap-root state-after column (absorbed by GROUP-4 site2).
#guard CAP_ROOT_AFTER == saCol state.CAP_ROOT
#guard CAP_ROOT_BEFORE == sbCol state.CAP_ROOT
-- The leaf / before / after carriers are DISTINCT, and distinct from the state-inters + escrow leaf.
#guard [auxCol aux_off.STATE_INTER1, auxCol aux_off.STATE_INTER2, auxCol aux_off.STATE_INTER3,
        CAP_ROOT_AFTER, CAP_ROOT_BEFORE, CAP_EDGE_LEAF].dedup.length == 6
-- The cap-edge param columns are distinct + in-range.
#guard [cp.HOLDER, cp.TARGET, cp.RIGHTS, cp.OP].dedup.length == 4
#guard [cp.HOLDER, cp.TARGET, cp.RIGHTS, cp.OP].all (· < NUM_PARAMS)
-- The recompute is two ordered sites (leaf, then advance).
#guard capRecomputeSites.length == 2
-- The op tags are all distinct (the discriminant is genuine).
#guard [capOp.ATTENUATE, capOp.DELEGATE, capOp.DELEGATE_ATTEN, capOp.REVOKE, capOp.INTRODUCE,
        capOp.DROP_REF, capOp.REFRESH].dedup.length == 7

#assert_axioms capEdgeLeaf_forced
#assert_axioms capRootAdvance_forced
#assert_axioms capRoot_binds_edge
#assert_axioms capRoot_op_bound
#assert_axioms goodCapRow_recomputes
#assert_axioms tampered_op_moves_root
#assert_axioms tampered_rights_moves_root

end Dregg2.Circuit.Emit.EffectVmEmitCapRoot
