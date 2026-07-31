/-
# Dregg2.Circuit.Emit.TurnAuthCapOpenWeld — the STAGED wiring of in-AIR authorization onto the
# deployed cap-open turn-bound member.

**Lean-authored AIR.** Both halves are `def`-generators: the cap-open crown
(`CapOpenEmit`/`CapOpenTurnPins`) and the authorization gadget (`TurnAuthLamportEmit`). This module
only COMPOSES them and states what the composition forces. Rust constructs nothing.

## Why the two halves belong together

The crown and the signature answer DIFFERENT questions, and each is useless alone:

  * the depth-16 cap crown answers **WHICH capability, and what does it permit** — a real in-AIR
    Merkle membership against the committed cap root, with a genuine submask facet gate;
  * it CANNOT answer **WHO invoked it**, because a Merkle path is PUBLIC data: anyone who can read
    the cap root can produce a membership witness for any leaf in it. That is why `auth_tag` pinned
    to `SIGNATURE_AUTH_TAG = 1` is a TIER BYTE and not a signature check, and why routing owner
    effects through the crown would have moved the hole rather than closed it;
  * the Lamport verify answers **WHO** — the prover exhibits Poseidon2 preimages of the public-key
    halves selected by the signed message, under a public key folded to a PUBLISHED authority root;
  * it CANNOT answer **which capability**, because a signature says nothing about the cap tree.

Composed on one descriptor, over one turn identity, they say: *the holder of this authority root
asked for THIS turn, and a capability in the committed cap tree permits it.*

## The three free welds — and the handoff this module answers

Measured earlier today on the committed artifact: `transferCapOpenTBVmDescriptor2R24` pinned col 894
→ PI 46 (`src`), col 928 → PI 47 (`actor`), col 929 → PI 48 (`dst`), and across all 397 constraints
col 928 appeared in exactly ONE and col 929 in exactly ONE — their own `pi_binding`. `src` was the
only genuinely welded one (`targetBindGate` chains it to the opened leaf and thence to the committed
cap root).

⚑ **The `actor`/`dst` pins have since been DELETED** by the unforced-pin subtraction (`CapOpenTurnPins`
§"WHAT WAS REMOVED, 2026-07-30"), which is the right call for a pin that publishes a prover-chosen
felt: *"A weld that publishes a PROVER-CHOSEN felt for who acted and who received is worse than no
weld, because its name says otherwise."* That module ends by naming the successor explicitly:

> The real actor binding … is the authorization-in-AIR lane's work, and **it will publish `actor`
> when it can also force it.**

This module is that. It re-introduces `actor` and `dst`, publishes them to public inputs, **and
forces them** — they are `turnIn` of `turnDigestLookup`, whose 8-felt output the signed message bits
recompose, so moving either moves the signed message and the witness must then contain a Lamport
preimage the owner never revealed. The measurement is not a claim: `unforcedPins` — the very census
that condemned the old pins — returns EMPTY on this descriptor, kernel-checked in §3.

## STAGED — this changes no deployed member yet

`authWeldedCapOpenTB` is the descriptor the convergence re-emit turns on. It is not referenced by
`EmitByName`/`EmitWideRegistryProbe`, so no registry member changes shape, no `registry_fp` moves,
and no VK rotates because of this file. What the re-emit must do is spelled out in
`AUTH_WELD_REEMIT_NOTE` below.
-/
import Dregg2.Circuit.Emit.CapOpenTurnPins
import Dregg2.Circuit.Emit.UnforcedPiPins
import Dregg2.Circuit.Emit.TurnAuthLamportEmit

namespace Dregg2.Circuit.Emit.TurnAuthCapOpenWeld

open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2)
open Dregg2.Circuit.Emit.CapOpenEmit (capOpenCols CAP_OPEN_SPAN effCapOpenV3)
open Dregg2.Circuit.Emit.CapOpenTurnPins (effCapOpenV3TB)
open Dregg2.Circuit.Emit.TurnAuthLamportEmit (withTurnAuth NB AUTH_SPAN ELL W)
open Dregg2.Circuit.Emit.UnforcedPiPins (unforcedPins unforcedPiSlots pinsOf)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRow)

set_option autoImplicit false

/-! ## §1 — re-introducing `actor` and `dst`, this time FORCED.

The two columns ride immediately past the turn-bound cap-open's width; the authorization gadget
rides past them. Both are `turnIn` of the turn-digest absorb, so both are read by a non-pin
constraint — which is exactly the property `unforcedPins` tests for. -/

/-- The turn's `actor` column: the first free column past the turn-bound cap-open. -/
def authActorCol (d : EffectVmDescriptor2) : Nat := d.traceWidth
/-- The turn's `dst` column. -/
def authDstCol (d : EffectVmDescriptor2) : Nat := d.traceWidth + 1

/-- `d` widened by the two turn-identity columns and their public-input pins. The pins are legitimate
here — and only here — because §2 routes both columns into the signed turn digest. -/
def withActorDst (d : EffectVmDescriptor2) : EffectVmDescriptor2 :=
  { d with
    traceWidth  := d.traceWidth + 2
    piCount     := d.piCount + 2
    constraints := d.constraints
      ++ [ .base (.piBinding VmRow.first (authActorCol d) d.piCount)
         , .base (.piBinding VmRow.first (authDstCol d) (d.piCount + 1)) ] }

/-- The turn identity the signature covers: the cap-open's own `src` (welded to the opened leaf's
target by `targetBindGate`), plus the re-introduced `actor` and `dst`. -/
def turnIdentityCols (base : EffectVmDescriptor2) (name : String) (n : Nat) : List Nat :=
  let d := effCapOpenV3TB base name n
  [(capOpenCols base.traceWidth).src, authActorCol d, authDstCol d]

/-! ## §2 — the composed descriptor. -/

/-- **`authWeldedCapOpenTB base name n nb`** — the deployed cap-open turn-bound descriptor, plus
`actor`/`dst` published, plus in-AIR authorization over all three. Every existing cap-open
constraint is preserved verbatim, so every crown keystone lifts unchanged. -/
def authWeldedCapOpenTB (base : EffectVmDescriptor2) (name : String) (n nb : Nat) :
    EffectVmDescriptor2 :=
  withTurnAuth (withActorDst (effCapOpenV3TB base name n)) nb (turnIdentityCols base name n)

/-- Every constraint of the turn-bound cap-open survives the weld: the crown is KEPT, not replaced.
So `effCapOpenV3TB_authorizes` (the membership leg) and `effCapOpenV3TB_hsrc` lift verbatim, and the
signature is an ADDITION to the capability check, never a substitute for it. -/
theorem authWelded_keeps_every_capopen_constraint (base : EffectVmDescriptor2) (name : String)
    (n nb : Nat) (c : Dregg2.Circuit.DescriptorIR2.VmConstraint2)
    (hc : c ∈ (effCapOpenV3TB base name n).constraints) :
    c ∈ (authWeldedCapOpenTB base name n nb).constraints :=
  List.mem_append_left _ (List.mem_append_left _ hc)

/-- The weld's shape, as arithmetic on the host descriptor. -/
theorem authWelded_shape (base : EffectVmDescriptor2) (name : String) (n nb : Nat) :
    (authWeldedCapOpenTB base name n nb).traceWidth
        = (effCapOpenV3TB base name n).traceWidth + 2 + AUTH_SPAN nb
      ∧ (authWeldedCapOpenTB base name n nb).piCount
        = (effCapOpenV3TB base name n).piCount + 2 + W :=
  ⟨rfl, rfl⟩

/-- The v2 graduation invariant survives: no v1 `ranges`/`hashSites` carrier is introduced, so
`check_descriptor2` still accepts (it refuses any v2 descriptor carrying either). -/
theorem authWelded_stays_graduated (base : EffectVmDescriptor2) (name : String) (n nb : Nat)
    (hr : base.ranges = []) (hh : base.hashSites = []) :
    (authWeldedCapOpenTB base name n nb).ranges = []
      ∧ (authWeldedCapOpenTB base name n nb).hashSites = [] := by
  exact ⟨hr, hh⟩

#assert_axioms authWelded_keeps_every_capopen_constraint
#assert_axioms authWelded_shape
#assert_axioms authWelded_stays_graduated

/-! ## §2.5 — ⚑ THE MEASUREMENT: `unforcedPins` returns EMPTY.

`UnforcedPiPins.unforcedPins` is the census that condemned the old `actor`/`dst` pins: it returns
every pin whose column NO non-pin constraint, hash site or range tooth reads. Running it on this
descriptor is the machine-checked closure of the free-weld item — the pins are not merely
*intended* to be forced, the checker that found them free says they no longer are. -/

/-- A minimal host, so the census reduces in the kernel. The cap-open appendix and the auth gadget
are generated identically over any base, so the census result is a property of the composition. -/
def probeHost : EffectVmDescriptor2 :=
  { name := "auth-weld-census-host", traceWidth := 8, piCount := 0
  , tables := [], constraints := [], hashSites := [], ranges := [] }

-- The welded descriptor carries PI pins (so the census is not empty for want of subjects).
-- (Docstring DEMOTED: Lean attaches `/-- -/` to the next declaration, and `#guard` is not one.)
#guard (pinsOf (authWeldedCapOpenTB probeHost "auth-weld-census" 1 1)).length > 0
-- ⚑ AND NOT ONE OF THEM IS UNFORCED.
#guard (unforcedPins (authWeldedCapOpenTB probeHost "auth-weld-census" 1 1)).isEmpty
#guard (unforcedPiSlots (authWeldedCapOpenTB probeHost "auth-weld-census" 1 1)).isEmpty

-- The census is NON-VACUOUS: drop the turn-digest lookup (the only constraint reading `actor`/`dst`)
-- and the two pins are condemned again — exactly the two slots the subtraction removed today.
def withoutTurnDigest : EffectVmDescriptor2 :=
  let d := authWeldedCapOpenTB probeHost "auth-weld-census" 1 1
  { d with constraints := d.constraints.filter (fun c => match c with
      | .lookup _ => ! (Dregg2.Circuit.Emit.RotWideCompactS2.refs2 c).contains
            (authActorCol (effCapOpenV3TB probeHost "auth-weld-census" 1))
      | _ => true) }

#guard (unforcedPins withoutTurnDigest).length == 2

/-! ## §3 — what the convergence re-emit must do (the flag day, written so it is findable). -/

/-- **`AUTH_WELD_REEMIT_NOTE`** — the exact re-emit contract for the single convergence pass.

SHAPE CHANGE. `transferCapOpenTBVmDescriptor2R24` (and any sibling routed through
`authWeldedCapOpenTB`) grows by `AUTH_SPAN NB = 12185` columns and by `W = 8` public inputs. The
`registry_fp` is the sha256 of the Lean-emitted TSV bytes, so it MOVES; peers on the old fingerprint
must REFUSE to load rather than reinterpret.

PRODUCER WORK — this is the part that bites, and it is a FAIL-OPEN shape if ignored.
`prove_vm_descriptor2` zero-extends short rows BEFORE the width check, so a producer that does not
write the new columns proves GREEN with zeros on any descriptor whose new columns are unconstrained.
That is NOT the case here — an all-zero signature block fails the sig lookup and the select gate,
which is measured in `circuit/tests/turn_auth_in_air_refuses.rs` as the UNSIGNED tooth. The gadget
is fail-CLOSED against the zero-extension hazard by construction. The producer must nonetheless
supply: the owner's Lamport public-key halves, the revealed preimages for the signed bits, the
per-bit pair compressions, the authority-root fold, the turn-digest absorb, the message bits with
their canonicality products, and the zero pad column.

VERIFIER WORK. The light client must ANCHOR `PI[pc .. pc+7]` from the owner's committed authority
root, exactly as it already anchors the turn-identity PIs from the trusted turn. Without that anchor
the prover chooses the public key and the verify is a tautology.

WHAT RE-EMITS: the wide registry TSV, its fingerprint, the VK for every rotated member, and the
`whole_history_proof` bake. WHAT REFUSES TO LOAD: any peer or proof on the old fingerprint. -/
def AUTH_WELD_REEMIT_NOTE : String :=
  "authWeldedCapOpenTB: +12185 columns, +8 PIs, registry_fp MOVES, VK rotates, producer must write \
   the signature/public-key/fold/digest/bit columns, verifier must anchor the 8 authority-root PIs \
   from the owner's committed key."

#guard AUTH_SPAN NB == 12185
#guard ELL NB == 248
#guard W == 8

end Dregg2.Circuit.Emit.TurnAuthCapOpenWeld
