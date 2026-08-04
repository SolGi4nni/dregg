/-
# PoA Dark Bazaar private descriptor — receipt-bound v2

This is a separately versioned extension of the fixed N=4/K=4 Dark Bazaar AIR.
It retains every v1 private-book, commitment and clearing constraint and adds
eight dedicated columns which publish the canonical Path of Angels receipt
digest as eight BabyBear public inputs.  No 32-byte-to-one-felt fold exists.

These eight pins bind a proof transcript to a receipt identity; they do not by
themselves prove that the receipt is the output of the PoA state machine.  The
consumer must run the Lean public-transition judge, obtain its canonical
`OutputWire.receiptDigest`, and compare all eight canonical lanes to these PIs.
-/
import Market.DarkBazaarPrivateDescriptor

namespace Market.DarkBazaarPrivatePoaDescriptor

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 Satisfied2 TraceFamily VmConstraint2 VmTrace emitVmJson2)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)

set_option autoImplicit false

/-- Stable public-statement family version.  V1 remains deployed separately. -/
def VERSION : Nat := 2

/-- The receipt digest occupies eight fresh columns after the complete v1 row. -/
def POA_RECEIPT_BASE : Nat := Market.DarkBazaarPrivateDescriptor.TRACE_WIDTH
def POA_RECEIPT (lane : Nat) : Nat := POA_RECEIPT_BASE + lane
def TRACE_WIDTH : Nat := Market.DarkBazaarPrivateDescriptor.TRACE_WIDTH +
  Market.DarkBazaarPrivateDescriptor.DIGEST_WIDTH
def PI_COUNT : Nat := 12 + Market.DarkBazaarPrivateDescriptor.DIGEST_WIDTH

/-- Exact v2 public statement: the complete v1 statement plus the faithful
eight-lane canonical PoA receipt digest. -/
structure PublicStatement where
  privateBook : Market.DarkBazaarPrivateDescriptor.PublicStatement
  poaReceiptDigest : Fin 8 → Int
deriving DecidableEq, Repr

/-- Eight independent first-row pins.  The wire mapping is lane-preserving:
receipt lane `i` is PI `12 + i`; no reduction or fold combines lanes. -/
def receiptPins : List VmConstraint2 :=
  (List.range Market.DarkBazaarPrivateDescriptor.DIGEST_WIDTH).map fun lane =>
    .base (.piBinding .first (POA_RECEIPT lane) (12 + lane))

/-- The separately named PoA receipt-bound proof family.  Its original
semantic constraints are reused from their Lean definitions, not copied into
Rust or reconstructed from emitted JSON. -/
def darkBazaarPrivatePoaN4K4Descriptor : EffectVmDescriptor2 :=
  { name := "dark-bazaar-private-poa-n4k4::receipt8-v2"
  , traceWidth := TRACE_WIDTH
  , piCount := PI_COUNT
  , tables := []
  , constraints := Market.DarkBazaarPrivateDescriptor.hashLookups ++
      Market.DarkBazaarPrivateDescriptor.semanticBodies.map
        (fun body => .base (.gate body)) ++
      Market.DarkBazaarPrivateDescriptor.publicPins ++ receiptPins ++
      Market.DarkBazaarPrivateDescriptor.semanticBodies.map
        (fun body => .base (.boundary .last body))
  , hashSites := []
  , ranges := [] }

theorem descriptor_trace_width :
    darkBazaarPrivatePoaN4K4Descriptor.traceWidth = 189 := rfl

theorem descriptor_pi_count :
    darkBazaarPrivatePoaN4K4Descriptor.piCount = 20 := rfl

theorem receipt_pins_length : receiptPins.length = 8 := by decide

/-- Every constraint of the v1 relation survives in v2.  The new family is
additive: it cannot drop a private-book or clearing tooth while adding receipt
identity. -/
theorem v1_constraints_subset :
    ∀ constraint ∈
        Market.DarkBazaarPrivateDescriptor.darkBazaarPrivateN4K4Descriptor.constraints,
      constraint ∈ darkBazaarPrivatePoaN4K4Descriptor.constraints := by
  intro constraint member
  simp only [Market.DarkBazaarPrivateDescriptor.darkBazaarPrivateN4K4Descriptor,
    darkBazaarPrivatePoaN4K4Descriptor,
    List.mem_append] at member ⊢
  rcases member with head | boundary
  · exact Or.inl (Or.inl head)
  · exact Or.inr boundary

theorem receipt_pin_mem (lane : Fin 8) :
    VmConstraint2.base (.piBinding .first (POA_RECEIPT lane.val) (12 + lane.val)) ∈
      darkBazaarPrivatePoaN4K4Descriptor.constraints := by
  simp [darkBazaarPrivatePoaN4K4Descriptor, receiptPins,
    Market.DarkBazaarPrivateDescriptor.DIGEST_WIDTH, lane.isLt]

/-- Satisfaction forces each receipt column to its separately indexed PI. -/
theorem receipt_pin_sound
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash darkBazaarPrivatePoaN4K4Descriptor
      Market.DarkBazaarPrivateDescriptor.dbM0 Market.DarkBazaarPrivateDescriptor.dbF0 []
      (Market.DarkBazaarPrivateDescriptor.constTrace a pis tf))
    (lane : Fin 8) :
    a (POA_RECEIPT lane.val) ≡ pis (12 + lane.val)
      [ZMOD Market.DarkBazaarPrivateDescriptor.BABYBEAR_MODULUS] := by
  have row := hsat.rowConstraints 0
    (by simp [Market.DarkBazaarPrivateDescriptor.constTrace]) _ (receipt_pin_mem lane)
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm,
    Market.DarkBazaarPrivateDescriptor.BABYBEAR_MODULUS] using row

/-- With canonical BabyBear representatives on both sides, the binding is
integer equality lane by lane, not merely equality after host reduction. -/
theorem receipt_lane_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : Market.DarkBazaarPrivateDescriptor.CanonicalAssignment a)
    (hcanonPis : Market.DarkBazaarPrivateDescriptor.CanonicalAssignment pis)
    (hsat : Satisfied2 hash darkBazaarPrivatePoaN4K4Descriptor
      Market.DarkBazaarPrivateDescriptor.dbM0 Market.DarkBazaarPrivateDescriptor.dbF0 []
      (Market.DarkBazaarPrivateDescriptor.constTrace a pis tf))
    (lane : Fin 8) :
    a (POA_RECEIPT lane.val) = pis (12 + lane.val) :=
  Market.DarkBazaarPrivateDescriptor.eq_of_modEq_of_canonical (receipt_pin_sound hsat lane)
    (hcanon (POA_RECEIPT lane.val)) (hcanonPis (12 + lane.val))

def columnReceiptDigest (a : Assignment) : Fin 8 → Int :=
  fun lane => a (POA_RECEIPT lane.val)

def piReceiptDigest (pis : Assignment) : Fin 8 → Int :=
  fun lane => pis (12 + lane.val)

/-- The whole faithful octet is equal.  This is the Lean-side statement the
Rust verifier's exact expected-receipt comparison implements. -/
theorem receipt_digest_exact
    {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hcanon : Market.DarkBazaarPrivateDescriptor.CanonicalAssignment a)
    (hcanonPis : Market.DarkBazaarPrivateDescriptor.CanonicalAssignment pis)
    (hsat : Satisfied2 hash darkBazaarPrivatePoaN4K4Descriptor
      Market.DarkBazaarPrivateDescriptor.dbM0 Market.DarkBazaarPrivateDescriptor.dbF0 []
      (Market.DarkBazaarPrivateDescriptor.constTrace a pis tf)) :
    columnReceiptDigest a = piReceiptDigest pis := by
  funext lane
  exact receipt_lane_exact hcanon hcanonPis hsat lane

#assert_axioms descriptor_trace_width
#assert_axioms descriptor_pi_count
#assert_axioms receipt_pins_length
#assert_axioms v1_constraints_subset
#assert_axioms receipt_pin_sound
#assert_axioms receipt_lane_exact
#assert_axioms receipt_digest_exact

end Market.DarkBazaarPrivatePoaDescriptor
