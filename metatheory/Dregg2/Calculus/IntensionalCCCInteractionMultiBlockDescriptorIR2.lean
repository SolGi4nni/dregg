/-
# A rate-safe multi-block DescriptorIR2 backend for deep interaction receipts

The one-site interaction-receipt backend is live only while `depth + 2 <= 16`.
This module gives every finite typed interaction address a live lowering.  It
packs the lossless `(root :: path)` words into eleven-word blocks and hashes
each block with four framing words:

`domain || total_depth || block_count || previous_digest || payload[11]`.

Every site therefore has fixed arity fifteen, below the deployed sixteen-lane
chip boundary.  The before and after domains use independent chains.  Every
intermediate digest is a public input and the next site reads its predecessor's
publicly pinned column, so a chain link is neither hidden witness data nor an
unconstrained host-side accumulator.

The descriptor still publishes the complete lossless receipt layout.  This is
intentional: the theorem for an arbitrary satisfying trace is unconditional at
the relation layer, while the hash chain is a separately auditable commitment
carrier.  The construction binds the executable interaction receipt; as proved
by the imported single-block module, it does not recreate typed syntax which
the receipt translation deliberately erases.

This is an additive module.  Canonical umbrella and report integration belong
to their owners.
-/

import Dregg2.Calculus.IntensionalCCCInteractionDescriptorIR2

namespace Dregg2.Calculus.IntensionalCCCInteractionMultiBlockDescriptorIR2

open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Calculus.IntensionalCCCTrace
open Dregg2.Calculus.IntensionalCCCInteractionBridge
open Dregg2.Calculus.IntensionalCCCInteractionBridge.Receipt

namespace Single
  abbrev rootCode :=
    Dregg2.Calculus.IntensionalCCCInteractionDescriptorIR2.rootCode
  abbrev pathWords :=
    Dregg2.Calculus.IntensionalCCCInteractionDescriptorIR2.pathWords
  abbrev layoutWords :=
    Dregg2.Calculus.IntensionalCCCInteractionDescriptorIR2.layoutWords
  abbrev receiptOfLayout :=
    Dregg2.Calculus.IntensionalCCCInteractionDescriptorIR2.receiptOfLayout
  theorem layoutWords_injective : Function.Injective layoutWords :=
    Dregg2.Calculus.IntensionalCCCInteractionDescriptorIR2.layoutWords_injective
  theorem stepReceipt_eq_receiptOfLayout
      {Γ : List Ty} {A : Ty} {before after : Net Γ A}
      (step : LocalStep before after) :
      stepReceipt step = receiptOfLayout (layout step) :=
    Dregg2.Calculus.IntensionalCCCInteractionDescriptorIR2.stepReceipt_eq_receiptOfLayout step
  theorem eq_of_modEq_of_canonical {x y : Int}
      (hmod : x ≡ y [ZMOD 2013265921])
      (hx : 0 <= x /\ x < 2013265921)
      (hy : 0 <= y /\ y < 2013265921) : x = y :=
    Dregg2.Calculus.IntensionalCCCInteractionDescriptorIR2.eq_of_modEq_of_canonical
      hmod hx hy
end Single

abbrev BoolLocalCert := Dregg2.Calculus.InteractionNetTrace.LocalCert

set_option autoImplicit false

def BABYBEAR_MODULUS : Int := 2013265921

/-! ## 1. Rate-safe framed chain -/

/-- Four framing words leave eleven payload lanes in a live 15-of-16 site. -/
def BLOCK_PAYLOAD : Nat := 11

def SITE_ARITY : Nat := 4 + BLOCK_PAYLOAD

def BEFORE_CHAIN_DOMAIN : Int := 1101
def AFTER_CHAIN_DOMAIN : Int := 1102

/-- `layoutWords` is nonempty, so this quotient formula is its positive ceiling
division by eleven. -/
def blockCount (depth : Nat) : Nat := depth / BLOCK_PAYLOAD + 1

theorem blockCount_pos (depth : Nat) : 0 < blockCount depth := by
  simp [blockCount]

/-- The final block always covers the final layout word; the padding subtraction
in the resource ledger therefore cannot underflow. -/
theorem blockCount_capacity (depth : Nat) :
    depth + 1 <= blockCount depth * BLOCK_PAYLOAD := by
  have hmod : depth % BLOCK_PAYLOAD < BLOCK_PAYLOAD :=
    Nat.mod_lt depth (by decide : 0 < BLOCK_PAYLOAD)
  have hdecomp : depth / BLOCK_PAYLOAD * BLOCK_PAYLOAD +
      depth % BLOCK_PAYLOAD = depth := by
    simpa [Nat.mul_comm] using Nat.div_add_mod depth BLOCK_PAYLOAD
  change depth + 1 <= (depth / 11 + 1) * 11
  norm_num [BLOCK_PAYLOAD] at hmod hdecomp
  omega

theorem site_arity_exact : SITE_ARITY = 15 := by decide

theorem site_arity_live : SITE_ARITY <= CHIP_RATE := by decide

def paddedLayoutWord (source : Layout) (k : Nat) : Int :=
  (Single.layoutWords source).getD k 0

def payloadBlock (source : Layout) (block : Nat) : List Int :=
  (List.range BLOCK_PAYLOAD).map fun lane =>
    paddedLayoutWord source (block * BLOCK_PAYLOAD + lane)

@[simp] theorem payloadBlock_length (source : Layout) (block : Nat) :
    (payloadBlock source block).length = BLOCK_PAYLOAD := by
  simp [payloadBlock]

/-- The canonical chained digest at a block index.  Calls beyond the declared
block count are meaningful algebraically but never emitted. -/
def chainDigestAt (hash : List Int -> Int) (domain : Int) (source : Layout) :
    Nat -> Int
  | 0 => hash ([domain, source.path.length, blockCount source.path.length, 0] ++
      payloadBlock source 0)
  | block + 1 =>
      hash ([domain, source.path.length, blockCount source.path.length,
        chainDigestAt hash domain source block] ++ payloadBlock source (block + 1))

def chainPreimageAt (hash : List Int -> Int) (domain : Int)
    (source : Layout) (block : Nat) : List Int :=
  [domain, source.path.length, blockCount source.path.length,
    if block = 0 then 0 else chainDigestAt hash domain source (block - 1)] ++
      payloadBlock source block

theorem chainDigestAt_eq_hash_preimage (hash : List Int -> Int) (domain : Int)
    (source : Layout) (block : Nat) :
    chainDigestAt hash domain source block =
      hash (chainPreimageAt hash domain source block) := by
  cases block with
  | zero => rfl
  | succ block => simp [chainDigestAt, chainPreimageAt]

def chainDigestWords (hash : List Int -> Int) (domain : Int)
    (source : Layout) : List Int :=
  (List.range (blockCount source.path.length)).map fun block =>
    chainDigestAt hash domain source block

@[simp] theorem chainDigestWords_length (hash : List Int -> Int) (domain : Int)
    (source : Layout) :
    (chainDigestWords hash domain source).length = blockCount source.path.length := by
  simp [chainDigestWords]

/-! ## 2. Exact public wire image -/

def beforeDomainCol (depth : Nat) : Nat := depth + 1
def afterDomainCol (depth : Nat) : Nat := depth + 2
def depthCol (depth : Nat) : Nat := depth + 3
def blockCountCol (depth : Nat) : Nat := depth + 4
def digestBase (depth : Nat) : Nat := depth + 5

def beforeDigestCol (depth block : Nat) : Nat := digestBase depth + block
def afterDigestCol (depth block : Nat) : Nat :=
  digestBase depth + blockCount depth + block

def traceWidth (depth : Nat) : Nat := depth + 5 + 2 * blockCount depth

def publicWords (hash : List Int -> Int) (source : Layout) : List Int :=
  Single.layoutWords source ++
    [BEFORE_CHAIN_DOMAIN, AFTER_CHAIN_DOMAIN, source.path.length,
      blockCount source.path.length] ++
    chainDigestWords hash BEFORE_CHAIN_DOMAIN source ++
    chainDigestWords hash AFTER_CHAIN_DOMAIN source

def publicOf (hash : List Int -> Int) (source : Layout) : Assignment :=
  fun c =>
    if _hLayout : c < source.path.length + 1 then
      paddedLayoutWord source c
    else if c = beforeDomainCol source.path.length then BEFORE_CHAIN_DOMAIN
    else if c = afterDomainCol source.path.length then AFTER_CHAIN_DOMAIN
    else if c = depthCol source.path.length then source.path.length
    else if c = blockCountCol source.path.length then blockCount source.path.length
    else if _hBefore : c < digestBase source.path.length + blockCount source.path.length then
      chainDigestAt hash BEFORE_CHAIN_DOMAIN source
        (c - digestBase source.path.length)
    else if _hAfter : c < traceWidth source.path.length then
      chainDigestAt hash AFTER_CHAIN_DOMAIN source
        (c - (digestBase source.path.length + blockCount source.path.length))
    else 0

@[simp] theorem layoutWords_length (source : Layout) :
    (Single.layoutWords source).length = source.path.length + 1 := by
  simp [Dregg2.Calculus.IntensionalCCCInteractionDescriptorIR2.layoutWords,
    Dregg2.Calculus.IntensionalCCCInteractionDescriptorIR2.pathWords]

@[simp] theorem publicWords_length (hash : List Int -> Int) (source : Layout) :
    (publicWords hash source).length = traceWidth source.path.length := by
  simp [publicWords, traceWidth]
  omega

@[simp] theorem publicOf_layout (hash : List Int -> Int) (source : Layout)
    (k : Nat) (hk : k < source.path.length + 1) :
    publicOf hash source k = paddedLayoutWord source k := by
  simp [publicOf, hk]

@[simp] theorem publicOf_root (hash : List Int -> Int) (source : Layout) :
    publicOf hash source 0 = Single.rootCode source.root := by
  rw [publicOf_layout hash source 0 (by omega)]
  unfold paddedLayoutWord
  change (((Single.rootCode source.root : Int) ::
    Single.pathWords source.path).getD 0 0) = Single.rootCode source.root
  rw [List.getD_cons_zero]

@[simp] theorem publicOf_path (hash : List Int -> Int) (source : Layout)
    (i : Nat) (hi : i < source.path.length) :
    publicOf hash source (i + 1) = source.path[i].code := by
  rw [publicOf_layout hash source (i + 1) (by omega)]
  simp [paddedLayoutWord,
    Dregg2.Calculus.IntensionalCCCInteractionDescriptorIR2.layoutWords,
    Dregg2.Calculus.IntensionalCCCInteractionDescriptorIR2.pathWords, hi]

@[simp] theorem publicOf_beforeDomain (hash : List Int -> Int) (source : Layout) :
    publicOf hash source (beforeDomainCol source.path.length) = BEFORE_CHAIN_DOMAIN := by
  simp [publicOf, beforeDomainCol]

@[simp] theorem publicOf_afterDomain (hash : List Int -> Int) (source : Layout) :
    publicOf hash source (afterDomainCol source.path.length) = AFTER_CHAIN_DOMAIN := by
  simp [publicOf, beforeDomainCol, afterDomainCol]

@[simp] theorem publicOf_depth (hash : List Int -> Int) (source : Layout) :
    publicOf hash source (depthCol source.path.length) = source.path.length := by
  simp [publicOf, beforeDomainCol, afterDomainCol, depthCol]

@[simp] theorem publicOf_blockCount (hash : List Int -> Int) (source : Layout) :
    publicOf hash source (blockCountCol source.path.length) =
      blockCount source.path.length := by
  simp [publicOf, beforeDomainCol, afterDomainCol, depthCol, blockCountCol]

@[simp] theorem publicOf_beforeDigest (hash : List Int -> Int) (source : Layout)
    (block : Nat) (hblock : block < blockCount source.path.length) :
    publicOf hash source (beforeDigestCol source.path.length block) =
      chainDigestAt hash BEFORE_CHAIN_DOMAIN source block := by
  have hLayout : ¬ beforeDigestCol source.path.length block <
      source.path.length + 1 := by
    simp [beforeDigestCol, digestBase]
    omega
  have hDomain0 : beforeDigestCol source.path.length block ≠
      beforeDomainCol source.path.length := by
    simp [beforeDigestCol, beforeDomainCol, digestBase]
    omega
  have hDomain1 : beforeDigestCol source.path.length block ≠
      afterDomainCol source.path.length := by
    simp [beforeDigestCol, afterDomainCol, digestBase]
    omega
  have hDepth : beforeDigestCol source.path.length block ≠
      depthCol source.path.length := by
    simp [beforeDigestCol, depthCol, digestBase]
    omega
  have hCount : beforeDigestCol source.path.length block ≠
      blockCountCol source.path.length := by
    simp [beforeDigestCol, blockCountCol, digestBase]
    omega
  have hBefore : beforeDigestCol source.path.length block <
      digestBase source.path.length + blockCount source.path.length := by
    simpa [beforeDigestCol, Nat.add_assoc] using
      Nat.add_lt_add_left hblock (digestBase source.path.length)
  unfold publicOf
  rw [dif_neg hLayout, if_neg hDomain0, if_neg hDomain1, if_neg hDepth,
    if_neg hCount, dif_pos hBefore]
  congr 1
  simp [beforeDigestCol, digestBase]

@[simp] theorem publicOf_afterDigest (hash : List Int -> Int) (source : Layout)
    (block : Nat) (hblock : block < blockCount source.path.length) :
    publicOf hash source (afterDigestCol source.path.length block) =
      chainDigestAt hash AFTER_CHAIN_DOMAIN source block := by
  have hLayout : ¬ afterDigestCol source.path.length block <
      source.path.length + 1 := by
    simp [afterDigestCol, digestBase]
    omega
  have hDomain0 : afterDigestCol source.path.length block ≠
      beforeDomainCol source.path.length := by
    simp [afterDigestCol, beforeDomainCol, digestBase]
    omega
  have hDomain1 : afterDigestCol source.path.length block ≠
      afterDomainCol source.path.length := by
    simp [afterDigestCol, afterDomainCol, digestBase]
    omega
  have hDepth : afterDigestCol source.path.length block ≠
      depthCol source.path.length := by
    simp [afterDigestCol, depthCol, digestBase]
    omega
  have hCount : afterDigestCol source.path.length block ≠
      blockCountCol source.path.length := by
    simp [afterDigestCol, blockCountCol, digestBase]
    omega
  have hBefore : ¬ afterDigestCol source.path.length block <
      digestBase source.path.length + blockCount source.path.length := by
    simp [afterDigestCol]
  have hAfter : afterDigestCol source.path.length block <
      traceWidth source.path.length := by
    have hinner := Nat.add_lt_add_left hblock (blockCount source.path.length)
    have houter := Nat.add_lt_add_left hinner (digestBase source.path.length)
    simpa [afterDigestCol, traceWidth, digestBase, Nat.add_assoc, Nat.two_mul]
      using houter
  unfold publicOf
  rw [dif_neg hLayout, if_neg hDomain0, if_neg hDomain1, if_neg hDepth,
    if_neg hCount, dif_neg hBefore, dif_pos hAfter]
  congr 1
  simp [afterDigestCol, digestBase]

/-! ## 3. Descriptor and live hash sites -/

def payloadInputs (depth block : Nat) : List HashInput :=
  (List.range BLOCK_PAYLOAD).map fun lane =>
    let k := block * BLOCK_PAYLOAD + lane
    if k < depth + 1 then .col k else .zero

def priorInput (digestCol : Nat -> Nat) (block : Nat) : HashInput :=
  if block = 0 then .zero else .col (digestCol (block - 1))

def blockInputs (depth domainColumn : Nat) (digestCol : Nat -> Nat)
    (block : Nat) : List HashInput :=
  [.col domainColumn, .col (depthCol depth), .col (blockCountCol depth),
    priorInput digestCol block] ++ payloadInputs depth block

@[simp] theorem payloadInputs_length (depth block : Nat) :
    (payloadInputs depth block).length = BLOCK_PAYLOAD := by
  simp [payloadInputs]

@[simp] theorem blockInputs_length (depth domainColumn : Nat)
    (digestCol : Nat -> Nat) (block : Nat) :
    (blockInputs depth domainColumn digestCol block).length = SITE_ARITY := by
  simp [blockInputs, SITE_ARITY]
  omega

def beforeBlockSite (depth block : Nat) : VmHashSite :=
  { digestCol := beforeDigestCol depth block
  , inputs := blockInputs depth (beforeDomainCol depth)
      (beforeDigestCol depth) block
  , arity := SITE_ARITY }

def afterBlockSite (depth block : Nat) : VmHashSite :=
  { digestCol := afterDigestCol depth block
  , inputs := blockInputs depth (afterDomainCol depth)
      (afterDigestCol depth) block
  , arity := SITE_ARITY }

def beforeSites (depth : Nat) : List VmHashSite :=
  (List.range (blockCount depth)).map (beforeBlockSite depth)

def afterSites (depth : Nat) : List VmHashSite :=
  (List.range (blockCount depth)).map (afterBlockSite depth)

def endpointHashSites (depth : Nat) : List VmHashSite :=
  beforeSites depth ++ afterSites depth

theorem endpointHashSites_length (depth : Nat) :
    (endpointHashSites depth).length = 2 * blockCount depth := by
  simp [endpointHashSites, beforeSites, afterSites]
  omega

theorem endpointHashSites_live (depth : Nat) (site : VmHashSite)
    (hsite : site ∈ endpointHashSites depth) :
    site.inputs.length = 15 /\ site.arity = 15 /\ site.arity <= CHIP_RATE := by
  simp only [endpointHashSites, List.mem_append, beforeSites, afterSites,
    List.mem_map] at hsite
  rcases hsite with ⟨block, _, rfl⟩ | ⟨block, _, rfl⟩ <;>
    exact ⟨by simp [beforeBlockSite, afterBlockSite, site_arity_exact],
      site_arity_exact, site_arity_live⟩

def publicPins (depth : Nat) : List VmConstraint2 :=
  (List.range (traceWidth depth)).map fun c =>
    .base (.piBinding .first c c)

def descriptorAtDepth (depth : Nat) : EffectVmDescriptor2 :=
  { name := "dregg-intensional-ccc-local-receipt-v2-multiblock-depth-" ++
      toString depth
  , traceWidth := traceWidth depth
  , piCount := traceWidth depth
  , tables := [mainTableDef (traceWidth depth)]
  , constraints := publicPins depth
  , hashSites := endpointHashSites depth
  , ranges := [] }

def descriptor {Γ : List Ty} {A : Ty} {before after : Net Γ A}
    (step : LocalStep before after) : EffectVmDescriptor2 :=
  descriptorAtDepth (layout step).path.length

theorem descriptor_shape_exact (depth : Nat) :
    (descriptorAtDepth depth).traceWidth = depth + 5 + 2 * blockCount depth /\
      (descriptorAtDepth depth).piCount = depth + 5 + 2 * blockCount depth /\
      (descriptorAtDepth depth).constraints.length = depth + 5 + 2 * blockCount depth /\
      (descriptorAtDepth depth).hashSites.length = 2 * blockCount depth /\
      (descriptorAtDepth depth).ranges = [] := by
  simp [descriptorAtDepth, traceWidth, publicPins, endpointHashSites_length]

structure Cost where
  addressDepth : Nat
  payloadWords : Nat
  blocksPerEndpoint : Nat
  publicChainDigests : Nat
  publicInputs : Nat
  traceColumns : Nat
  linearPiConstraints : Nat
  hashSites : Nat
  absorbedFelts : Nat
  paddedPayloadFelts : Nat
  maxArithmeticGateDegree : Nat
  deriving DecidableEq, Repr

def costAtDepth (depth : Nat) : Cost :=
  let blocks := blockCount depth
  { addressDepth := depth
  , payloadWords := depth + 1
  , blocksPerEndpoint := blocks
  , publicChainDigests := 2 * blocks
  , publicInputs := traceWidth depth
  , traceColumns := traceWidth depth
  , linearPiConstraints := (publicPins depth).length
  , hashSites := (endpointHashSites depth).length
  , absorbedFelts := 2 * blocks * SITE_ARITY
  , paddedPayloadFelts := 2 * (blocks * BLOCK_PAYLOAD - (depth + 1))
  , maxArithmeticGateDegree := 1 }

theorem cost_exact (depth : Nat) :
    costAtDepth depth =
      { addressDepth := depth, payloadWords := depth + 1,
        blocksPerEndpoint := blockCount depth,
        publicChainDigests := 2 * blockCount depth,
        publicInputs := depth + 5 + 2 * blockCount depth,
        traceColumns := depth + 5 + 2 * blockCount depth,
        linearPiConstraints := depth + 5 + 2 * blockCount depth,
        hashSites := 2 * blockCount depth,
        absorbedFelts := 30 * blockCount depth,
        paddedPayloadFelts :=
          2 * (blockCount depth * BLOCK_PAYLOAD - (depth + 1)),
        maxArithmeticGateDegree := 1 } := by
  simp [costAtDepth, traceWidth, publicPins, endpointHashSites_length,
    SITE_ARITY]
  unfold BLOCK_PAYLOAD
  omega

/-! ## 4. Constructive completeness -/

def rowOf (hash : List Int -> Int) (source : Layout) : Assignment :=
  publicOf hash source

def traceOf (hash : List Int -> Int) (source : Layout) : VmTrace :=
  { rows := [rowOf hash source]
  , pub := publicOf hash source
  , tf := fun _ => [] }

@[simp] private theorem envAt_traceOf_loc (hash : List Int -> Int)
    (source : Layout) (c : Nat) :
    (envAt (traceOf hash source) 0).loc c = publicOf hash source c := by
  simp [envAt, traceOf, rowOf]

private theorem resolved_payloadInputs (hash : List Int -> Int) (source : Layout)
    (block : Nat) (acc : List Int) :
    (payloadInputs source.path.length block).map
        (HashInput.resolve (envAt (traceOf hash source) 0) acc) =
      payloadBlock source block := by
  rw [payloadInputs, payloadBlock, List.map_map]
  apply List.ext_getElem
  · simp
  · intro lane hleft hright
    have hlane : lane < BLOCK_PAYLOAD := by simpa using hright
    simp only [List.getElem_map, List.getElem_range, Function.comp_apply]
    by_cases hk : block * BLOCK_PAYLOAD + lane < source.path.length + 1
    · simp [hk, HashInput.resolve, envAt, traceOf, rowOf, paddedLayoutWord]
    · have hget : (Single.layoutWords source).getD
          (block * BLOCK_PAYLOAD + lane) 0 = 0 := by
        rw [List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by simpa [layoutWords_length] using hk)]
        rfl
      simp [hk, HashInput.resolve, paddedLayoutWord]

private theorem resolved_blockInputs (hash : List Int -> Int) (domain : Int)
    (source : Layout) (block : Nat)
    (hblock : block < blockCount source.path.length)
    (domainColumn : Nat) (digestColumn : Nat -> Nat)
    (hdomain : publicOf hash source domainColumn = domain)
    (hdigest : forall b, b < blockCount source.path.length ->
      publicOf hash source (digestColumn b) = chainDigestAt hash domain source b)
    (acc : List Int) :
    (blockInputs source.path.length domainColumn digestColumn block).map
        (HashInput.resolve (envAt (traceOf hash source) 0) acc) =
      chainPreimageAt hash domain source block := by
  have hloc : (envAt (traceOf hash source) 0).loc = publicOf hash source := by
    funext c
    exact envAt_traceOf_loc hash source c
  simp only [blockInputs, List.map_append, List.map_cons, List.map_nil,
    HashInput.resolve, hloc]
  rw [hdomain, publicOf_depth, publicOf_blockCount,
    resolved_payloadInputs hash source block acc]
  cases block with
  | zero => rfl
  | succ block =>
      have hb : block < blockCount source.path.length := by omega
      simp [priorInput, hdigest block hb, chainPreimageAt]

private def DirectInput : HashInput -> Prop
  | .col _ => True
  | .zero => True
  | .digest _ => False

private def DirectSite (site : VmHashSite) : Prop :=
  forall input, input ∈ site.inputs -> DirectInput input

private theorem direct_resolve_independent (env : VmRowEnv) (site : VmHashSite)
    (hdirect : DirectSite site) (left right : List Int) :
    site.inputs.map (HashInput.resolve env left) =
      site.inputs.map (HashInput.resolve env right) := by
  apply List.map_congr_left
  intro input hinput
  have h := hdirect input hinput
  cases input <;> simp_all [DirectInput, HashInput.resolve]

private theorem blockSite_direct (depth domainColumn : Nat)
    (digestColumn : Nat -> Nat) (block : Nat) :
    DirectSite
      { digestCol := digestColumn block
      , inputs := blockInputs depth domainColumn digestColumn block
      , arity := SITE_ARITY } := by
  intro input hinput
  rcases List.mem_append.mp hinput with hprefix | hpayload
  · simp only [List.mem_cons] at hprefix
    rcases hprefix with rfl | rfl | rfl | rfl | hfalse
    · trivial
    · trivial
    · trivial
    · cases block <;> simp [priorInput, DirectInput]
    · exact False.elim (List.not_mem_nil hfalse)
  · simp only [payloadInputs, List.mem_map] at hpayload
    obtain ⟨lane, _, rfl⟩ := hpayload
    split <;> trivial

private theorem siteHoldsAll_of_direct_equations (hash : List Int -> Int)
    (env : VmRowEnv) (sites : List VmHashSite)
    (hdirect : forall site, site ∈ sites -> DirectSite site)
    (hequation : forall site, site ∈ sites ->
      env.loc site.digestCol = hash (site.resolvedInputs env [])) :
    siteHoldsAll hash env sites := by
  unfold siteHoldsAll
  have go : forall (acc : List Int) (rest : List VmHashSite),
      (forall site, site ∈ rest -> DirectSite site) ->
      (forall site, site ∈ rest ->
        env.loc site.digestCol = hash (site.resolvedInputs env [])) ->
      siteHoldsAll.go hash env acc rest := by
    intro acc rest
    induction rest generalizing acc with
    | nil => simp [siteHoldsAll.go]
    | cons site tail ih =>
        intro hdir heq
        simp only [siteHoldsAll.go]
        have hsdir : DirectSite site := hdir site (by simp)
        have hresolved := direct_resolve_independent env site hsdir acc []
        constructor
        · change env.loc site.digestCol =
            hash (site.inputs.map (HashInput.resolve env acc))
          rw [hresolved]
          exact heq site (by simp)
        · apply ih
          · intro s hs
            exact hdir s (by simp [hs])
          · intro s hs
            exact heq s (by simp [hs])
  exact go [] sites hdirect hequation

private theorem beforeBlockSite_equation (hash : List Int -> Int) (source : Layout)
    (block : Nat) (hblock : block < blockCount source.path.length) :
    (envAt (traceOf hash source) 0).loc
        (beforeBlockSite source.path.length block).digestCol =
      hash ((beforeBlockSite source.path.length block).resolvedInputs
        (envAt (traceOf hash source) 0) []) := by
  rw [show (envAt (traceOf hash source) 0).loc
      (beforeBlockSite source.path.length block).digestCol =
      chainDigestAt hash BEFORE_CHAIN_DOMAIN source block by
        simpa [beforeBlockSite, envAt, traceOf, rowOf] using
          publicOf_beforeDigest hash source block hblock]
  rw [chainDigestAt_eq_hash_preimage]
  congr 1
  exact (resolved_blockInputs hash BEFORE_CHAIN_DOMAIN source block hblock
    (beforeDomainCol source.path.length) (beforeDigestCol source.path.length)
    (publicOf_beforeDomain hash source)
    (fun b hb => publicOf_beforeDigest hash source b hb) []).symm

private theorem afterBlockSite_equation (hash : List Int -> Int) (source : Layout)
    (block : Nat) (hblock : block < blockCount source.path.length) :
    (envAt (traceOf hash source) 0).loc
        (afterBlockSite source.path.length block).digestCol =
      hash ((afterBlockSite source.path.length block).resolvedInputs
        (envAt (traceOf hash source) 0) []) := by
  rw [show (envAt (traceOf hash source) 0).loc
      (afterBlockSite source.path.length block).digestCol =
      chainDigestAt hash AFTER_CHAIN_DOMAIN source block by
        simpa [afterBlockSite, envAt, traceOf, rowOf] using
          publicOf_afterDigest hash source block hblock]
  rw [chainDigestAt_eq_hash_preimage]
  congr 1
  exact (resolved_blockInputs hash AFTER_CHAIN_DOMAIN source block hblock
    (afterDomainCol source.path.length) (afterDigestCol source.path.length)
    (publicOf_afterDomain hash source)
    (fun b hb => publicOf_afterDigest hash source b hb) []).symm

theorem traceOf_hashes (hash : List Int -> Int) (source : Layout) :
    siteHoldsAll hash (envAt (traceOf hash source) 0)
      (endpointHashSites source.path.length) := by
  apply siteHoldsAll_of_direct_equations
  · intro site hsite
    simp only [endpointHashSites, List.mem_append, beforeSites, afterSites,
      List.mem_map] at hsite
    rcases hsite with ⟨block, hblock, rfl⟩ | ⟨block, hblock, rfl⟩
    · exact blockSite_direct source.path.length (beforeDomainCol source.path.length)
        (beforeDigestCol source.path.length) block
    · exact blockSite_direct source.path.length (afterDomainCol source.path.length)
        (afterDigestCol source.path.length) block
  · intro site hsite
    simp only [endpointHashSites, List.mem_append, beforeSites, afterSites,
      List.mem_map] at hsite
    rcases hsite with ⟨block, hblock, rfl⟩ | ⟨block, hblock, rfl⟩
    · exact beforeBlockSite_equation hash source block (by simpa using hblock)
    · exact afterBlockSite_equation hash source block (by simpa using hblock)

theorem memLog_descriptorAtDepth (depth : Nat) (trace : VmTrace) :
    memLog (descriptorAtDepth depth) trace = [] := by
  simp [memLog, memOpsOf, descriptorAtDepth, publicPins]

theorem mapLog_descriptorAtDepth (depth : Nat) (trace : VmTrace) :
    mapLog (descriptorAtDepth depth) trace = [] := by
  simp [mapLog, mapOpsOf, descriptorAtDepth, publicPins]

/-- Every typed local step, at every finite address depth, constructs a live
IR-v2 witness.  There is no depth<=14 premise. -/
theorem trace_complete (hash : List Int -> Int)
    {Γ : List Ty} {A : Ty} {before after : Net Γ A}
    (step : LocalStep before after) :
    Satisfied2 hash (descriptor step) (fun _ => 0)
      (fun _ => ((0 : Int), 0)) []
      (traceOf hash (layout step)) := by
  refine ⟨?_, ?_, ?_, List.nodup_nil, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi c hc
    have hi0 : i = 0 := by
      simp [traceOf] at hi
      omega
    subst i
    simp only [descriptor, descriptorAtDepth] at hc
    simp only [publicPins, List.mem_map] at hc
    obtain ⟨col, hcol, rfl⟩ := hc
    simp [VmConstraint2.holdsAt, traceOf, rowOf, envAt]
  · intro i hi
    have hi0 : i = 0 := by
      simp [traceOf] at hi
      omega
    subst i
    exact traceOf_hashes hash (layout step)
  · intro i hi r hr
    simp [descriptor, descriptorAtDepth] at hr
  · intro op hop
    rw [show descriptor step = descriptorAtDepth (layout step).path.length by rfl,
      memLog_descriptorAtDepth] at hop
    cases hop
  · rw [show descriptor step = descriptorAtDepth (layout step).path.length by rfl,
      memLog_descriptorAtDepth]
    trivial
  · rw [show descriptor step = descriptorAtDepth (layout step).path.length by rfl,
      memLog_descriptorAtDepth]
    simpa using
      (memCheck_nil (fun _ : Int => 0) (fun _ : Int => ((0 : Int), 0)))
  · rw [show descriptor step = descriptorAtDepth (layout step).path.length by rfl,
      memLog_descriptorAtDepth]
    simp [traceOf]
  · rw [show descriptor step = descriptorAtDepth (layout step).path.length by rfl,
      mapLog_descriptorAtDepth]
    simp [traceOf]

/-! ## 5. Arbitrary satisfying-trace soundness -/

def withPublic (hash : List Int -> Int) (source : Layout) (trace : VmTrace) : VmTrace :=
  { trace with pub := publicOf hash source }

def CanonicalFirstLayoutRow (source : Layout) (trace : VmTrace) : Prop :=
  (0 <= (envAt trace 0).loc 0 /\
    (envAt trace 0).loc 0 < BABYBEAR_MODULUS) /\
  forall i, i < source.path.length ->
    0 <= (envAt trace 0).loc (i + 1) /\
      (envAt trace 0).loc (i + 1) < BABYBEAR_MODULUS

def StatementSatisfied (hash : List Int -> Int)
    {Γ : List Ty} {A : Ty} {before after : Net Γ A}
    (step : LocalStep before after) (trace : VmTrace) : Prop :=
  trace.rows ≠ [] /\
    CanonicalFirstLayoutRow (layout step) trace /\
    Satisfied2 hash (descriptor step) (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (withPublic hash (layout step) trace)

theorem public_pin_modEq (hash : List Int -> Int) (source : Layout)
    (trace : VmTrace) (hne : trace.rows ≠ [])
    (hsat : Satisfied2 hash (descriptorAtDepth source.path.length) (fun _ => 0)
      (fun _ => ((0 : Int), 0)) [] (withPublic hash source trace))
    (c : Nat) (hc : c < traceWidth source.path.length) :
    (envAt trace 0).loc c ≡ publicOf hash source c [ZMOD 2013265921] := by
  have hpos : 0 < (withPublic hash source trace).rows.length := by
    simp [withPublic]
    exact List.length_pos_iff.mpr hne
  have h := hsat.rowConstraints 0 hpos
    (.base (.piBinding .first c c)) (by
      simp [descriptorAtDepth, publicPins, hc])
  simpa [VmConstraint2.holdsAt, withPublic, envAt] using h

theorem root_code_bound (root : RootTag) :
    0 <= (Single.rootCode root : Int) /\
      (Single.rootCode root : Int) < BABYBEAR_MODULUS := by
  cases root <;> decide

theorem path_code_bound (tag : PathTag) :
    0 <= (tag.code : Int) /\ tag.code < BABYBEAR_MODULUS := by
  cases tag <;> decide

theorem satisfying_root_exact (hash : List Int -> Int)
    {Γ : List Ty} {A : Ty} {before after : Net Γ A}
    (step : LocalStep before after) (trace : VmTrace)
    (h : StatementSatisfied hash step trace) :
    (envAt trace 0).loc 0 = Single.rootCode (layout step).root := by
  exact Single.eq_of_modEq_of_canonical
    (public_pin_modEq hash (layout step) trace h.1 h.2.2 0 (by
      simp [traceWidth])) h.2.1.1 (root_code_bound (layout step).root)

theorem satisfying_path_exact (hash : List Int -> Int)
    {Γ : List Ty} {A : Ty} {before after : Net Γ A}
    (step : LocalStep before after) (trace : VmTrace)
    (h : StatementSatisfied hash step trace)
    (i : Nat) (hi : i < (layout step).path.length) :
    (envAt trace 0).loc (i + 1) = (layout step).path[i].code := by
  exact Single.eq_of_modEq_of_canonical
    (by simpa [publicOf_path hash (layout step) i hi] using
      public_pin_modEq hash (layout step) trace h.1 h.2.2 (i + 1) (by
        simp [traceWidth]
        omega))
    (h.2.1.2 i hi) (path_code_bound (layout step).path[i])

def firstRowLayoutWords (depth : Nat) (trace : VmTrace) : List Int :=
  (envAt trace 0).loc 0 ::
    (List.range depth).map fun i => (envAt trace 0).loc (i + 1)

theorem satisfying_layout_words_exact (hash : List Int -> Int)
    {Γ : List Ty} {A : Ty} {before after : Net Γ A}
    (step : LocalStep before after) (trace : VmTrace)
    (h : StatementSatisfied hash step trace) :
    firstRowLayoutWords (layout step).path.length trace =
      Single.layoutWords (layout step) := by
  change (envAt trace 0).loc 0 ::
      (List.range (layout step).path.length).map
        (fun i => (envAt trace 0).loc (i + 1)) =
    (Single.rootCode (layout step).root : Int) ::
      Single.pathWords (layout step).path
  simp only [List.cons.injEq]
  constructor
  · exact satisfying_root_exact hash step trace h
  · apply List.ext_getElem
    · simp [Dregg2.Calculus.IntensionalCCCInteractionDescriptorIR2.pathWords]
    · intro i hiLeft hiRight
      have hi : i < (layout step).path.length := by
        simpa [Dregg2.Calculus.IntensionalCCCInteractionDescriptorIR2.pathWords]
          using hiRight
      simp [Dregg2.Calculus.IntensionalCCCInteractionDescriptorIR2.pathWords,
        satisfying_path_exact hash step trace h i hi]

theorem satisfying_trace_binds_exact_receipt (hash : List Int -> Int)
    {Γ : List Ty} {A : Ty} {before after : Net Γ A}
    (step : LocalStep before after) (trace : VmTrace)
    (h : StatementSatisfied hash step trace) (candidate : Layout)
    (hcandidate : Single.layoutWords candidate =
      firstRowLayoutWords (layout step).path.length trace) :
    Single.receiptOfLayout candidate = stepReceipt step := by
  rw [satisfying_layout_words_exact hash step trace h] at hcandidate
  have hc : candidate = layout step := Single.layoutWords_injective hcandidate
  subst candidate
  exact (Single.stepReceipt_eq_receiptOfLayout step).symm

theorem satisfying_trace_relation_sound (hash : List Int -> Int)
    {Γ : List Ty} {A : Ty} {before after : Net Γ A}
    (step : LocalStep before after) (trace : VmTrace)
    (h : StatementSatisfied hash step trace) (candidate : Layout)
    (hcandidate : Single.layoutWords candidate =
      firstRowLayoutWords (layout step).path.length trace)
    (env : Env Γ) :
    (Single.receiptOfLayout candidate).check = true /\
      after.denote env = before.denote env := by
  have hreceipt := satisfying_trace_binds_exact_receipt
    hash step trace h candidate hcandidate
  rw [hreceipt]
  exact translatedStep_checked_and_source_sound step env

/-- Every public chain link, not merely the final digest, is pinned by an
arbitrary satisfying trace. -/
theorem satisfying_public_chain_links (hash : List Int -> Int)
    {Γ : List Ty} {A : Ty} {before after : Net Γ A}
    (step : LocalStep before after) (trace : VmTrace)
    (h : StatementSatisfied hash step trace)
    (block : Nat) (hblock : block < blockCount (layout step).path.length) :
    (envAt trace 0).loc (beforeDigestCol (layout step).path.length block) ≡
        chainDigestAt hash BEFORE_CHAIN_DOMAIN (layout step) block
          [ZMOD 2013265921] /\
      (envAt trace 0).loc (afterDigestCol (layout step).path.length block) ≡
        chainDigestAt hash AFTER_CHAIN_DOMAIN (layout step) block
          [ZMOD 2013265921] := by
  constructor
  · simpa [publicOf_beforeDigest hash (layout step) block hblock] using
      public_pin_modEq hash (layout step) trace h.1 h.2.2
        (beforeDigestCol (layout step).path.length block) (by
          simp [beforeDigestCol, digestBase, traceWidth]
          omega)
  · simpa [publicOf_afterDigest hash (layout step) block hblock] using
      public_pin_modEq hash (layout step) trace h.1 h.2.2
        (afterDigestCol (layout step).path.length block) (by
          simp [afterDigestCol, digestBase, traceWidth]
          omega)

/-! ## 6. Refusal and deep reference guard -/

def tamperedBeforeLinkPublic (hash : List Int -> Int) (source : Layout)
    (block : Nat) : Assignment :=
  fun c => if c = beforeDigestCol source.path.length block then
    publicOf hash source c + 1 else publicOf hash source c

def tamperedBeforeLinkTrace (hash : List Int -> Int) (source : Layout)
    (block : Nat) : VmTrace :=
  { rows := [rowOf hash source]
  , pub := tamperedBeforeLinkPublic hash source block
  , tf := fun _ => [] }

/-- Changing one published intermediate commitment while retaining the honest
row and all hash computations is refused by the corresponding PI binding. -/
theorem public_chain_link_tamper_refused (hash : List Int -> Int) (source : Layout)
    (block : Nat) (hblock : block < blockCount source.path.length) :
    ¬ Satisfied2 hash (descriptorAtDepth source.path.length) (fun _ => 0)
      (fun _ => ((0 : Int), 0)) []
      (tamperedBeforeLinkTrace hash source block) := by
  intro hsat
  let col := beforeDigestCol source.path.length block
  have hcol : col < traceWidth source.path.length := by
    simp [col, beforeDigestCol, digestBase, traceWidth]
    omega
  have h := hsat.rowConstraints 0 (by simp [tamperedBeforeLinkTrace])
    (.base (.piBinding .first col col)) (by
      simp [descriptorAtDepth, publicPins, hcol])
  have hmod : publicOf hash source col ≡ publicOf hash source col + 1
      [ZMOD 2013265921] := by
    simp [VmConstraint2.holdsAt, tamperedBeforeLinkTrace, rowOf,
      tamperedBeforeLinkPublic, col, envAt] at h
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp hmod
  omega

namespace Reference

def deepLayout : Layout :=
  ⟨.beta, List.replicate 25 .shareBody⟩

theorem deep_layout_depth : deepLayout.path.length = 25 := by decide

theorem deep_block_count : blockCount deepLayout.path.length = 3 := by decide

theorem deep_cost_exact :
    costAtDepth deepLayout.path.length =
      { addressDepth := 25, payloadWords := 26, blocksPerEndpoint := 3,
        publicChainDigests := 6, publicInputs := 36, traceColumns := 36,
        linearPiConstraints := 36, hashSites := 6, absorbedFelts := 90,
        paddedPayloadFelts := 14, maxArithmeticGateDegree := 1 } := by
  decide

theorem deep_all_sites_live (site : VmHashSite)
    (hsite : site ∈ endpointHashSites deepLayout.path.length) :
    site.inputs.length = 15 /\ site.arity = 15 /\ site.arity <= CHIP_RATE :=
  endpointHashSites_live _ site hsite

#guard (descriptorAtDepth 25).traceWidth == 36
#guard (descriptorAtDepth 25).piCount == 36
#guard (descriptorAtDepth 25).constraints.length == 36
#guard (descriptorAtDepth 25).hashSites.length == 6
#guard (descriptorAtDepth 25).hashSites.all (fun site => site.arity == 15)

end Reference

#assert_all_clean [
  blockCount_pos,
  blockCount_capacity,
  site_arity_exact,
  site_arity_live,
  payloadBlock_length,
  chainDigestAt_eq_hash_preimage,
  chainDigestWords_length,
  layoutWords_length,
  publicWords_length,
  publicOf_layout,
  publicOf_root,
  publicOf_path,
  publicOf_beforeDomain,
  publicOf_afterDomain,
  publicOf_depth,
  publicOf_blockCount,
  publicOf_beforeDigest,
  publicOf_afterDigest,
  payloadInputs_length,
  blockInputs_length,
  endpointHashSites_length,
  endpointHashSites_live,
  descriptor_shape_exact,
  cost_exact,
  traceOf_hashes,
  trace_complete,
  public_pin_modEq,
  satisfying_root_exact,
  satisfying_path_exact,
  satisfying_layout_words_exact,
  satisfying_trace_binds_exact_receipt,
  satisfying_trace_relation_sound,
  satisfying_public_chain_links,
  public_chain_link_tamper_refused,
  Reference.deep_layout_depth,
  Reference.deep_block_count,
  Reference.deep_cost_exact,
  Reference.deep_all_sites_live
]

end Dregg2.Calculus.IntensionalCCCInteractionMultiBlockDescriptorIR2
