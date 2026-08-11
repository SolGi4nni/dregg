/-
# CheckVkPinLiterals — every `*_VK_LANES` literal, RESOLVED IN LEAN against the served tree.

⚑ **WHAT THIS IS THE PAYOFF OF.** A `vk_pin` is nine `Faithful9` lanes of a descriptor's semantic
fingerprint. Until `Dregg2.Circuit.DescriptorCanonical` landed, an AIR author could not produce that
value in Lean at all — the canonical ENCODER was Rust-only — so fourteen `*_VK_LANES` constants
across seven modules are digits somebody ran `cargo run --example conj_fingerprint` for and TYPED IN.
This driver recomputes the whole chain (`descriptor JSON → canonical bytes → BLAKE3 derive-key →
nine lanes`) **in Lean, with no Rust anywhere in the path**, for every served descriptor, and then
asks of each literal: *which served descriptor do you pin?*

## ⚑ IT RESOLVES BY VALUE, NOT BY A HAND-WRITTEN MAP

Nothing here says "`CHAINLINK_VK_LANES` pins `pasta-fq-chainlink.json`". A table of literal→file
would be one more transcription, and a stale one is invisible in exactly the way the literals are.
Each literal is looked up in the computed table of all 159 served fingerprints, and the answer is
whatever descriptor's lanes it equals — or **nothing**, which is the interesting answer.

## ⚠ THE THREE `FORGED_*` LITERALS MUST MATCH NOTHING

`LightClientMinaAir`'s three forged pins are deliberate falsifiers: a leg pinned to one must be
UNSATISFIABLE against every real sub-program. If a forged literal ever matched a served descriptor,
the falsifier it powers would have quietly become a no-op. That check is tree-independent in spirit
and is a HARD failure here.

## ⚠ WHAT THIS DELIBERATELY DOES NOT DO

It does not decide which literal *should* have been. A verdict of that kind names a tree, not a fact,
and this tree is mid-reshape. `--strict` turns "a live literal matches nothing served" into a
non-zero exit for a caller who wants that; the default reports it and exits zero on it, because
`circuit/tests/vk_pin_closure_over_the_served_tree.rs` already carries that verdict and a second
copy of it would be a twin, not a second witness.

Usage: `lake env lean --run CheckVkPinLiterals.lean <descriptor-root> [--strict]`
-/
import Dregg2.Circuit.DescriptorCanonicalJson
import Dregg2.Circuit.Emit.LightClientMinaAir
import Dregg2.Circuit.Emit.LightClientMinaLinkAir
import Dregg2.Circuit.Emit.MinaAccumulatorAir
import Dregg2.Circuit.Emit.MinaWrapClosingAir
import Dregg2.Circuit.Emit.MinaSeams
import Dregg2.Circuit.Emit.MinaBodyPreimageSeams
import Dregg2.Circuit.Emit.MinaBodyHashRelimbSeams

open Dregg2.Circuit.DescriptorCanonical
open Dregg2.Circuit.DescriptorCanonicalJson

/-- One pin literal: where it is written, and what it says. -/
structure PinSite where
  /-- The fully qualified Lean name, so a reader can go straight to it. -/
  site : String
  /-- ⚑ A deliberate falsifier that must match NOTHING served. -/
  forged : Bool
  /-- The nine literal lanes. -/
  lanes : List Int

/-- ⚑ **EVERY `*_VK_LANES` LITERAL IN THE TREE**, by reference rather than by transcription: each
entry names the actual `def`, so a literal that moves takes this table with it and a literal that is
deleted breaks this file rather than leaving a row that silently checks nothing. -/
def pinSites : List PinSite :=
  [ ⟨"Emit.LightClientMinaAir.CHAINLINK_VK_LANES", false,
      Dregg2.Circuit.Emit.LightClientMinaAir.CHAINLINK_VK_LANES⟩
  , ⟨"Emit.LightClientMinaAir.LINK_VK_LANES", false,
      Dregg2.Circuit.Emit.LightClientMinaAir.LINK_VK_LANES⟩
  , ⟨"Emit.LightClientMinaAir.CONJ_VK_LANES", false,
      Dregg2.Circuit.Emit.LightClientMinaAir.CONJ_VK_LANES⟩
  , ⟨"Emit.LightClientMinaAir.FORGED_VK_LANES", true,
      Dregg2.Circuit.Emit.LightClientMinaAir.FORGED_VK_LANES⟩
  , ⟨"Emit.LightClientMinaAir.FORGED_LINK_VK_LANES", true,
      Dregg2.Circuit.Emit.LightClientMinaAir.FORGED_LINK_VK_LANES⟩
  , ⟨"Emit.LightClientMinaAir.FORGED_CONJ_VK_LANES", true,
      Dregg2.Circuit.Emit.LightClientMinaAir.FORGED_CONJ_VK_LANES⟩
  , ⟨"Emit.LightClientMinaLinkAir.ABSORB_VK_LANES", false,
      Dregg2.Circuit.Emit.LightClientMinaLinkAir.ABSORB_VK_LANES⟩
  , ⟨"Emit.LightClientMinaLinkAir.FP_CHAINLINK_VK_LANES", false,
      Dregg2.Circuit.Emit.LightClientMinaLinkAir.FP_CHAINLINK_VK_LANES⟩
  , ⟨"Emit.MinaAccumulatorAir.MINA_HEAD_VK_LANES", false,
      Dregg2.Circuit.Emit.MinaAccumulatorAir.MINA_HEAD_VK_LANES⟩
  , ⟨"Emit.MinaWrapClosingAir.ABSORB_VK_LANES", false,
      Dregg2.Circuit.Emit.MinaWrapClosingAir.ABSORB_VK_LANES⟩
  , ⟨"Emit.MinaSeams.ENDO_VK_LANES", false, Dregg2.Circuit.Emit.MinaSeams.ENDO_VK_LANES⟩
  , ⟨"Emit.MinaSeams.HEAD_VK_LANES", false, Dregg2.Circuit.Emit.MinaSeams.HEAD_VK_LANES⟩
  , ⟨"Emit.MinaBodyPreimageSeams.BODY_BITS_VK_LANES", false,
      Dregg2.Circuit.Emit.MinaBodyPreimageSeams.BODY_BITS_VK_LANES⟩
  , ⟨"Emit.MinaBodyHashRelimbSeams.RELIMB_VK_LANES", false,
      Dregg2.Circuit.Emit.MinaBodyHashRelimbSeams.RELIMB_VK_LANES⟩ ]

/-- Every `.json` under a root, recursively, minus the registry manifest. -/
partial def collectJson (dir : System.FilePath) : IO (Array System.FilePath) := do
  let mut out := #[]
  for e in ← dir.readDir do
    if ← e.path.isDir then
      out := out ++ (← collectJson e.path)
    else if e.path.extension == some "json" && e.path.fileName != some "PROVENANCE.json" then
      out := out.push e.path
  return out

def main (args : List String) : IO UInt32 := do
  let some (root : String) := args[0]? | do
    IO.eprintln "usage: CheckVkPinLiterals <descriptor-root> [--strict]"
    return 2
  let strict := args.contains "--strict"

  -- ⚑ The served table, computed ENTIRELY IN LEAN: parse the file, encode the canonical record,
  -- derive-key it, pack the nine lanes. No Rust, no stored fingerprint.
  let files ← collectJson (System.FilePath.mk root)
  let mut table : Array (String × String × List Nat) := #[]
  let mut refused := 0
  for f in files.qsort (fun a b => a.toString < b.toString) do
    let src ← IO.FS.readBinFile f
    match parseDescriptor src with
    | .error _ => refused := refused + 1   -- not an ir:2 record (seams, table AIRs, v1 wire)
    | .ok d =>
      match vkPinLanesNatOf d with
      | .ok (some lanes) => table := table.push (d.name, f.toString, lanes)
      | _ => refused := refused + 1

  if table.size < 100 then
    IO.eprintln s!"REFUSED: only {table.size} descriptors resolved under {root}; a lookup table that small makes every \"matches nothing\" verdict meaningless"
    return 2

  IO.println s!"vk_pin literal resolution: {table.size} served descriptors fingerprinted in pure Lean"
  IO.println s!"  ({files.size} json files walked, {refused} not ir:2 records)"
  IO.println ""

  let mut forgedHits : Array String := #[]
  let mut unresolved : Array String := #[]
  let mut malformed : Array String := #[]

  for p in pinSites do
    let lanesNat := p.lanes.map Int.toNat
    let shapeOk := p.lanes.length == 9 ∧ p.lanes.all (· ≥ 0)
    let hits := table.filter (fun (_, _, l) => l == lanesNat)
    let zero := p.lanes == List.replicate 9 (0 : Int)
    let tag := if p.forged then "FORGED " else ""
    if ¬ shapeOk then
      malformed := malformed.push s!"  {p.site}: not nine non-negative lanes ({p.lanes})"
      IO.println s!"  {tag}{p.site}\n      MALFORMED: {p.lanes}"
    else if zero then
      IO.println s!"  {tag}{p.site}\n      all-zero placeholder — declares itself unmeasured, pins nothing"
    else if h : hits.size > 0 then
      let (nm, path, _) := hits[0]
      if p.forged then
        forgedHits := forgedHits.push s!"  {p.site} matches served `{nm}` ({path})"
        IO.println s!"  {tag}{p.site}\n      ⚠ MATCHES `{nm}`"
      else
        IO.println s!"  {p.site}\n      pins `{nm}`  ({path})"
    else
      if p.forged then
        IO.println s!"  {tag}{p.site}\n      matches nothing served — as a falsifier must"
      else
        unresolved := unresolved.push s!"  {p.site}: {p.lanes}"
        IO.println s!"  {p.site}\n      ⚠ MATCHES NO SERVED DESCRIPTOR"

  IO.println ""
  IO.println s!"  {pinSites.length} literals; {unresolved.size} name no served program; {forgedHits.size} forged literals collide with a served one"

  unless malformed.isEmpty do
    IO.eprintln "FAIL: a pin literal is not nine non-negative lanes"
    for m in malformed do IO.eprintln m
    return 1

  unless forgedHits.isEmpty do
    IO.eprintln "FAIL: a deliberate FORGED_* falsifier matches a SERVED descriptor."
    for m in forgedHits do IO.eprintln m
    IO.eprintln "⚠ A forged pin that names a real program is a falsifier that has stopped falsifying:"
    IO.eprintln "  the leg it powers became satisfiable and its refusal test now proves nothing."
    return 1

  unless unresolved.isEmpty do
    IO.eprintln ""
    IO.eprintln s!"⚠ {unresolved.size} live pin literal(s) name a program no descriptor in this tree has:"
    for m in unresolved do IO.eprintln m
    IO.eprintln "  These nine numbers are now COMPUTABLE in Lean —"
    IO.eprintln "  `DescriptorCanonical.vkPinLanesOf <the descriptor term>` — so the repair is to"
    IO.eprintln "  point each literal at its descriptor rather than to retype the digits."
    IO.eprintln "  ⚠ Which literal is wrong versus which descriptor moved is a question about THIS"
    IO.eprintln "  tree, not a fact; this driver reports and does not adjudicate. --strict exits 1."
    if strict then return 1

  return 0
