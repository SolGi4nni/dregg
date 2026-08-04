/-
SCRATCH executable: emit the Pasta ALU descriptor (the in-AIR Kimchi/Wrap verifier's ROW) and its
honest three-operation trace fixture.

  lake env lean --run EmitPastaAlu.lean fp    > ../circuit/descriptors/by-name/pasta-alu-sound.json
  lake env lean --run EmitPastaAlu.lean fq    > ../circuit/descriptors/by-name/pasta-alu-fq-sound.json
  lake env lean --run EmitPastaAlu.lean trace > ../circuit/tests/fixtures/pasta-alu-sound-trace.txt

The descriptors are `Dregg2.Circuit.Emit.MinaWrapVerifierAir.{fpAluDesc, fqAluDesc}`, each
`EffectLower.lowerAir` of the source `EffectAir` `pastaAluAir` — House Law #1's endpoint form:
there is no hand-written `VmConstraint2` list for a re-emission to drift from. This file only
RENDERS; it authors nothing.

⚑ The trace is EIGHT rows: the honest multiply, add and sub rows, padded to a power-of-two height
by repeating the multiply. Every declared range lookup constrains its wire on EVERY row
(`LookupSpec` carries no guard), so the padding is a copy of a legal row rather than zeros.
`SEL_CHAIN` is `0` on every row, so the emitted fixture is eight UNRELATED Pasta operations — which
is `unchained_transition_relates_nothing` on the wire, not a shortcut.

⚑ **AND THE MACHINE** (`MinaWrapVerifierProgram`): the register-file + instruction-ROM descriptor
and its honest S-box run, which is the first emitted object in this cone whose PUBLIC INPUTS say
what it computes.

  lake env lean --run EmitPastaAlu.lean sbox      > ../circuit/descriptors/by-name/pasta-sbox-prog.json
  lake env lean --run EmitPastaAlu.lean sboxtrace > ../circuit/tests/fixtures/pasta-sbox-prog-trace.txt
  lake env lean --run EmitPastaAlu.lean sboxpis   > ../circuit/tests/fixtures/pasta-sbox-prog-pis.txt
-/
import Dregg2.Circuit.Emit.MinaWrapVerifierAir
import Dregg2.Circuit.Emit.MinaWrapVerifierProgram

open Dregg2.Circuit.DescriptorIR2 (emitVmJson2)
open Dregg2.Circuit.Emit.MinaWrapVerifierAir

def render (r : List Int) : String := String.intercalate " " (r.map toString)

/-- mul · add · sub · mul · mul · add · sub · mul — eight rows, all three operations exercised,
and a power-of-two height. Every `SEL_CHAIN` is `0`. -/
def traceText : String :=
  let m := render aluMulRow
  let a := render aluAddRow
  let s := render aluSubRow
  String.intercalate "\n" [m, a, s, m, m, a, s, m] ++ "\n"

/-- ⚑ The CHAINED fixture: row 0 multiplies with `SEL_CHAIN = 1` and row 1 adds `Z + 0 = Z`, so the
32 chain legs hold with the selector ON. Rows 2..7 are unchained filler at a power-of-two height. -/
def chainTraceText : String :=
  let c0 := render aluChainRow0
  let c1 := render aluChainRow1
  let m := render aluMulRow
  let a := render aluAddRow
  let s := render aluSubRow
  String.intercalate "\n" [c0, c1, m, a, s, m, a, s] ++ "\n"

/-- ⚑ The MACHINE's honest S-box run: eight rows, `x ↦ x⁷` at the `PastaField` KAT operand, with
the register file, the program counter and the ROM-pinned immediates all filled by
`MinaWrapVerifierProgram.runRows` — the Lean interpreter, from the instruction list. No cell here
is asserted from what the program was supposed to do; every one is computed from the inputs. -/
def sboxTraceText : String :=
  String.intercalate "\n"
    ((Dregg2.Circuit.Emit.MinaWrapVerifierProgram.sboxTrace
      Dregg2.Circuit.Emit.MinaWrapVerifierProgram.SBOX_X).map render) ++ "\n"

/-- The `2^10` run of the same machine: four S-box multiplies then 1 020 padding adds, so the
per-instruction price is a measured slope and not an 8-row fixed cost divided by eight. -/
def longTraceText : String :=
  String.intercalate "\n"
    ((Dregg2.Circuit.Emit.MinaWrapVerifierProgram.longTrace
      Dregg2.Circuit.Emit.MinaWrapVerifierProgram.SBOX_X).map render) ++ "\n"

/-- The 64 public inputs: the input's 32 limbs then the claimed output's. -/
def sboxPisText : String :=
  render Dregg2.Circuit.Emit.MinaWrapVerifierProgram.sboxPIs ++ "\n"

def main (args : List String) : IO Unit :=
  match args with
  | ["fp"]         => IO.println (emitVmJson2 fpAluDesc)
  | ["fq"]         => IO.println (emitVmJson2 fqAluDesc)
  | ["trace"]      => IO.print traceText
  | ["chaintrace"] => IO.print chainTraceText
  | ["sbox"]       => IO.println (emitVmJson2 Dregg2.Circuit.Emit.MinaWrapVerifierProgram.sboxDesc)
  | ["sboxtrace"]  => IO.print sboxTraceText
  | ["sboxpis"]    => IO.print sboxPisText
  | ["long"]       => IO.println (emitVmJson2 Dregg2.Circuit.Emit.MinaWrapVerifierProgram.longDesc)
  | ["longtrace"]  => IO.print longTraceText
  | _              => IO.eprintln
      "usage: EmitPastaAlu.lean (fp|fq|trace|chaintrace|sbox|sboxtrace|sboxpis|long|longtrace)"
