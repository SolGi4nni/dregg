/-
# EmitTurnAuthProbe — emit the IN-AIR AUTHORIZATION gadget as a standalone byte-exact descriptor.

**Lean-authored AIR.** `Dregg2/Circuit/Emit/TurnAuthLamportEmit.lean` authors every constraint;
this file only serialises. Rust parses the bytes and supplies a witness — it constructs nothing.

Emits `withTurnAuth` over a minimal 3-column base whose columns are the TURN IDENTITY
`(src, actor, dst)` — the three that `transferCapOpenTB` publishes to PI 46/47/48 and that nothing
else in the deployed circuit constrains. Here they are absorbed into the turn-digest lookup whose
output the signature's message bits recompose, so moving `actor` or `dst` moves the signed message.

Two instances, both the SAME generator:

  * `nb = 1` — 31 signed bits. The per-bit machinery (sig lookup, select gate, boolean gate, the
    public-key fold, the authority-root PI pins) is identical to the deployed instance at every
    `k`; this is the fast prove-through the refusal teeth run against.
  * `nb = NB = 8` — the DEPLOYED instance: 248 signed bits, one 31-bit block per felt of the chip's
    8-felt squeeze, so every digest felt is signed and the message determines the turn digest.

SCRATCH executable: `lake env lean --run EmitTurnAuthProbe.lean`. Prints `<filename>\t<json>` per
line (the `EmitByName` convention).
-/
import Dregg2.Circuit.Emit.TurnAuthLamportEmit

open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 emitVmJson2)
open Dregg2.Circuit.Emit.TurnAuthLamportEmit (withTurnAuth NB AUTH_SPAN ELL)

/-- The probe base: three columns carrying the turn identity `(src, actor, dst)`, no constraints,
no public inputs. Everything else is the authorization gadget. -/
def probeBase (name : String) : EffectVmDescriptor2 :=
  { name        := name
  , traceWidth  := 3
  , piCount     := 0
  , tables      := []
  , constraints := []
  , hashSites   := []
  , ranges      := [] }

/-- The probe descriptor at block count `nb`: the turn columns welded into the signed message. -/
def probe (nb : Nat) (name : String) : EffectVmDescriptor2 :=
  withTurnAuth (probeBase name) nb [0, 1, 2]

/-- The fast instance (31 signed bits) the refusal teeth run against. -/
def probeNb1 : EffectVmDescriptor2 := probe 1 "dregg-turn-auth-lamport-probe-nb1::v1"

/-- The DEPLOYED instance (248 signed bits — every digest felt signed). -/
def probeNb8 : EffectVmDescriptor2 := probe NB "dregg-turn-auth-lamport-probe-nb8::v1"

-- Shape pins the Rust witness builder mirrors.
#guard probeNb1.traceWidth == 3 + AUTH_SPAN 1
#guard probeNb8.traceWidth == 3 + AUTH_SPAN NB
#guard probeNb1.piCount == 8
#guard probeNb8.piCount == 8
#guard ELL 1 == 31
#guard ELL NB == 248

def main : IO Unit := do
  IO.println s!"turn-auth-lamport-probe-nb1.json\t{emitVmJson2 probeNb1}"
  IO.println s!"turn-auth-lamport-probe-nb8.json\t{emitVmJson2 probeNb8}"
