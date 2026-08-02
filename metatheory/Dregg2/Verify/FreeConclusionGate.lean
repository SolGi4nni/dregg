/-
# Dregg2.Verify.FreeConclusionGate — WHERE THE FREE-CONCLUSION GATE RUNS.

`Dregg2/Verify/FreeConclusionRatchet.lean` is the machinery; this module is the INVOCATION, and it
is a separate file for exactly one reason: **the gate can only see the keystones that are in scope
where it runs.** It imports every `KeystoneAudit*` module in the tree, so the whole
`@[load_bearing_keystone]` corpus is in the environment when `#free_conclusion_ratchet` fires, and
the machinery FAILS CLOSED (`minKeystones`) if that ever stops being true.

⚑ **AN IMPORT LIST IS A FAIL-OPEN SURFACE, so it is not the only defence.** A new `KeystoneAudit*`
module that nobody adds here would be invisible to the gate — the same class as the un-called
initializer. Two things stand against it: the scale gate below (which only catches a LOSS, not a
missing addition), and the invocation of `#free_conclusion_ratchet` at the end of `Dregg2.lean`,
which sees the corpus through the ROOT's imports rather than through this list.

⚑ THAT SECOND SENTENCE WAS FALSE WHEN FIRST WRITTEN AND IS NOW TRUE — recorded rather than quietly
fixed, because a gate documenting a backstop it does not have is the worst possible place for "a name
is a claim", and this was at the exact line documenting its own weakest surface. An audit measured it:
the only occurrence of `#free_conclusion_ratchet` in the root was prose inside an import comment. The
invocation was then added. If you are reading this and want to check rather than trust it — which is
the whole lesson — `rg -n '^#free_conclusion_ratchet' Dregg2.lean` must return a line. This module exists
so the gate is buildable and testable on its own — `lake build Dregg2.Verify.FreeConclusionGate`,
no root build required — and so `scripts/free_conclusion_canary.lean` has one import to name.
-/
import Dregg2.Verify.FreeConclusionRatchet
import Dregg2.Verify.FreeConclusionSpecimens
import Dregg2.Verify.KeystoneAuditNonAmp
import Dregg2.Verify.KeystoneAuditAuthModes
import Dregg2.Verify.KeystoneAuditIntegrity
import Dregg2.Verify.KeystoneAuditFreshness
import Dregg2.Verify.KeystoneAuditUnfoolability
import Dregg2.Verify.KeystoneAuditSupply
import Dregg2.Verify.KeystoneAuditConservation
import Dregg2.Verify.KeystoneAuditTransport
import Dregg2.Verify.KeystoneAuditRunnable
import Dregg2.Verify.KeystoneAuditSystemRoots
import Dregg2.Verify.KeystoneAuditArgusReceipt
import Dregg2.Verify.KeystoneAuditTerminalAdapters

set_option autoImplicit false

namespace Dregg2.Verify.FreeConclusionGate

#free_conclusion_ratchet

end Dregg2.Verify.FreeConclusionGate
