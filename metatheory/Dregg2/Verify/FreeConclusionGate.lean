/-
# Dregg2.Verify.FreeConclusionGate — WHERE THE FREE-CONCLUSION GATE RUNS.

`Dregg2/Verify/FreeConclusionRatchet.lean` is the machinery; this module is the INVOCATION, and it
is a separate file for exactly one reason: **the gate can only see the keystones that are in scope
where it runs.** It imports every `KeystoneAudit*` module in the tree, so the whole
`@[load_bearing_keystone]` corpus is in the environment when `#free_conclusion_ratchet` fires, and
the machinery FAILS CLOSED (`minKeystones`) if that ever stops being true.

⚑ **AN IMPORT LIST IS A FAIL-OPEN SURFACE, so it is not the only defence.** A new `KeystoneAudit*`
module that nobody adds here would be invisible to the gate — the same class as the un-called
initializer. ⚠ AND THE SECOND DEFENCE THIS PARAGRAPH CLAIMED DOES NOT EXIST — corrected rather than
quietly dropped, because a gate documenting a backstop it does not have is the worst possible place
for that sin. It said "the invocation of `#free_conclusion_ratchet` at the end of `Dregg2.lean`,
which sees the corpus through the ROOT's imports rather than through this list". There is no such
invocation: the only occurrence of that name in `Dregg2.lean` is prose inside its own import comment.
So exactly ONE structural defence stands — the scale gate below, which catches a LOSS and not a
missing addition — plus the textual corpus check in `scripts/free_conclusion_check.sh`. Adding the
root invocation is real remaining work and it is what would close the fail-open. This module exists
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
