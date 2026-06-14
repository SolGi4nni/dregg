// =============================================================================
// Section 10: deos
// =============================================================================

#import "../defs.typ": lean
= deos: the agentic desktop <sec-deos>

deos is the firmament made visual. It is the userlayer a human or an agent
touches --- windows, the surfaces they render, the compositor that draws them ---
built so that every visual and interactive primitive *reduces to a kernel
theorem*. It adds no new trust: a window is a capability, an interaction is a
turn, and what a viewer may see or do is decided by the capabilities they hold.
The mathematics is the firmament's existing mathematics --- attenuation, the
admission gate, the receipt chain, unfoolability --- restated for pixels,
affordances, and rehydration.

== A window is a capability

A surface is a `(target, rights)` capability over a cell (@sec-firmament). A
window therefore confers no authority beyond its rights, and a view- or
notify-only surface confers no Granovetter edge at all
(#lean("Deos.viewSurface_confers_no_edge"), #lean("Deos.notifySurface_confers_no_edge")):
showing someone a window does not hand them the power to act through it. Narrowing
a surface to fewer rights cannot amplify
(#lean("Deos.surface_attenuate_no_amplify"), an instance of the @sec-authority
attenuation law). This is the foundation deos shares with no conventional desktop:
the right to see is separated from the right to act, and both are capabilities.

The interaction model is declarative and server-rendered in the web's style, with
the ambient-authority soup removed. A cell publishes named, typed *affordances*
--- effect templates --- and an interaction is a verified turn: the "button" is a
capability-gated effect, the rendered "fragment" is the attested post-state
surface, and *who may press it* is decided by held capabilities rather than a
session cookie. An agent fires only the affordances its capabilities authorize ---
the same `required ⊆ held` gate (#lean("Deos.fire_authorized_iff")) --- and the
post-state surface binds the attested root of the turn it produced
(#lean("Deos.firedSurface_binds_attested_root")). Progressive enhancement becomes
*progressive attenuation*: projecting a surface for a viewer is monotone in their
authority (#lean("Deos.projectFor_monotone")), so two agents see exactly the
affordances their respective capabilities allow over one surface.

== Per-viewer non-interference

Because a surface is projected per viewer, deos can state the property a
cross-domain compositor usually only *trusts* its rendering process to provide:
non-interference. A low-authority viewer's render is a function of the
low-authorized state *alone* --- changing a cell that viewer cannot see leaves
their view bit-identical (#lean("Deos.noninterference"),
#lean("Deos.hidden_change_invisible")), a hidden cell is structurally absent from
the projection rather than merely undrawn (#lean("Deos.hiddenCell_absent")), two
viewers diverge by exactly their authority (#lean("Deos.divergence")), and vision
is monotone in capability (#lean("Deos.vision_monotone")). What a viewer sees is
determined by exactly the fragment inside their capability --- the information-flow
sibling of rehydration confinement below.

The compositing underneath is an algebra with the guarantees a windowing system's
correctness rests on, here proved rather than assumed. Damage is exact --- a
present dirties exactly its declared regions and nothing outside them
(#lean("Deos.present_damage_exact")); paint is order-free on a well-formed scene,
so z-order does not affect the pixels (#lean("Deos.paint_order_independent")); and
editing one window cannot perturb another's pixels, the compositional dual of
non-interference (#lean("Deos.render_frame_property")). Re-rendering is functorial
over the per-viewer projection: re-rendering after a state update equals updating
the rendered surface, the central web-framework guarantee
(#lean("Deos.rerender_square")).

== The rehydratable surface

The primitive that only this substrate can offer is the *rehydratable surface*. A
deos snapshot --- a "screenshot" --- is a frame of the certified compositor over
the witness graph, and what it actually embeds is a *sturdy reference behind a
membrane*: a persistable, attenuable capability that, when the image is opened,
re-attaches a live --- or faithfully replayable --- interactive surface. It is not
a faithfulness proof retrofitted onto a dead pixel grid, which would ask a viewer
to instantiate arbitrary author state. The fidelity is upstream and structural:
the frame came out of a compositor whose render is itself a verified projection
over the witness graph, so it can only draw what the graph authorizes. The
snapshot rehydrates because it was never a dead artifact --- it is a paused camera
on a witnessed scene.

The membrane makes rehydration *relational*. Two agents opening the same snapshot
do not reconstruct identical surfaces; each renegotiates, across the membrane, the
slice their capabilities authorize. Reshares compose attenuation across hops ---
re-sharing $A arrow.r B arrow.r C$ confers on $C$ no more than $B$ held, for
chains of any length (#lean("Deos.reshare_chain_attenuates"),
#lean("Deos.reshareN_attenuates")) --- and a widening reshare is darkened, not
granted (#lean("Deos.reshare_refuses_amplification")). Sharing a surface stops
being "I leaked my session" and becomes "I extended a revocable, attenuated,
per-viewer right to re-view." The snapshot is a lossless per-viewer handle, not a
lossy thumbnail: it re-expands faithfully and under attenuation
(#lean("Deos.snapshot_roundtrip"), #lean("Deos.snapshot_roundtrip_attenuated")).

== The liveness type is the confined fragment

The cost of "live *or* replayed" cannot be negotiated away --- if the original
contexts are gone, replay fidelity is bounded by how deterministically the witness
graph captured the scene's nondeterminism --- so the membrane *types* every
reacquisition with one of three values: ${"Live", "ReplayedDeterministic",
"ReconstructedApproximate"}$. The type is not a label of good intent; it is a
*proven confinement readout*, computed from what the witness graph actually
attested. The crown theorem is that #emph[ReplayedDeterministic] is *exactly* the
confined fragment: for a non-live context, it classifies as ReplayedDeterministic
if and only if every interaction it made was a witnessed, attested turn
(#lean("Deos.replayedDeterministic_iff_confined")). A context whose nondeterminism
all flowed through attested turns can be replayed deterministically by construction
(#lean("Deos.replayedDeterministic_replays"), riding the receipt-chain
tamper-evidence of @sec-proofs); a context that reached for nondeterminism *outside*
the membrane --- an unwitnessed clock, an ambient random draw, an un-attested
external call --- is intrinsically #emph[ReconstructedApproximate], because the
very thing that made it nondeterministic was never captured. So the liveness type
is a readout of confinement, not a claim of honesty: the system cannot misreport
which kind of true an opened image hands a viewer, because the classification is
derived from the attested record rather than asserted over it.

The Lean development is kernel-clean throughout: each of these is an existing
kernel proof --- attenuation, the admission gate, the receipt chain, projection
--- restated for surfaces, with the one honest seam being the digest
collision-resistance the replay payoff carries as a named hypothesis (the same
floor carrier of @sec-assurance), never an axiom and never an admitted goal. The
Rust realization of the rehydration and affordance stack ships in
`starbridge-web-surface`; the certified compositor as a sole-framebuffer
protection domain is the frontier piece, @sec-sel4.
