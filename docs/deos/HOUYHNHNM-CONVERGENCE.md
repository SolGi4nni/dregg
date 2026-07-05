# The Houyhnhnm Convergence

*How dregg/deos already embodies fare's Houyhnhnm Computing, where the gaps are, and how
those same gaps are exactly what burned David's buildr team (the Lunar Town Council, 2026-06-22).*

Three texts, one shape seen from three angles: fare's **Houyhnhnm Computing** (the 11-chapter
ideal), **dregg/deos** (the artifact), and the **Lunar Town Council retrospective** (a fleet's
hard-won lessons under fire). The council *independently rediscovered* the Houyhnhnm principles
the hard way; dregg is the substrate that makes them STRUCTURAL instead of hand-rolled bash that
churns 101 commits never-once-in-a-known-good-state. "How can we be more Houyhnhnm" and "what
would have helped David's team" turn out to be the **same question**.

## The principle-by-principle map

| Houyhnhnm principle (ch.) | dregg/deos today | the David's-team wound it answers |
|---|---|---|
| **Orthogonal persistence** — everything persists by default, no "save" button, *you never lose your session* (ch2–3) | the blocklace IS the persistence journal; `World::open_recovering` recovers an image; **and boot is now wired to it** — `starbridge-v2/src/durable_desktop.rs::boot_desktop_world` boots over `World::open_recovering` (recover → re-execute → verify), and `session::open_session_world` opens the durable per-principal image on login; the ephemeral `demo_world` is now only an explicit escape hatch (WM-3, LANDED) | "in-session wakes don't survive a full reboot"; "monitors die on compaction/reboot"; restart loses state |
| **Persistence log = input events + deterministic replay** (ch3) | the blocklace + the replay tape + symbolic/collapse — *exactly this* | the recovery story: replay from the log, not reconstruct by hand |
| **Virtualization = branching; errors stay imaginary in unmerged branches** (ch3–4) | **the rehydratable membrane + branch-and-stitch + the TIME scrubber — built** | the team used 157 worktrees / 271 branches as the *human-hack* version; the destructive codex-wedge had no branch isolation |
| **The Monitor** — an external simple-but-complete system that stops, inspects, fixes, restarts a broken system; recursively virtualizable (ch3, ch6) | the cockpit inspector + the seL4 monitor PD + the live image — **and now the recovery monitor itself: `sel4/dregg-firmament/src/recovery_monitor.rs` (the Houyhnhnm Recovery Monitor — reads the live artifact, `RecoveryNotHolding` on claimed-vs-actual divergence, restart-loop escalation, fail-closed post-restart probe; BUILT)** | **THE 15-HOUR WEDGE**: needed exactly this — instead a restart-loop that logged "revert OK" while the live artifact re-wedged every 4 min |
| **Non-stop change / live upgrade from within; code-change-as-a-transaction; linear-logic upgrade (must *explicitly* drop data)** (ch5) | dregg turns are code-change transactions; conservation Σδ=0 *is* the linear-logic discipline; dregg-doc patches | "sanitize-*before*-revert" was a transaction the team had to invent; the shared-revert was non-transactional → re-wedge |
| **"I object to doing things computers can do" / the save-habit is wasted wetware** (ch2) | the witness IS the artifact; receipts; ToolGateway — the computer does the verifying | **THE ROOT FAILURE**: "assertion-over-artifact — a tool asserting success the live artifact refutes" (`revert OK`, `refreshed=5` over dead tokens) |
| **Polycentric kernel** — every subsystem its own kernel; decentralized invariant enforcement; full abstraction *enforced*, not by-convention; linear logic for resources (ch6) | dregg **is** this: cells are polycentric kernels, cell-programs enforce their own invariants, caps = linear logic, the membrane = enforced full abstraction; no single privileged kernel | the RSH was *one central stop-hook layer enforcing a static set* — the un-Houyhnhnm anti-pattern the council named ("structural-proof can become a new overbearing stop-hook religion") |
| **Platforms not applications** — components; "no difference between using and programming"; one file-selector for the whole platform (ch7) | deos apps-as-views + the moldable inspector + the dock | buildr's bb engine *is* a platform; the RSH rituals were app-level bolt-ons that "turned coordination into the work" |
| **Full-abstraction sandbox** — an activity can't tell it's virtualized; protocols are meta-level; *preemptive beats cooperative because programmers are unreliable* (ch8) | the membrane fork-isolation + the sandbox host-PD + ToolGateway; the guest can't tell it's in a fork | **"advisory-under-load was the root failure the entire time"** = cooperative multitasking (relies on the agent obeying). The Houyhnhnm fix = preemptive = deterministic gates = the council's **enforce-not-advise** verdict, verbatim |
| **Build system = the dev system at the meta-level**; hermetic, deterministic, source-addressed; "build from HEAD" = the branches that pass their tests; four roles (author/user/integrator/end-user); hot-patching decouples release cycles (ch9) | circuits emitted-from-Lean + the keystone test-gate; dregg is hermetic + deterministic *by construction* | the fab provisioning gap (`lake absent` = non-hermetic build); the keystone test-gate = build-from-HEAD; the live fix-atom = hot-patching |
| **The Urbit critique** — a frozen central VM is a sham (jets not bug-compatible with Nock); global deterministic semantics *only* matters to verify *others'* computations; metaprogramming + proven-equivalence is the real answer (ch10) | dregg is the **principled** resolution: verified semantics exactly where it matters (cross-party light-client unfoolability), the circuit *proven equivalent* to the executor (the anti-ghost tooth), both emitted from one Lean source — no lying fast-path | the philosophical grounding for why "mount herdr on dregg" (Fork B) is the right substrate, not a new Nock |
| **Bad tools not bad users; preemptive enforcement; Low Time-Preference / general principles for long-run tools** (ch11) | — (this is the *method*, not a feature) | the **whole retrospective**: David's exhaustion from "a harness that fought its operator"; the "fewer interruptions for a naive solo user" metric; salvage-vs-refork = a Low-Time-Preference call; "calibrate a proven thing, don't burn it" |

## The distilled answer

dregg/deos already embodies more Houyhnhnm principles than any extant system — it *is* the
polycentric kernel, virtualization-as-branching, linear-logic resources, artifact-over-assertion,
and verified-semantics-where-it-matters. **The two principles that were once designed-but-not-yet-realized
— precisely the gaps that burned David's team — have since LANDED.**

Two stood out, both highest-Houyhnhnm and highest-would-have-helped, both now closed:

1. **Orthogonal persistence / never-lose-your-session** (ch2–3) — boot resumes the *exact* image
   where it closed; no save button; the blocklace is the log. The machinery (`World::open_recovering`,
   redb dual-write) exists AND is now wired into boot: `starbridge-v2/src/durable_desktop.rs::boot_desktop_world`
   boots the desktop over `World::open_recovering` (recover → re-execute → verify), and
   `session::open_session_world` opens the durable per-principal image on login. This directly answers
   "in-session wakes don't survive reboot." → **WM-3, LANDED**.

2. **The Monitor** (ch3, ch6) — a *Houyhnhnm recovery monitor*: an external, simple-but-complete
   watcher that reads the **live artifact** (never a self-reported "OK"), detects claimed-vs-actual
   divergence (the council's `RECOVERY_NOT_HOLDING`; cred-steward's "every auto-process must prove
   it fired on real input AND that the result persisted"), and can stop / inspect / fix / restart
   a wedged subsystem — recursively (a monitor of monitors). This is *exactly* the thing that would
   have ended the 15-hour codex-wedge in minutes instead of fighting the operator for a day. It is
   now **built**: `sel4/dregg-firmament/src/recovery_monitor.rs` is that monitor — the firmament's
   simplest component (reads live cell state, `RecoveryNotHolding` on divergence, restart-loop
   escalation, fail-closed post-restart probe; its module doc names this convergence essay directly).
   → THE standout build, LANDED.

The deepest point: the council, under fire, re-derived Houyhnhnm computing —
*enforce-not-advise* = preemptive>cooperative (ch8); *artifact-over-assertion* = "I object to doing
things computers can do" + the monitor (ch2–3); the *bb append-only log* = the persistence journal
(ch3); *worktree isolation* = virtualization-as-branching (ch3); *"fewer interruptions for a naive
solo user"* = "wise men blame the toolsmiths" (ch11). buildr learned the principles the hard way;
dregg is the substrate that makes them structural — which is why Fork B (mount herdr on dregg) and
Fork A (calibrate the RSH) are one destination.
