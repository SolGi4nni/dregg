-- Iocore: the completion-queue reactor as a verified sans-IO transition system.
--
-- A clean-room MODEL of a multiplatform I/O completion reactor: the
-- generation-tagged ABA-safe operation slab (`Iocore.Slab`) and the
-- submit/complete/inline reactor (`Iocore.Reactor`) whose safety invariants —
-- ABA safety, no-lost/no-double completion, inline≡deferred — are theorems, not
-- comments. The running Rust reactors are the realization; this is the spec they
-- refine. Composes the slab lease with `Uring.RecycleOnce`.
import Iocore.Slab
import Iocore.Reactor
