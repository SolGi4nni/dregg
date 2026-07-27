/-
Admin — the proven decisions behind the operator admin API (`crates/dataplane/src/admin.rs`).

The admin listener is an untrusted operator sidecar; the SAFETY-CRITICAL choices
it drives are proven here:

  * `Admin.Reload`  — config reload fail-safe: an invalid config is rejected, not
    applied (the proven `Dsl.Config.parseOn` parser is the gate);
  * `Admin.Drain`   — graceful-drain monotonicity: once draining, stays draining,
    no new connection admitted (composing the proven `Drain` FSM);
  * `Admin.Cache`   — cache purge invalidation: a purged key thereafter misses.
-/

import Admin.Reload
import Admin.Drain
import Admin.Cache
