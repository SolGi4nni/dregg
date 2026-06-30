# dregg-agent — a real, flexible, live operator agent you can audit

Hand a **live model** an *arbitrary* natural-language goal, a **budget**, and a
**cap bundle**. It runs a genuine **reason → act → observe** loop: the model
decides the next tool call, and every call is **cap-gated · metered · receipted**
and executed **for real** — a real shell, real fs, real http, real `git clone`,
or a budget-gated spend. The whole run is one cryptographic receipt chain you can
re-verify yourself, offline, trusting no host.

There is **no script**. Hand it a different `--goal` and it genuinely adapts —
that is the proof it is not a puppet.

Built on [`dregg-agent`](../) — the open-source (AGPL), substrate-only,
cap-bounded / budget-bounded / receipted agent runtime. No cloud, no control plane.

## Run it (one command)

```sh
bash demo/business.sh
```

Needs a model key in `~/.nvidiakey` (or `NVIDIA_API_KEY`). It builds once, runs
the live agent on a real default goal (clone a tiny repo, inspect it, hit the
GitHub API, pay for the work — all real), narrates each real step, writes
`demo/run.json`, **re-witnesses it**, and shows a **tampered line caught**.

Hand it your own goal:

```sh
bash demo/business.sh "clone https://github.com/octocat/Hello-World, read its \
   files, and report what the repo is" --caps shell,fs,git:github.com --budget 800
```

## What the judge sees

1. **A live model reasons and acts.** The default goal makes a real NVIDIA
   Nemotron agent `git clone` a repo, `list_dir` + `fs_read` it, `http_get` the
   GitHub API, and `spend` from its budget — each decided live from the previous
   observation. Native OpenAI `tool_calls` drive it (confirmed against the live
   endpoint).
2. **Every tool is on a leash.** Each call is cap-gated **per-tool AND
   per-resource**: `shell` is granted but confined to the workdir; `fs` only
   under the workdir root (a `/etc/passwd` read is refused **before it runs**, no
   receipt); `http` only to granted hosts; the `spend` is drawn from the budget
   cell, so an over-budget spend is refused **in-band before any money moves**.
3. **It is all receipted.** Every admitted action is sealed into a prev-hash
   chained, ed25519-signed receipt (with a witnessed `(command · inputs ·
   result)` binding), so a forged "it succeeded / I barely spent" breaks the
   signature.
4. **SCALE — no amplify.** It forks a sub-agent with a *narrower* cap bundle it
   provably cannot exceed (an out-of-bundle http / spend is refused on both axes).
5. **PROVE.** `dregg-agent verify run.json` re-witnesses the whole run offline —
   chain intact + signed, consumed ≤ ceiling, sub-agent chain too. Then
   `--tamper` flips one receipted line and the proof **rejects it**
   (`BadSignature`).

## The operator toolkit (every tool rides the same cap · meter · receipt rail)

| tool | what it does | cap (per-resource) |
|------|--------------|--------------------|
| `shell` | real bash: persistent cwd, pipes/`&&`, real stdout/stderr/exit, timeout | `shell` (workdir-confined) |
| `fs_read`/`fs_write`/`list_dir`/`mkdir` | real fs, scoped to the workdir root | `fs-read:<path>` / `fs-write:<path>` (prefix grant) |
| `http_get` | real outbound GET | `http:<host>` (per-host egress) |
| `git_clone` | real shallow clone into the workdir | `http:<host>` |
| `spend` (`stripe_pay`) | budget-gated payout | `invoke:stripe_pay` + the budget draw |
| `cell_read`/`cell_write` | real committed state | `cell-read:`/`cell-write:<path>` |

The cap bundle is a **signed** `dga1_` credential; resource scopes ride
`AttrPrefix`, so a sub-agent can only ever **narrow** them (`attenuate_subset`).

## Caps (`--caps`, comma-separated)

`shell`, `fs`, `git:HOST`, `http:HOST`, `spend`, `run_tests`, `cell:/path` — each
is a per-tool / per-resource grant. Default:
`shell,fs,git:github.com,http:api.github.com,spend`.

## The money leg (honest)

The budget draw is **always real** (a metered ledger cell — the spend bound is a
theorem about the cell, not a watchdog). The live **Stripe** leg is real **only
with a test key**: put an `sk_test_…` key in `~/.stripekey` (or `STRIPE_API_KEY`)
and `stripe_pay` makes a genuine Stripe **test-mode** PaymentIntent
(`pm_card_visa`). Without it, the spend is a real budget draw labeled honestly
("budget enforced; Stripe live leg needs a test key") — never a fake "✓ paid".

## Capture a good run for the film

```sh
dregg-agent run --record demo/resp.json --out demo/run.json    # live; saves the brain
dregg-agent run --replay demo/resp.json                        # re-runs it, tools FOR REAL
```

Replaying a captured **real** run is legit (the model's decisions are re-fed; the
tools execute for real against the same workdir). The default is always live.

## Verify it yourself

```sh
dregg-agent verify demo/run.json          # re-witness offline (green)
dregg-agent verify --tamper demo/run.json # one line flipped → caught (BadSignature)
```

Nothing here is mocked: the model really reasons, the tools really run, the
budget refusal is real, and the receipts really re-witness. The only recorded
artifact is the optional `--replay` capture — and it re-executes the real tools.
