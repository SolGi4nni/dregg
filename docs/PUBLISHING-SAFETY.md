# Publishing Safety — how a secret can never be pushed public again

This is the process rule + the automated backstop that together make the incident that produced this
document **unrepeatable**.

## What happened (the concrete lesson)

The root cause was **process, not a one-off typo**: staging / pre-public content was staged directly on
`main`, and a routine `git push origin main` then carried a secret **public**. The secret was never
supposed to be on `main` — but because `main` was where the staging happened, the normal, muscle-memory
push published it.

The fix is two-layered: **fix the process so `main` is push-safe by construction**, and **add an
automated backstop so a secret is blocked even if the process slips.**

## The process rule (primary — makes `main` push-safe by construction)

1. **`main` holds only vetted, publishable content.** Nothing unvetted lives on it, so a routine
   `git push origin main` can never carry a surprise.
2. **Staging / pre-public / monorepo-subdir additions go on a SEPARATE branch** (e.g.
   `staging-<topic>`), where they are scanned + reviewed. They merge to `main` **only when clean**.
   Never commit staging content directly on `main`.
3. **Review the diff before merging to `main`** — the merge to `main` is the publish gate. Treat it
   like publishing, because it is.

Because `main` is push-safe by construction, the routine `git push origin main` is safe by
construction. The hook below is the *backstop*, not the primary defense.

## The automated backstop (secondary — catches a slip)

A **secret-scanning git hook** (pre-commit **and** pre-push) scans for real-secret shapes and **blocks**:

- **pre-commit** scans the **staged diff** — a secret can't even enter a commit.
- **pre-push** scans the **to-be-pushed commits** — a secret already committed locally can't reach the
  remote. (This is the exact layer that would have caught the incident.)

It prefers [`gitleaks`](https://github.com/gitleaks/gitleaks) (`brew install gitleaks`) and falls back
to a POSIX-grep scan with the same shapes if gitleaks isn't installed, so the guardrail is never
vacuous. Rules + the allowlist live in [`.gitleaks.toml`](../.gitleaks.toml); the hooks live in
[`scripts/git-hooks/`](../scripts/git-hooks/).

### Shapes it blocks

Stripe (`whsec_`, `sk_live_`/`sk_test_`, `pk_`/`rk_`), AWS (`AKIA…`/`ASIA…`), PEM private keys,
GitHub PATs (`ghp_…`, `github_pat_…`), Slack (`xox[baprs]-…`), and high-entropy
`PASSWORD/SECRET/TOKEN/API_KEY/ADMIN_PASSWORD = <20+ chars>` assignments (placeholders excluded).

### What it deliberately allows (known offline test fixtures)

The repo intentionally contains offline demo/unit-test signers that must stay. The `.gitleaks.toml`
allowlist carves these out so the hook isn't noisy: `whsec_demo_…` / `whsec_test_…` demo signers,
`whsec_attacker_guess` (a forge-detection unit-test literal), and the `sk_live_secret` test literal.
Obvious placeholders (`xxx`, `<...>`, `REDACTED`, `PLACEHOLDER`, `changeme`, `${...}`, `example`,
`dummy`) are also allowed.

## Install (any clone / operator)

```sh
sh scripts/install-git-hooks.sh   # symlinks pre-commit + pre-push into .git/hooks
```

This repo uses the **default** `.git/hooks` dir (git-lfs owns the post-* hooks there, and our pre-push
re-invokes `git lfs pre-push`), so `core.hooksPath` is intentionally left unchanged.

## Emergency bypass (discouraged)

`git commit --no-verify` / `git push --no-verify` skips the hook. Use only when you are certain the
match is a false positive **and** you cannot quickly allowlist it — then fix the allowlist afterward.
