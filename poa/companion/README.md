# Public Path of Angels companion routes

This directory is the source tree for the public, read-only
`companion.pathofangels.network` origin. It is intentionally separate from both
the password-curtained beta and the mutable node API.

The production route set is currently empty: the two real YouTube episode IDs
are not present in this repository, so this tree does not guess them. Test-only
placeholder IDs live in `extension/test/poa-companion-v3.test.mjs`.

After the author supplies an exact context, create a strict
`poa-companion/v3` draft and run the curator ceremony. A YouTube output goes to
`public/v1/youtube/<exact-11-character-video-id>.json`; an explicitly authored X
route goes to `public/v1/x/<exact-post-snowflake>.json`. Unknown files return
404 and the edge accepts only GET/HEAD.

```sh
cargo run --manifest-path poa-curator/Cargo.toml -- sign-companion \
  --secret /secure/poa-development-curator.key \
  --pin poa/config/curator-key.json \
  --manifest poa/artifacts/poag1/manifest.json \
  --deployment poa/deployments/epoch-1/poa-devnet.json \
  --content-signature poa/artifacts/poag1/manifest.sig.json \
  --content-epoch 1 --content-counter 4 \
  --draft /secure/review/episode-1-companion-v3.json \
  --output poa/companion/public/v1/youtube/REAL_VIDEO_ID.json

cargo run --manifest-path poa-curator/Cargo.toml -- verify-companion \
  --pin poa/config/curator-key.json \
  --manifest poa/artifacts/poag1/manifest.json \
  --deployment poa/deployments/epoch-1/poa-devnet.json \
  --content-signature poa/artifacts/poag1/manifest.sig.json \
  --content-epoch 1 --content-counter 4 \
  --input poa/companion/public/v1/youtube/REAL_VIDEO_ID.json
```

The signer refuses an unverified content signature, another deployment, stale
or overlong lifetime, foreign origin/action, unpinned asset, wrong curator key,
or an output path that already exists. It never writes or prints the secret.
Route revocation is a higher `sequence` signed for the same exact context with
the game/actions omitted; removal at the edge alone is availability loss, not a
signed revocation for clients that still hold an unexpired response.

Deployment copies only `public/` to `/var/www/pathofangels-companion`. Never
copy drafts, keys, the deployment package, or this README into that root.
