# Devnet configuration (generated)

This directory is **generated at devnet startup** and should not be committed.

Run `./docker/start-devnet.sh` (or manually):

```bash
cargo run -p dregg-node -- genesis --validators 3 --output docker/devnet-config/
```

That writes validator key files, `genesis.json`, and `.devnet/` metadata here. Docker Compose mounts these read-only into each federation node.

To regenerate: stop the stack, remove this directory, and run `start-devnet.sh` again.