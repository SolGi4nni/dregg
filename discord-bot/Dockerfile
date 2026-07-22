# dregg-discord-bot — STAGING runtime image.
#
# This is a RUNTIME-ONLY image: it wraps a pre-built `dregg-discord-bot` binary
# in a slim base. It deliberately does NOT compile Rust — the bot is a member of
# a STANDALONE cargo workspace whose path-deps (dregg-sdk/turn/circuit/...) reach
# back into the (huge) root workspace, and the realistic build is a NATIVE
# linux/amd64 `cargo build`, not a cross-compile. So the binary is built once on a
# capable native-Linux box and COPYed in here (the same "build on a capable
# builder, ship the artifact" shape the dregg-node image uses).
#
# Build the binary (on a native linux/amd64 box with the full breadstuffs
# checkout) WITHOUT linking the Lean kernel archive — the bot signs+submits turns
# to a dregg-node over HTTP and lets the NODE prove, so it needs no in-process
# Lean producer:
#
#   cd discord-bot
#   cargo build --release --features dregg-sdk/no-lean-link
#   docker build -t dregg-discord-bot:staging .
#
# BASE GLIBC: the binary is a glibc (gnu) binary. Pick a base whose glibc is
# >= the build box's glibc. The reference build box (persvati) is Ubuntu with
# glibc 2.42, so the base is `ubuntu:25.10` (glibc 2.42). If you build on an
# older glibc you may drop to a slimmer/older base. TLS is rustls (no openssl);
# SQLite is statically bundled (libsqlite3-sys) — so only ca-certificates is
# needed at runtime.
FROM ubuntu:25.10

RUN apt-get update && apt-get install -y --no-install-recommends \
        ca-certificates \
    && rm -rf /var/lib/apt/lists/*

# The pre-built bot binary. Override BOT_BIN if you build elsewhere.
ARG BOT_BIN=target/release/dregg-discord-bot
COPY ${BOT_BIN} /usr/local/bin/dregg-discord-bot
RUN chmod +x /usr/local/bin/dregg-discord-bot

# The (vestigial) SQL migration seed. The schema actually self-initializes via
# CREATE TABLE IF NOT EXISTS in db.rs::connect(), so no migration step runs at
# boot — this is carried only for parity/inspection.
COPY migrations /opt/dregg-bot/migrations

# Sane container defaults. The SQLite DB lives on a mounted volume at /data;
# `?mode=rwc` makes sqlx create the file on first boot. The HTTP read+admin
# surface binds all interfaces inside the container (reached via Caddy).
ENV DATABASE_URL=sqlite:/data/bot.db?mode=rwc \
    HTTP_HOST=0.0.0.0 \
    HTTP_PORT=8080 \
    RUST_LOG=info

# POST-QUANTUM POSTURE: the games bot signs custodial GAME turns but is NOT part of dregg's
# proven TCB (the node installs the ~195 MB Lean-verified ML-DSA core; the bot does not). So it
# runs the regular (unaudited) fips204/ml-kem crates. dregg-pq's no-silent-fallback gate
# `process::abort()`s any turn-signing without this explicit opt-in — and prints a loud
# "assurance VOID" warning at first use, so the posture is never silent. See
# discord-bot/.cargo/config.toml for the same choice at build/test time.
ENV DREGG_ALLOW_UNAUDITED_PQ=1

WORKDIR /data
EXPOSE 8080

# The bot reads DISCORD_TOKEN / DISCORD_APP_ID / BOT_SECRET / FEDERATION_ID /
# DEVNET_URL / ADMIN_TOKEN / ADMIN_DISCORD_ID from the environment (compose
# injects them from /opt/dreggnet/.env). It exits 1 with a friendly message if a
# required var is missing — so before the token is dropped it simply will not run.
ENTRYPOINT ["/usr/local/bin/dregg-discord-bot"]
