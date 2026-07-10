# Deploy the dregg discord bot on hbox — cutover runbook

Built in a SEPARATE worktree (`~/dev/bot-deploy`, branch `bot-deploy`) so hbox's active
`mlkem-encaps-route` checkout is untouched. Binary: `~/dev/bot-deploy-target/release/dregg-discord-bot`.

## 0. Wait for the build (in progress)
    ssh hbox@hbox.local 'tail -n 3 ~/bot-build.log'      # look for `EXIT=0`

## 1. Place the token env on hbox  (EMBER — I won't sling a prod token)
From `./discord-values` (local): DISCORD_APP_ID, DISCORD_TOKEN. Write on hbox:
    ssh hbox@hbox.local 'mkdir -p ~/.config/dregg && cat > ~/.config/dregg/discord-bot.env' <<VALS
    DISCORD_TOKEN=…
    DISCORD_APP_ID=…
    # for live Claude Haiku narration (optional; else the bot narrates scripted, honestly labeled):
    AWS_PROFILE=commonquant-ember
    DREGG_NARRATOR_LEDGER=/home/hbox/.dregg/narrator-ledger.json
    VALS
    ssh hbox@hbox.local 'chmod 600 ~/.config/dregg/discord-bot.env'
(AWS creds also need to reach hbox for Bedrock — `~/.aws/` or instance role. Scripted works without.)

## 2. ⚠ STOP graviton's bot FIRST  (EMBER — I have no ssh to graviton)
Two bots on one token = every command fires twice. Stop graviton's before hbox's starts:
    ssh <graviton> 'sudo systemctl stop dregg-discord-bot'      # or `disable --now`

## 3. Install + start on hbox
    ssh hbox@hbox.local '
      mkdir -p ~/.config/systemd/user
      cp ~/dev/bot-deploy/deploy/hbox/dregg-discord-bot.service ~/.config/systemd/user/
      systemctl --user daemon-reload
      loginctl enable-linger hbox            # so the user unit survives logout
      systemctl --user enable --now dregg-discord-bot
      sleep 5; systemctl --user status dregg-discord-bot --no-pager | head -12
    '
Fastest alternative (no systemd), for a quick presentation run:
    ssh hbox@hbox.local 'cd ~/dev/bot-deploy/discord-bot && set -a && . ~/.config/dregg/discord-bot.env && set +a && nohup ~/dev/bot-deploy-target/release/dregg-discord-bot > ~/bot-run.log 2>&1 & sleep 5; tail ~/bot-run.log'

## 4. Verify in Discord
`/dungeon list` → `/dungeon start` → tap a vote button → `/dungeon close` → `/dungeon verify`.
Author: `/dungeon check` (paste/attach a .dungeon) → `/dungeon forge` → the channel plays it.

## Narrator note
fiction.rs narrates via ollama gemma2 → scripted fallback. hbox has NO ollama, so it narrates SCRIPTED
(honest footer). To get live Claude Haiku 4.5, swap fiction.rs onto `dregg-narrator` (Bedrock, the same
hard $20 ledger) — a follow-up code change + rebuild, not required for the first live deploy.
