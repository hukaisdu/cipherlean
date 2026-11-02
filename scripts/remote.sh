#!/usr/bin/env bash
# remote.sh — run a cipherlean step on another machine that has the workspace installed
# (`git clone` of this skill there + `setup_env.sh --install`), with the paper directory synced from here.
# Builds and checks on a big Linux box are several times faster than on a laptop (Ubuntu 24.04, 128 cores:
# `import CipherLean` 2 s instead of 7 s), while the sources stay on this machine.
#
#   export CIPHERLEAN_REMOTE=user@host          # required; key-based ssh
#   remote.sh sync  <Slug>                      rsync CipherLean/<Slug>/ to the remote workspace
#   remote.sh build <Slug> <Module>             sync, then lake_build.sh CipherLean.<Slug>.<Module> (timed)
#   remote.sh check <Slug> <File.lean> [args]   sync, then check_lean.py (summary, FAIL rows, errors)
#   remote.sh chain <Slug> <File.lean> [...]    sync, then chain_check.py CHAIN.md <File.lean> ... (all pieces at once)
#   remote.sh trim  <Slug> <File.lean>          sync, trim_imports.py --apply there, copy the file back here
#   remote.sh lib   [<File.lean> ...]           copy this machine's library (CipherLean/Lib/ and CipherLean.lean, i.e. the
#                                               skill's assets/lib and assets/workspace/CipherLean.lean through the workspace
#                                               symlinks) into the remote skill clone's assets, run setup_env.sh --update-library
#                                               there (symlinks, rebuild), then check_lean.py on each library file given (step 7,
#                                               promotion). The remote clone is dirty until the change is committed here, pushed,
#                                               and pulled there with `remote.sh pull`.
#   remote.sh pull                              on the remote: discard the copies `lib` left in the skill clone's assets, git pull,
#                                               setup_env.sh --update-library (after a commit and push from here)
#   remote.sh eval  < snippet.lean              run a Lean snippet there with `lake env lean`
# Variables: CIPHERLEAN_WS (local workspace, default ~/cipherlean), CIPHERLEAN_REMOTE_WS (default ~/cipherlean),
# CIPHERLEAN_REMOTE_SKILL (default ~/.claude/skills/cipherlean). Non-login ssh shells do not have ~/.elan/bin on
# PATH, so every remote command starts with `export PATH="$HOME/.elan/bin:$PATH"`.
set -euo pipefail
case "${1:-}" in -h|--help|"") sed -n 2,18p "$0"; exit 0 ;; esac
HOST=${CIPHERLEAN_REMOTE:-}
[ -n "$HOST" ] || { echo "remote.sh: set CIPHERLEAN_REMOTE=user@host" >&2; exit 2; }
WS=${CIPHERLEAN_WS:-$HOME/cipherlean}
RWS=${CIPHERLEAN_REMOTE_WS:-'$HOME/cipherlean'}
RSKILL=${CIPHERLEAN_REMOTE_SKILL:-'$HOME/.claude/skills/cipherlean'}
SSH="ssh -o BatchMode=yes -o ConnectTimeout=10 -o ServerAliveInterval=30 $HOST"
PRE="export PATH=\"\$HOME/.elan/bin:\$PATH\"; cd $RWS"
cmd=${1:-}; shift || true
sync_slug() {
  rsync -az --exclude '.lake' --exclude '*.aux' --exclude '*.log' --exclude '*.fls' --exclude '*.fdb_latexmk' \
    --exclude '*.synctex.gz' "$WS/CipherLean/$1/" "$HOST:$RWS/CipherLean/$1/"
}
case "$cmd" in
  sync)  sync_slug "$1"; echo "synced CipherLean/$1 to $HOST" ;;
  build) sync_slug "$1"
         $SSH "$PRE; S=\$(date +%s); bash $RSKILL/scripts/lake_build.sh CipherLean.$1.$2 2>&1 | grep -v -E 'exceeds the 100|linter.style|^Note:|^\$' | tail -40; echo \"build elapsed=\$(( \$(date +%s) - S ))s\"" ;;
  check) slug=$1; file=$2; shift 2; sync_slug "$slug"
         $SSH "$PRE; S=\$(date +%s); python3 $RSKILL/scripts/check_lean.py CipherLean/$slug/$file $* > /tmp/check_$slug.log 2>&1; rc=\$?; echo \"check exit=\$rc elapsed=\$(( \$(date +%s) - S ))s\"; grep -E '^build:|VERDICT' /tmp/check_$slug.log; echo \"PASS=\$(grep -c '| PASS |' /tmp/check_$slug.log) NATIVE=\$(grep -c '| NATIVE |' /tmp/check_$slug.log) FAIL=\$(grep -c '| FAIL |' /tmp/check_$slug.log)\"; grep '| FAIL |' /tmp/check_$slug.log | head -20; grep -E '^(error|warning)' /tmp/check_$slug.log | grep -v 'exceeds the 100' | head -20" ;;
  chain) slug=$1; shift; sync_slug "$slug"; files=""; for f in "$@"; do files="$files CipherLean/$slug/$f"; done
         $SSH "$PRE; python3 $RSKILL/scripts/chain_check.py CipherLean/$slug/CHAIN.md $files 2>&1 | grep -E 'UNKNOWN|MISSING|VERDICT|extra|^- '" ;;
  trim)  sync_slug "$1"
         $SSH "$PRE; python3 $RSKILL/scripts/trim_imports.py CipherLean/$1/$2 --apply 2>&1 | tail -8"
         scp -q "$HOST:$RWS/CipherLean/$1/$2" "$WS/CipherLean/$1/$2" && echo "trimmed file copied back to $WS/CipherLean/$1/$2" ;;
  lib)   # -L: read through this workspace's symlinks; the destination is the remote skill clone's assets (never the remote
         # workspace's symlinks, which rsync would replace by files)
         rsync -azL --exclude '.lake' "$WS/CipherLean/Lib/" "$HOST:$RSKILL/assets/lib/"
         rsync -azL "$WS/CipherLean.lean" "$HOST:$RSKILL/assets/workspace/CipherLean.lean"
         $SSH "$PRE; S=\$(date +%s); bash $RSKILL/scripts/setup_env.sh --update-library 2>&1 | grep -E '^  (OK|note|FAIL|changed)|SETUP FAILED' | tail -6; echo \"library update elapsed=\$(( \$(date +%s) - S ))s\"; git -C $RSKILL status --short | head -12"
         for f in "$@"; do
           $SSH "$PRE; python3 $RSKILL/scripts/check_lean.py CipherLean/Lib/$f --no-build > /tmp/check_lib.log 2>&1; rc=\$?; echo \"check Lib/$f exit=\$rc \$(grep -E 'VERDICT' /tmp/check_lib.log | head -1) PASS=\$(grep -c '| PASS |' /tmp/check_lib.log) NATIVE=\$(grep -c '| NATIVE |' /tmp/check_lib.log) FAIL=\$(grep -c '| FAIL |' /tmp/check_lib.log)\"; grep '| FAIL |' /tmp/check_lib.log | head -10"
         done ;;
  pull)  $SSH "$PRE; cd $RSKILL && git checkout -- assets/lib assets/workspace/CipherLean.lean && git pull && git log --oneline -1 && bash scripts/setup_env.sh --update-library 2>&1 | grep -E '^  (OK|note|FAIL)' | tail -4" ;;
  eval)  tmp=$(mktemp); cat > "$tmp"; scp -q "$tmp" "$HOST:/tmp/cipherlean_snippet.lean"; rm -f "$tmp"
         $SSH "$PRE; S=\$(date +%s); lake env lean /tmp/cipherlean_snippet.lean 2>&1 | cut -c1-200; echo \"eval took \$(( \$(date +%s) - S ))s\"; rm -f /tmp/cipherlean_snippet.lean" ;;
  *) sed -n 2,18p "$0"; exit 2 ;;
esac
