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
#   remote.sh eval  < snippet.lean              run a Lean snippet there with `lake env lean`
# Variables: CIPHERLEAN_WS (local workspace, default ~/cipherlean), CIPHERLEAN_REMOTE_WS (default ~/cipherlean),
# CIPHERLEAN_REMOTE_SKILL (default ~/.claude/skills/cipherlean). Non-login ssh shells do not have ~/.elan/bin on
# PATH, so every remote command starts with `export PATH="$HOME/.elan/bin:$PATH"`.
set -euo pipefail
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
  eval)  tmp=$(mktemp); cat > "$tmp"; scp -q "$tmp" "$HOST:/tmp/cipherlean_snippet.lean"; rm -f "$tmp"
         $SSH "$PRE; S=\$(date +%s); lake env lean /tmp/cipherlean_snippet.lean 2>&1 | cut -c1-200; echo \"eval took \$(( \$(date +%s) - S ))s\"; rm -f /tmp/cipherlean_snippet.lean" ;;
  *) sed -n 2,16p "$0"; exit 2 ;;
esac
