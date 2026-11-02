#!/usr/bin/env bash
# sync_library.sh — copy the shared library from the workspace back into this skill's assets/lib
# (the source of truth that ships with the skill), then show what changed. The opposite direction
# (skill -> workspace) is `setup_env.sh --update-library`.
#   usage: sync_library.sh [--workspace DIR]     (default $CIPHERLEAN_WS, else ~/cipherlean)
set -eu
HERE="$(cd "$(dirname "$0")" && pwd)"; SKILL="$(cd "$HERE/.." && pwd)"
WS="${CIPHERLEAN_WS:-$HOME/cipherlean}"
case "${1:-}" in -h|--help) sed -n '2,5p' "$0"; exit 0 ;; --workspace) WS="$2" ;; esac
LIB="$WS/CipherLean/Lib"
[ -d "$LIB" ] || { echo "no library at $LIB (set CIPHERLEAN_WS or --workspace)" >&2; exit 2; }
mkdir -p "$SKILL/assets/lib"
rsync -a --delete --exclude 'PROMOTE.md' "$LIB/" "$SKILL/assets/lib/"
cp "$WS/CipherLean.lean" "$SKILL/assets/workspace/CipherLean.lean"
echo "assets/lib and assets/workspace/CipherLean.lean synced from $WS"
( cd "$SKILL" && git status --short -- assets/lib assets/workspace/CipherLean.lean | sed 's/^/  /' )
echo "next: run check_lean.py on the touched modules in the workspace, then commit and push (or open a PR)."
