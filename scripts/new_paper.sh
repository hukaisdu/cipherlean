#!/usr/bin/env bash
# new_paper.sh — scaffold Formal/<Slug>/ in the lean-formal workspace.
#   usage: new_paper.sh <Slug> [--paper-dir <dir>]
#   <Slug>        UpperCamelCase ASCII (it becomes a Lean module name), e.g. Divisibility26
#   --paper-dir   keep the real files in <dir>/formal/ (synced and versioned with the paper)
#                 and symlink <workspace>/Formal/<Slug> -> <dir>/formal
set -euo pipefail
WS="${LEAN_FORMAL_WS:-$HOME/lean-formal}"
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ASSETS="$HERE/../assets"
SLUG="${1:?usage: new_paper.sh <Slug> [--paper-dir <dir>]}"; shift
PAPER_DIR=""
while [ $# -gt 0 ]; do
  case "$1" in
    --paper-dir) PAPER_DIR="${2:?--paper-dir needs a directory}"; shift 2 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done
[[ "$SLUG" =~ ^[A-Z][A-Za-z0-9]*$ ]] || { echo "Slug must be UpperCamelCase ASCII (Lean module name), got: $SLUG" >&2; exit 2; }
[ -f "$WS/lakefile.toml" ] || { echo "workspace not found at $WS: run $HERE/setup_env.sh --install (or set LEAN_FORMAL_WS)" >&2; exit 2; }
DEST="$WS/Formal/$SLUG"
[ -e "$DEST" ] || [ -L "$DEST" ] && { echo "already exists: $DEST" >&2; exit 1; }
if [ -n "$PAPER_DIR" ]; then
  [ -d "$PAPER_DIR" ] || { echo "no such directory: $PAPER_DIR" >&2; exit 2; }
  REAL="$(cd "$PAPER_DIR" && pwd)/formal"
  mkdir -p "$REAL"
  ln -s "$REAL" "$DEST"
  echo "real files: $REAL  (symlink: $DEST)"
else
  mkdir -p "$DEST"
fi
for pair in "file-template.lean:Main.lean" "README-template.md:README.md" "NOTATION-template.md:NOTATION.md"; do
  src="${pair%%:*}"; dst="${pair##*:}"
  [ -e "$DEST/$dst" ] || sed "s/<Slug>/$SLUG/g" "$ASSETS/$src" > "$DEST/$dst"
done
ls -la "$DEST/"
echo "next: fill README.md (statement, hypotheses, plan) and NOTATION.md; then"
echo "      cd $WS && lake build Formal.$SLUG.Main"
