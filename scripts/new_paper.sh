#!/usr/bin/env bash
# new_paper.sh — scaffold CipherLean/<Slug>/ in the cipherlean workspace.
#   usage: new_paper.sh <Slug> [--paper-dir <dir>] [--file <Name>]
#   <Slug>        UpperCamelCase ASCII (it becomes a Lean module name), e.g. Divisibility26
#   --paper-dir   keep the real files in <dir>/formal/ (synced and versioned with the paper)
#                 and symlink <workspace>/CipherLean/<Slug> -> <dir>/formal
#   --file <Name> add <Name>.lean from the file template to an existing CipherLean/<Slug>/ (one file per
#                 piece of a split theorem; Main.lean imports them)
set -euo pipefail
WS="${CIPHERLEAN_WS:-$HOME/cipherlean}"
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ASSETS="$HERE/../assets"
case "${1:-}" in -h|--help|"") sed -n '2,8p' "$0"; exit 0 ;; esac
SLUG="$1"; shift
PAPER_DIR=""
FILE=""
while [ $# -gt 0 ]; do
  case "$1" in
    --paper-dir) PAPER_DIR="${2:?--paper-dir needs a directory}"; shift 2 ;;
    --file) FILE="${2:?--file needs a name}"; shift 2 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done
[[ "$SLUG" =~ ^[A-Z][A-Za-z0-9]*$ ]] || { echo "Slug must be UpperCamelCase ASCII (Lean module name), got: $SLUG" >&2; exit 2; }
[ -f "$WS/lakefile.toml" ] || { echo "workspace not found at $WS: run $HERE/setup_env.sh --install (or set CIPHERLEAN_WS)" >&2; exit 2; }
DEST="$WS/CipherLean/$SLUG"
if [ -n "$FILE" ]; then
  [[ "$FILE" =~ ^[A-Z][A-Za-z0-9]*$ ]] || { echo "--file name must be UpperCamelCase ASCII, got: $FILE" >&2; exit 2; }
  [ -d "$DEST" ] || { echo "no such directory: $DEST (scaffold it first)" >&2; exit 1; }
  [ -e "$DEST/$FILE.lean" ] && { echo "already exists: $DEST/$FILE.lean" >&2; exit 1; }
  sed "s/<Slug>/$SLUG/g" "$ASSETS/file-template.lean" > "$DEST/$FILE.lean"
  echo "created $DEST/$FILE.lean (add \`import CipherLean.$SLUG.$FILE\` to Main.lean when the piece is done; the last piece"
  echo "      turns Main.lean into the aggregator: imports of all pieces, the template main replaced by the target restated"
  echo "      from the last piece — a reviewer flags a leftover \`theorem main : True := by sorry\`)"
  exit 0
fi
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
for pair in "file-template.lean:Main.lean" "README-template.md:README.md" "NOTATION-template.md:NOTATION.md" "CHAIN-template.md:CHAIN.md"; do
  src="${pair%%:*}"; dst="${pair##*:}"
  [ -e "$DEST/$dst" ] || sed "s/<Slug>/$SLUG/g" "$ASSETS/$src" > "$DEST/$dst"
done
ls -la "$DEST/"
echo "next: fill README.md (statement, hypotheses) and CHAIN.md (the proof chain and its Roadmap: end, pieces, route and size per piece), draw the graph with chain_graph.py, get the reader's confirmation; then NOTATION.md and"
echo "      cd $WS && lake build CipherLean.$SLUG.Main"
