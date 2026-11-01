#!/usr/bin/env bash
# sandbox_project.sh — copy an existing Lean project to a scratch directory for verification:
# the sources are copied, `.lake` becomes a symlink to a scratch build tree, and the workspace's
# already-built Mathlib packages are reused when the project's pin matches (otherwise it stops and
# says what differs). Never builds inside a synced folder (~/sync) or writes to ~/.elan.
#   usage: sandbox_project.sh <project-dir> [<scratch-dir>]     (default scratch: /tmp/cipherlean-sandbox/<name>)
set -eu
SRC="$(cd "$1" && pwd)"; NAME="$(basename "$SRC")"
DEST="${2:-/tmp/cipherlean-sandbox/$NAME}"
WS="${CIPHERLEAN_WS:-$HOME/cipherlean}"
[ -f "$SRC/lean-toolchain" ] || { echo "no lean-toolchain in $SRC" >&2; exit 2; }
PIN="$(tr -d ' \n' < "$SRC/lean-toolchain")"; WSPIN="$(tr -d ' \n' < "$WS/lean-toolchain")"
MREV="$(python3 -c "import json,sys; d=json.load(open(sys.argv[1])); print(next((p['rev'] for p in d['packages'] if p['name']=='mathlib'), ''))" "$SRC/lake-manifest.json" 2>/dev/null || true)"
WSREV="$(python3 -c "import json,sys; d=json.load(open(sys.argv[1])); print(next((p['rev'] for p in d['packages'] if p['name']=='mathlib'), ''))" "$WS/lake-manifest.json" 2>/dev/null || true)"
echo "project pin : $PIN   mathlib $MREV"
echo "workspace   : $WSPIN   mathlib $WSREV"
if ! elan toolchain list 2>/dev/null | grep -q "${PIN#leanprover/lean4:}"; then
  echo "toolchain $PIN is not installed (elan toolchain list); install it, or verify on $WSPIN and say so in the report" >&2
fi
mkdir -p "$DEST/project" "$DEST/lake"
rsync -a --exclude '.lake' --exclude '.git' "$SRC/" "$DEST/project/"
ln -sfn "$DEST/lake" "$DEST/project/.lake"
if [ "$MREV" = "$WSREV" ] && [ "$PIN" = "$WSPIN" ] && [ -d "$WS/.lake/packages" ]; then
  mkdir -p "$DEST/lake/packages"
  for p in "$WS"/.lake/packages/*; do ln -sfn "$p" "$DEST/lake/packages/$(basename "$p")"; done
  echo "pins match: reusing the workspace's built packages (symlinks under $DEST/lake/packages)"
else
  echo "pins differ: no packages reused; either install the project's pin and run 'lake exe cache get' in $DEST/project, or change the pin deliberately and record it" >&2
fi
echo "sandbox: $DEST/project   (sources copied, .lake -> $DEST/lake)"
echo "next: scripts/build_profile.py --sites $DEST/project ; build the heaviest module alone with a time budget"
