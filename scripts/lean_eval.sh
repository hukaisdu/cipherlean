#!/usr/bin/env bash
# lean_eval.sh — run a Lean snippet against the workspace, fast.
#   usage: lean_eval.sh [--light | --full | --imports "Mathlib.A,Mathlib.B"] (file.lean | -)
#   --light (default)  a 17-module preset for cryptanalysis statements: big operators, Fintype,
#                      ZMod, BitVec, FinEnum, dotProduct, bilinear-form orthogonality, ZMod submodules, and the
#                      tactics ring / linarith / norm_num / field_simp / fin_cases / positivity
#                      (loads in ~7 s instead of ~27 s for `import Mathlib`)
#   --full             `import Mathlib` (use when the preset lacks something)
#   --imports LIST     your own comma-separated modules
#   A snippet that already starts with `import` is run unchanged.
#   Examples:  printf '#check @Finset.sum_comm\n' | lean_eval.sh -
#              lean_eval.sh --full scratch.lean
set -uo pipefail
WS="${LEAN_FORMAL_WS:-$HOME/lean-formal}"
export PATH="$HOME/.elan/bin:$PATH"
MODE=light; IMPORTS=""; SRC=""
while [ $# -gt 0 ]; do
  case "$1" in
    --light) MODE=light ;; --full) MODE=full ;;
    --imports) MODE=custom; IMPORTS="${2:?--imports needs a list}"; shift ;;
    -h|--help) sed -n '2,13p' "$0"; exit 0 ;;
    *) SRC="$1" ;;
  esac
  shift
done
[ -n "$SRC" ] || { echo "usage: lean_eval.sh [--light|--full|--imports LIST] (file.lean | -)" >&2; exit 2; }
[ -f "$WS/lakefile.toml" ] || { echo "workspace not found at $WS: run $(dirname "$0")/setup_env.sh --install" >&2; exit 2; }
LIGHT="Mathlib.Algebra.BigOperators.Group.Finset.Basic Mathlib.Algebra.BigOperators.Fin Mathlib.Data.Fintype.BigOperators Mathlib.Data.ZMod.Basic Mathlib.Algebra.CharP.Two Mathlib.Data.BitVec Mathlib.Data.FinEnum Mathlib.Data.Matrix.Mul Mathlib.Logic.Function.Basic Mathlib.LinearAlgebra.BilinearForm.Orthogonal Mathlib.Algebra.Module.ZMod Mathlib.Tactic.FieldSimp Mathlib.Tactic.Ring Mathlib.Tactic.Linarith Mathlib.Tactic.NormNum Mathlib.Tactic.FinCases Mathlib.Tactic.Positivity"
mkdir -p "$WS/.lake/eval"
TMP="$WS/.lake/eval/snippet_$$.lean"
if [ "$SRC" = "-" ]; then BODY="$(cat)"; else BODY="$(cat "$SRC")"; fi
if printf '%s' "$BODY" | grep -qE '^\s*import '; then
  printf '%s\n' "$BODY" > "$TMP"
else
  {
    case "$MODE" in
      light) for m in $LIGHT; do echo "import $m"; done ;;
      full) echo "import Mathlib" ;;
      custom) echo "$IMPORTS" | tr ',' '\n' | sed 's/^ *//; s/ *$//; /^$/d; s/^/import /' ;;
    esac
    echo; printf '%s\n' "$BODY"
  } > "$TMP"
fi
( cd "$WS" && lake env lean "$TMP" ) 2>&1 | sed "s#$TMP#<snippet>#g"
RC=${PIPESTATUS[0]}
rm -f "$TMP"
exit $RC
