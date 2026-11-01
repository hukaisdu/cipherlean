#!/usr/bin/env bash
# search_mathlib.sh — find an existing lemma three ways.
#   usage: search_mathlib.sh "<query>" [local|loogle|leansearch|all]
#   local      grep declaration heads in the workspace's Mathlib source (name fragment, regex ok)
#   loogle     https://loogle.lean-lang.org  — by name or by pattern, e.g. "Finset.sum _ (_ + _)",
#              "Function.Bijective _ → Finset.sum _ _ = Finset.sum _ _"  (rate limit ≈ 3 req / 30 s)
#   leansearch https://leansearch.net — natural language, e.g. "sum over a bijection equals sum over codomain"
set -uo pipefail
WS="${CIPHERLEAN_WS:-$HOME/cipherlean}"
Q="${1:?usage: search_mathlib.sh \"<query>\" [local|loogle|leansearch|all]}"
MODE="${2:-all}"
enc() { python3 -c 'import sys,urllib.parse;print(urllib.parse.quote(sys.argv[1]))' "$1"; }

if [[ "$MODE" == local || "$MODE" == all ]]; then
  echo "== local Mathlib: declaration heads matching /$Q/ =="
  ML="$WS/.lake/packages/mathlib/Mathlib"
  if command -v rg >/dev/null; then
    rg -n --no-heading -e "^(theorem|lemma|def|abbrev|instance|structure|class|@\[simp\] theorem|@\[simp\] lemma)\s+.*$Q" "$ML" | head -25
  else
    grep -rn --include='*.lean' -E "^(theorem|lemma|def|abbrev|instance|structure|class)\s+.*$Q" "$ML" | head -25
  fi
fi
if [[ "$MODE" == loogle || "$MODE" == all ]]; then
  echo; echo "== Loogle =="
  curl -s --max-time 25 "https://loogle.lean-lang.org/json?q=$(enc "$Q")" | python3 -c '
import json,sys
try: d=json.load(sys.stdin)
except Exception: print("(no response)"); sys.exit()
if d.get("error"): print("error:", d["error"].strip())
print(d.get("header","").strip())
for h in d.get("hits",[])[:12]: print("- {} : {}   [{}]".format(h["name"], h["type"].strip(), h["module"]))'
fi
if [[ "$MODE" == leansearch || "$MODE" == all ]]; then
  echo; echo "== LeanSearch (natural language) =="
  curl -s --max-time 25 -X POST https://leansearch.net/search -H 'Content-Type: application/json' \
    -d "$(python3 -c 'import json,sys;print(json.dumps({"query":[sys.argv[1]],"num_results":10}))' "$Q")" | python3 -c '
import json,sys
try: d=json.load(sys.stdin)
except Exception: print("(no response)"); sys.exit()
hits = d[0] if d and isinstance(d[0], list) else d
for h in hits[:10]:
    r=h.get("result",h); name=".".join(r.get("name",[])); sig=(r.get("signature") or r.get("type") or "").replace("\n"," ")
    print("- {} : {}".format(name, sig[:220]))'
fi
