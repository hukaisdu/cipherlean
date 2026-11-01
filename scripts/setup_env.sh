#!/usr/bin/env bash
# setup_env.sh — check, and on request create, everything the lean-formalize skill needs.
#
#   setup_env.sh --check            report OK / MISSING per item, change nothing; exit 1 if anything is missing
#   setup_env.sh --install          install / download / configure whatever is missing (idempotent,
#                                   never overwrites an existing file), then build Formal/Smoke.lean
#   options:  --workspace DIR       default $LEAN_FORMAL_WS, else ~/lean-formal
#             --smoke               with --check: also build Formal/Smoke.lean (~10-40 s)
#             --examples            with --install: also compile Formal/Examples (a few minutes)
#             --build-from-source   if the prebuilt Mathlib cannot be downloaded, compile it (hours)
#             --full-clone          let Lake clone the full git history instead of the shallow pre-clone
#             --update-library      copy assets/crypto over Formal/Crypto in the workspace and rebuild it
#             --mcp                 also register the lean-lsp-mcp server with Claude Code (needs uv and the
#                                   claude CLI; keeps Mathlib loaded between proof attempts; optional)
#
# What --install may do, in this order: install elan into ~/.elan (official installer, ~5 MB);
# install the Lean toolchain pinned in assets/workspace/lean-toolchain (~300 MB); create the
# workspace from assets/workspace; shallow-clone Mathlib and its dependencies at the pinned commits
# (git --depth 1, a few hundred MB instead of the full history); download the
# prebuilt Mathlib with `lake exe cache get` (~2 GB download, ~6 GB on disk); copy the examples;
# build Formal/Smoke.lean and run check_lean.py on it. Needs curl, git, python3, >= 10 GB free
# disk and network access. macOS and Linux (Windows: use WSL).
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SKILL="$(cd "$HERE/.." && pwd)"
MODE=check; SMOKE=0; EXAMPLES=0; FROM_SOURCE=0; FULL_CLONE=0; MCP=0; UPDATE_LIB=0
WS="${LEAN_FORMAL_WS:-$HOME/lean-formal}"
while [ $# -gt 0 ]; do
  case "$1" in
    --check) MODE=check ;;
    --install) MODE=install ;;
    --smoke) SMOKE=1 ;;
    --examples) EXAMPLES=1 ;;
    --update-library) UPDATE_LIB=1 ;;
    --build-from-source) FROM_SOURCE=1 ;;
    --full-clone) FULL_CLONE=1 ;;
    --mcp) MCP=1 ;;
    --workspace) WS="${2:?--workspace needs a directory}"; shift ;;
    -h|--help) sed -n '2,18p' "$0"; exit 0 ;;
    *) echo "unknown option: $1 (see --help)" >&2; exit 2 ;;
  esac
  shift
done
export PATH="$HOME/.elan/bin:$PATH"
TOOLCHAIN="$(cat "$SKILL/assets/workspace/lean-toolchain")"
VERSION="${TOOLCHAIN#leanprover/lean4:}"
MISSING=0
ok()   { printf '  OK       %s\n' "$*"; }
note() { printf '  note     %s\n' "$*"; }
miss() { printf '  MISSING  %s\n' "$*"; MISSING=1; }
fail() { printf '  FAIL     %s\n' "$*" >&2; echo "SETUP FAILED (see above)"; exit 1; }
step() { printf '\n== %s\n' "$*"; }

echo "lean-formalize environment ($MODE): workspace $WS, toolchain $TOOLCHAIN"

step "platform and tools"
case "$(uname -s)" in
  Darwin|Linux) ok "$(uname -s) $(uname -m)" ;;
  *) miss "unsupported OS $(uname -s): use macOS, Linux, or WSL on Windows" ;;
esac
for t in curl git python3; do
  if command -v "$t" >/dev/null 2>&1; then ok "$t: $(command -v "$t")"; else miss "$t not found: install it with your package manager"; fi
done
if command -v rg >/dev/null 2>&1; then ok "rg (ripgrep, optional)"; else note "rg not found; search_mathlib.sh falls back to grep"; fi
PARENT="$WS"; while [ ! -d "$PARENT" ]; do PARENT="$(dirname "$PARENT")"; done
FREE_KB="$(df -Pk "$PARENT" 2>/dev/null | awk 'NR==2{print $4}')"
if [ -n "${FREE_KB:-}" ]; then
  if [ "$FREE_KB" -ge 10485760 ]; then ok "disk: $((FREE_KB/1048576)) GB free at $PARENT"; else miss "disk: only $((FREE_KB/1048576)) GB free at $PARENT, the workspace needs about 8 GB"; fi
fi

step "elan (Lean version manager)"
if command -v elan >/dev/null 2>&1; then
  ok "elan $(elan --version 2>/dev/null | head -1)"
elif [ "$MODE" = install ]; then
  echo "  installing elan into ~/.elan with the official installer (no default toolchain)"
  curl -sSfL https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none || fail "elan installation failed"
  export PATH="$HOME/.elan/bin:$PATH"
  command -v elan >/dev/null 2>&1 && ok "elan installed (open a new shell, or add ~/.elan/bin to PATH)" || fail "elan is not on PATH after installation"
else
  miss "elan not installed (https://lean-lang.org/install/); --install runs the official installer"
fi

step "Lean toolchain $TOOLCHAIN"
if command -v elan >/dev/null 2>&1 && elan toolchain list 2>/dev/null | grep -q "$VERSION"; then
  ok "installed"
elif [ "$MODE" = install ] && command -v elan >/dev/null 2>&1; then
  echo "  downloading $TOOLCHAIN (~300 MB)"
  elan toolchain install "$TOOLCHAIN" || fail "toolchain download failed"
  ok "installed"
else
  miss "toolchain $TOOLCHAIN not installed; --install runs: elan toolchain install $TOOLCHAIN"
fi

step "workspace $WS"
NEED=0
for f in lakefile.toml lean-toolchain lake-manifest.json Formal.lean Formal/Smoke.lean; do [ -f "$WS/$f" ] || NEED=1; done
if [ "$NEED" = 0 ]; then
  ok "lakefile, manifest, Formal/ present"
  [ "$(cat "$WS/lean-toolchain")" = "$TOOLCHAIN" ] || note "workspace pins $(cat "$WS/lean-toolchain"); the skill was tested with $TOOLCHAIN"
elif [ "$MODE" = install ]; then
  mkdir -p "$WS/Formal"
  for f in lakefile.toml lean-toolchain lake-manifest.json Formal.lean .gitignore Formal/Smoke.lean; do
    [ -f "$WS/$f" ] || cp "$SKILL/assets/workspace/$f" "$WS/$f"
  done
  ok "created from assets/workspace (existing files kept)"
else
  miss "workspace files missing; --install creates them from assets/workspace"
fi


# Shallow-clone every package of lake-manifest.json at its pinned commit (git --depth 1), so that
# Lake finds the directories in place and does not fetch full histories. A package whose shallow
# fetch fails is removed again and left to Lake's own (full) clone.
preclone() {
  python3 - "$1" <<'PY'
import json, pathlib, shutil, subprocess, sys, time
ws = pathlib.Path(sys.argv[1]); man = json.load(open(ws / "lake-manifest.json"))
pk = ws / ".lake" / "packages"; pk.mkdir(parents=True, exist_ok=True)
def git(d, *a): return subprocess.run(["git", "-C", str(d), *a], capture_output=True, text=True)
for p in man["packages"]:
    d = pk / p["name"]
    if d.exists(): continue
    t0 = time.time(); d.mkdir()
    ok = (git(d, "init", "-q").returncode == 0 and git(d, "remote", "add", "origin", p["url"]).returncode == 0
          and git(d, "fetch", "-q", "--depth", "1", "origin", p["rev"]).returncode == 0
          and git(d, "checkout", "-q", "--detach", "FETCH_HEAD").returncode == 0
          and git(d, "rev-parse", "HEAD").stdout.strip() == p["rev"])
    if ok:
        print(f"  shallow clone {p['name']:18} {time.time() - t0:4.0f} s", flush=True)
    else:
        shutil.rmtree(d, ignore_errors=True)
        print(f"  shallow clone {p['name']:18} failed; Lake will clone it in full", flush=True)
PY
}

step "Mathlib (prebuilt)"
OLEAN="$WS/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean"
if [ -f "$OLEAN" ]; then
  ok "Mathlib.olean present under .lake/packages/mathlib"
elif [ "$MODE" = install ] && [ -f "$WS/lakefile.toml" ] && command -v lake >/dev/null 2>&1; then
  echo "  cloning Mathlib and its dependencies (shallow), then downloading the prebuilt oleans (lake exe cache get):"
  echo "  a few hundred MB of git data and about 2 GB of cache to download, 6 GB on disk, 10-30 min depending on the network"
  [ "$FULL_CLONE" = 1 ] || preclone "$WS"
  if ! ( cd "$WS" && lake exe cache get ); then
    if [ "$FROM_SOURCE" = 1 ]; then
      echo "  cache download failed; compiling Mathlib from source (this takes hours)"
      ( cd "$WS" && lake build Mathlib ) || fail "lake build Mathlib failed"
    else
      fail "lake exe cache get failed (network, proxy, or GitHub access?). Rerun --install, or add --build-from-source to compile Mathlib (hours)."
    fi
  fi
  [ -f "$OLEAN" ] && ok "Mathlib downloaded" || fail "cache get finished but $OLEAN is missing"
else
  miss "prebuilt Mathlib not present; --install runs 'lake exe cache get' (~6 GB on disk)"
fi

step "examples"
EX="$WS/Formal/Examples"
if [ -f "$EX/Halfspace.lean" ]; then
  ok "Formal/Examples present"
elif [ "$MODE" = install ]; then
  mkdir -p "$EX" && cp -R "$SKILL/assets/examples/." "$EX/"
  ok "copied assets/examples to Formal/Examples"
else
  miss "Formal/Examples missing; --install copies them"
fi

step "shared library"
LIB="$WS/Formal/Crypto"
if [ "$UPDATE_LIB" = 1 ] && [ -d "$WS" ] && command -v lake >/dev/null 2>&1; then
  mkdir -p "$LIB" && cp -R "$SKILL/assets/crypto/." "$LIB/" && cp "$LIB/Crypto.lean" "$WS/Formal/Crypto.lean" && rm -f "$LIB/Crypto.lean"
  if ( cd "$WS" && lake build Formal.Crypto ) >"$WS/.lake/setup-library.log" 2>&1; then
    ok "Formal/Crypto updated from assets/crypto and rebuilt"
  else
    tail -20 "$WS/.lake/setup-library.log"; fail "Formal.Crypto failed to compile after the update (log: $WS/.lake/setup-library.log)"
  fi
elif [ -f "$LIB/F2/Vec.lean" ] && [ -f "$WS/Formal/Crypto.lean" ]; then
  ok "Formal/Crypto present"
elif [ "$MODE" = install ]; then
  mkdir -p "$LIB" && cp -R "$SKILL/assets/crypto/." "$LIB/" && cp "$LIB/Crypto.lean" "$WS/Formal/Crypto.lean" && rm -f "$LIB/Crypto.lean"
  ok "copied assets/crypto to Formal/Crypto"
else
  miss "Formal/Crypto missing; --install copies and compiles it"
fi

step "smoke test"
if [ -f "$OLEAN" ] && [ -f "$WS/Formal/Smoke.lean" ] && command -v lake >/dev/null 2>&1 && { [ "$MODE" = install ] || [ "$SMOKE" = 1 ]; }; then
  LOG="$WS/.lake/setup-smoke.log"
  if ( cd "$WS" && lake build Formal.Smoke ) >"$LOG" 2>&1; then
    ok "lake build Formal.Smoke ($(grep -o 'Built Formal.Smoke ([^)]*)' "$LOG" | head -1 || echo cached))"
  else
    tail -20 "$LOG"; fail "Formal.Smoke does not build (log: $LOG)"
  fi
  if [ "$MODE" = install ]; then
    LOG2="$WS/.lake/setup-check.log"
    if python3 "$HERE/check_lean.py" --ws "$WS" "$WS/Formal/Smoke.lean" >"$LOG2" 2>&1; then
      ok "check_lean.py Formal/Smoke.lean: $(grep VERDICT "$LOG2")"
    else
      tail -20 "$LOG2"; fail "check_lean.py failed on Formal/Smoke.lean (log: $LOG2)"
    fi
    echo "  compiling the shared library Formal.Crypto (a few minutes)"
    ( cd "$WS" && lake build Formal.Crypto ) >"$WS/.lake/setup-library.log" 2>&1 \
      && ok "Formal.Crypto compiled ($(grep -c 'Built Formal.Crypto' "$WS/.lake/setup-library.log") modules)" \
      || { tail -20 "$WS/.lake/setup-library.log"; fail "Formal.Crypto failed to compile (log: $WS/.lake/setup-library.log)"; }
    if [ "$EXAMPLES" = 1 ]; then
      echo "  compiling the examples (a few minutes)"
      ( cd "$WS" && lake build Formal.Examples.Feistel Formal.Examples.Halfspace Formal.Examples.SboxDDT Formal.Examples.DdtInverse.Main ) >"$WS/.lake/setup-examples.log" 2>&1 \
        && ok "examples compiled" || { tail -20 "$WS/.lake/setup-examples.log"; fail "an example failed to compile"; }
    fi
  fi
else
  [ "$MODE" = check ] && note "smoke build not run (add --smoke)"
fi

if [ "$MCP" = 1 ]; then
  step "lean-lsp-mcp (optional: keeps Mathlib loaded between proof attempts)"
  if ! command -v uv >/dev/null 2>&1; then
    miss "uv not found (https://docs.astral.sh/uv/): curl -LsSf https://astral.sh/uv/install.sh | sh"
  elif ! command -v claude >/dev/null 2>&1; then
    miss "claude CLI not found; register by hand: claude mcp add lean-lsp -s user -e LEAN_PROJECT_PATH=$WS -- uvx lean-lsp-mcp"
  elif claude mcp list 2>/dev/null | grep -q "lean-lsp"; then
    ok "already registered (claude mcp list)"
  elif [ "$MODE" = install ]; then
    if claude mcp add lean-lsp -s user -e "LEAN_PROJECT_PATH=$WS" -- uvx lean-lsp-mcp; then
      ok "registered; restart Claude Code to load it"
    else
      miss "claude mcp add failed"
    fi
  else
    miss "not registered; --install --mcp registers it"
  fi
fi

echo
if [ "$MISSING" = 0 ]; then
  echo "ENVIRONMENT OK: workspace $WS, toolchain $TOOLCHAIN"
  exit 0
else
  echo "ENVIRONMENT INCOMPLETE: see the MISSING lines; rerun with --install"
  exit 1
fi
