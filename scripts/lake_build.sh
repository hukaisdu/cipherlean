#!/usr/bin/env bash
# lake_build.sh — `lake build <targets>` in the workspace, serialized by a file lock so that
# several agents sharing ~/cipherlean never build at the same time (macOS has no `flock`).
#   usage: lake_build.sh CipherLean.<Slug>.Main [more targets]
set -euo pipefail
case "${1:-}" in -h|--help|"") sed -n '2,4p' "$0"; exit 0 ;; esac
WS="${CIPHERLEAN_WS:-$HOME/cipherlean}"
export PATH="$HOME/.elan/bin:$PATH"
[ -f "$WS/lakefile.toml" ] || { echo "workspace not found at $WS: run $(dirname "$0")/setup_env.sh --install" >&2; exit 2; }
cd "$WS"
exec python3 - "$@" <<'EOF'
import fcntl, os, subprocess, sys, time
lock = open(os.path.join(".lake", "cipherlean-build.lock"), "w")
t0 = time.time()
fcntl.flock(lock, fcntl.LOCK_EX)
waited = time.time() - t0
if waited > 1:
    print(f"[lake_build.sh] waited {waited:.0f}s for another build to finish", flush=True)
sys.exit(subprocess.call(["lake", "build", *sys.argv[1:]]))
EOF
