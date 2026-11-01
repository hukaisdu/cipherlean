#!/usr/bin/env python3
"""build_profile.py — where did the build time go, and where are the computational proofs?

  build_profile.py <lake-build.log> [--top N]
      parses the `✔ [k/n] Built Module (12.3s)` lines Lake prints and lists the slowest modules
      with their share of the total (the top entry is where the next hour goes).
  build_profile.py --sites <dir-or-file> [--top N]
      counts `native_decide`, `decide +kernel`, `bv_decide` and plain `decide` call sites per
      .lean file (comment lines excluded), so the computational proofs are known before the
      first build (references/verify-existing.md, section 2).
Both at once are fine. Exit 0 always; this is a report.
"""
import argparse, pathlib, re, sys

BUILT = re.compile(r"Built\s+(\S+)\s+\((\d+(?:\.\d+)?)(ms|s|m)\)")
SITES = {"native_decide": re.compile(r"\bnative_decide\b"),
         "decide +kernel": re.compile(r"\bdecide\s*\+kernel\b"),
         "bv_decide": re.compile(r"\bbv_decide\b"),
         "decide": re.compile(r"(?<![\w+])decide\b(?!\s*\+kernel)")}


def profile(log, top):
    times = {}
    for line in pathlib.Path(log).read_text(encoding="utf-8", errors="replace").splitlines():
        m = BUILT.search(line)
        if not m:
            continue
        v, unit = float(m.group(2)), m.group(3)
        secs = v / 1000 if unit == "ms" else v * 60 if unit == "m" else v
        times[m.group(1)] = times.get(m.group(1), 0) + secs
    if not times:
        print("no `Built X (..s)` lines found; is this a lake build log?"); return
    total = sum(times.values())
    print(f"# Build profile — {log}\n\n{len(times)} modules, {total:.0f} s of module time\n")
    print("| module | seconds | share |\n|---|---:|---:|")
    for mod, s in sorted(times.items(), key=lambda kv: -kv[1])[:top]:
        print(f"| `{mod}` | {s:.1f} | {100 * s / total:.1f}% |")


def sites(path, top):
    p = pathlib.Path(path)
    files = sorted(p.rglob("*.lean")) if p.is_dir() else [p]
    files = [f for f in files if ".lake" not in f.parts]
    rows, totals = [], {k: 0 for k in SITES}
    for f in files:
        counts = {k: 0 for k in SITES}
        for line in f.read_text(encoding="utf-8", errors="replace").splitlines():
            code = line.split("--", 1)[0]
            for k, rx in SITES.items():
                counts[k] += len(rx.findall(code))
        if any(counts.values()):
            rows.append((f, counts))
            for k in SITES:
                totals[k] += counts[k]
    print(f"\n# Computational proof sites — {p}\n")
    print("| file | native_decide | decide +kernel | bv_decide | decide |\n|---|---:|---:|---:|---:|")
    rows.sort(key=lambda r: (-r[1]["native_decide"], -r[1]["decide +kernel"], -r[1]["bv_decide"]))
    for f, c in rows[:top]:
        rel = f.relative_to(p) if p.is_dir() else f.name
        print(f"| `{rel}` | {c['native_decide']} | {c['decide +kernel']} | {c['bv_decide']} | {c['decide']} |")
    print(f"| **total ({len(rows)} files)** | **{totals['native_decide']}** | **{totals['decide +kernel']}** | **{totals['bv_decide']}** | **{totals['decide']}** |")
    if totals["native_decide"]:
        print("\nEvery `native_decide` adds a compiler axiom; build the heaviest of these files alone first (verify-existing.md §2).")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("log", nargs="?")
    ap.add_argument("--sites")
    ap.add_argument("--top", type=int, default=15)
    a = ap.parse_args()
    if not a.log and not a.sites:
        ap.error("give a lake build log, --sites DIR, or both")
    if a.log:
        profile(a.log, a.top)
    if a.sites:
        sites(a.sites, a.top)


if __name__ == "__main__":
    main()
