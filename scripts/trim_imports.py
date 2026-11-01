#!/usr/bin/env python3
"""trim_imports.py — replace `import Mathlib` by the minimal imports a finished file needs,
verified by compiling the result.

Why: every Lean process that starts with `import Mathlib` maps about 8300 .olean files (27 s on a
laptop even when cached); the modules a finished file really needs load in 3-7 s. So every later
`lake build`, every `check_lean.py` run and every reader of the file gets faster. Do it once the
proofs are done; keep `import Mathlib` while developing.

How: appends `#min_imports` (Mathlib.Tactic.MinImports) to a scratch copy, reads the modules it
suggests, adds the umbrella modules of the tactics the file uses (the command sees the lemmas a
tactic produced, not the tactic's own implementation), compiles the trimmed copy with
`lake env lean`; on failure adds `Mathlib.Tactic.Common`, then `Mathlib.Tactic`; if nothing
compiles the file is left unchanged. Only the `import Mathlib` line is replaced; other imports
(sibling modules, Aesop, ...) are kept. Writes the file only with --apply.

usage: trim_imports.py <file.lean> [--apply] [--ws DIR]
"""
import argparse, os, pathlib, re, shutil, subprocess, sys, tempfile, time

TACTIC_UMBRELLAS = {
    r"\blinarith\b|\bnlinarith\b": "Mathlib.Tactic.Linarith",
    r"\bring\b|\bring_nf\b|\bring1\b": "Mathlib.Tactic.Ring",
    r"\bnorm_num\b": "Mathlib.Tactic.NormNum",
    r"\bfield_simp\b": "Mathlib.Tactic.FieldSimp",
    r"\bfin_cases\b": "Mathlib.Tactic.FinCases",
    r"\bpositivity\b": "Mathlib.Tactic.Positivity",
    r"\bsplit_ifs\b": "Mathlib.Tactic.SplitIfs",
    r"\bby_contra\b": "Mathlib.Tactic.ByContra",
    r"\buse\b": "Mathlib.Tactic.Use",
    r"\btauto\b": "Mathlib.Tactic.Tauto",
    r"\bgcongr\b": "Mathlib.Tactic.GCongr",
    r"\binterval_cases\b": "Mathlib.Tactic.IntervalCases",
    r"\bzify\b": "Mathlib.Tactic.Zify",
    r"\bqify\b": "Mathlib.Tactic.Qify",
    r"\bchoose\b": "Mathlib.Tactic.Choose",
    r"\bpush\b": "Mathlib.Tactic.Push",
    r"\baesop\b": "Aesop",
    r"\bdecide \+kernel\b|\bbv_decide\b|\bomega\b|\bdecide\b|\bsimp\b|\bexact\?": None,  # core Lean
}
FALLBACKS = ["Mathlib.Tactic.Common", "Mathlib.Tactic"]


def die(msg):
    print(f"trim_imports: {msg}", file=sys.stderr); sys.exit(2)


def run_lean(ws, path, timeout=3600):
    env = dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + os.pathsep + os.environ.get("PATH", ""))
    p = subprocess.run(["lake", "env", "lean", str(path)], cwd=ws, capture_output=True, text=True, timeout=timeout, env=env)
    return p.returncode, (p.stdout or "") + (p.stderr or "")


def module_exists(ws, mod):
    parts = mod.split(".")
    if parts[0] == "Mathlib":
        return (ws / ".lake/packages/mathlib" / pathlib.Path(*parts)).with_suffix(".lean").exists()
    return True  # other packages: trust the name


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("file"); ap.add_argument("--apply", action="store_true"); ap.add_argument("--ws")
    a = ap.parse_args()
    ws = pathlib.Path(a.ws or os.environ.get("CIPHERLEAN_WS") or os.path.expanduser("~/cipherlean")).resolve()
    if not (ws / "lakefile.toml").exists():
        die(f"no lakefile in {ws}: run scripts/setup_env.sh --install (or set --ws / CIPHERLEAN_WS)")
    f = pathlib.Path(a.file).resolve(); src = f.read_text(encoding="utf-8")
    lines = src.splitlines()
    idx = [i for i, l in enumerate(lines) if l.strip() == "import Mathlib"]
    if not idx:
        print("nothing to do: the file does not `import Mathlib`"); return
    scratch = pathlib.Path(tempfile.mkdtemp(prefix="trim_", dir=ws / ".lake"))
    try:
        # 1. ask Mathlib for the minimal imports
        probe = scratch / "probe.lean"
        probe.write_text(src + "\n\n#min_imports\n", encoding="utf-8")
        t0 = time.time(); rc, out = run_lean(ws, probe)
        if rc != 0:
            print(out[-3000:]); die("the file does not compile as it is; fix it before trimming")
        suggested = sorted({m.group(2) for m in re.finditer(r"^(public )?import (\S+)", out, re.M)})
        print(f"#min_imports suggests {len(suggested)} modules ({time.time() - t0:.0f} s): " + ", ".join(suggested))
        # 2. tactic umbrellas
        extra = []
        for pat, mod in TACTIC_UMBRELLAS.items():
            if mod and re.search(pat, src) and module_exists(ws, mod) and mod not in suggested:
                extra.append(mod)
        if extra:
            print("tactics used, adding: " + ", ".join(extra))
        base = [m for m in suggested if module_exists(ws, m)] + extra
        # 3. verify, widening on failure
        attempt = [base, base + FALLBACKS[:1], base + FALLBACKS[:2]]
        chosen, log = None, ""
        for i, mods in enumerate(attempt):
            block = "\n".join(f"import {m}" for m in sorted(set(mods)))
            trial = lines[:]; trial[idx[0]] = block
            for j in idx[1:]: trial[j] = ""
            cand = scratch / "trial.lean"; cand.write_text("\n".join(trial) + "\n", encoding="utf-8")
            t0 = time.time(); rc, out = run_lean(ws, cand)
            ok = rc == 0 and ": error" not in out
            print(f"trial {i + 1}: {len(set(mods))} imports -> {'compiles' if ok else 'FAILS'} ({time.time() - t0:.0f} s)")
            if ok:
                chosen = sorted(set(mods)); break
            log = out
        if chosen is None:
            print(log[-2500:]); print("RESULT: kept `import Mathlib` (no trimmed import set compiled)"); sys.exit(1)
        # 4. tidy: drop a module when another chosen module is its parent umbrella, if that still compiles
        tidy = [m for m in chosen if not any(o != m and m.startswith(o + ".") for o in chosen)]
        if len(tidy) < len(chosen):
            block = "\n".join(f"import {m}" for m in tidy)
            trial = lines[:]; trial[idx[0]] = block
            for j in idx[1:]: trial[j] = ""
            cand = scratch / "tidy.lean"; cand.write_text("\n".join(trial) + "\n", encoding="utf-8")
            rc, out = run_lean(ws, cand)
            if rc == 0 and ": error" not in out:
                print(f"tidy: {len(chosen)} -> {len(tidy)} imports (parent umbrellas cover the rest)")
                chosen = tidy
        block = "\n".join(f"import {m}" for m in chosen)
        print("RESULT:\n" + block)
        if a.apply:
            new = lines[:]; new[idx[0]] = block
            for j in idx[1:]: new[j] = ""
            f.write_text("\n".join(new) + "\n", encoding="utf-8")
            print(f"applied to {f}; rebuild with lake_build.sh")
        else:
            print("(dry run: add --apply to rewrite the file)")
    finally:
        shutil.rmtree(scratch, ignore_errors=True)


if __name__ == "__main__":
    main()
