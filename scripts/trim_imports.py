#!/usr/bin/env python3
"""trim_imports.py — replace a file's Mathlib imports by the minimal set a finished file needs,
verified by compiling the result.

Why: every Lean process that starts with `import Mathlib` maps about 8300 .olean files (27 s on a
laptop even when cached); the modules a finished file really needs load in 3-7 s. So every later
`lake build`, every `check_lean.py` run and every reader of the file gets faster. Do it once the
proofs are done; keep `import Mathlib` while developing.

How: appends `#min_imports` (Mathlib.Tactic.MinImports) to a scratch copy, reads the modules it
suggests, adds the umbrella modules of the tactics the file uses (the command sees the lemmas a
tactic produced, not the tactic's own implementation), compiles the trimmed copy with
`lake env lean`; on failure adds `Mathlib.Tactic.Common`, then `Mathlib.Tactic`; if nothing
compiles the file is left unchanged. Every `import Mathlib…` line is replaced — the umbrella `import
Mathlib`, or a hand-chosen list of specific modules, which is minimized the same way and left alone
when `#min_imports` agrees with it — and any other import line that turns out redundant (an umbrella
such as `import CipherLean`) is dropped; the rest (sibling pieces, library modules, Aesop, ...) is kept.
Writes the file only with --apply.

What the suggested modules are: `#min_imports` collects the constants the declarations use — directly,
and transitively through the proofs of the lemmas they call (instances found by typeclass search and
lemmas `simp` picked included) — plus the syntax kinds and attributes, maps each to the module that
declares it, and keeps the modules no other kept module imports. A module can be on that list only
because it was imported: a late instance such as `IsAzumaya.id : IsAzumaya R R` wins the typeclass
search for a parent class (`Module.Finite R R`) while its module is in scope, the proof term then
mentions it, and `#min_imports` reports `Mathlib.Algebra.Azumaya.Basic` although the file never names
anything of it (WHConj3's `Assembly.lean` carried five such RingTheory modules out of its first trim
under `import Mathlib`). So, once the suggested set compiles, the script tries the file without each
suggested Mathlib module and drops the ones it compiles without. `--why` prints, per suggested module,
the constants of the file declared there (direct) and how many the closure reaches there.

usage: trim_imports.py <file.lean> [--apply] [--why] [--ws DIR]
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
MATHLIB_IMPORT = re.compile(r"^import Mathlib(\.\S+)?\s*$")

# with --why: which constants come from which module. The declarations of the scratch file have no module
# of their own (module index none). WHYD lines: a constant one of them uses directly; WHYT lines: per module,
# how many constants of the transitive closure (what #min_imports looks at) are declared there, with examples.
WHY = r'''
open Lean in
#eval show Lean.Elab.Command.CommandElabM Unit from do
  let env ← Lean.getEnv
  let mine : Array Name := env.constants.fold (init := #[]) fun acc n _ =>
    if env.getModuleIdxFor? n == none && !n.isInternalDetail then acc.push n else acc
  let modOf (m : Name) : Option Name := (env.getModuleIdxFor? m).map fun i => env.header.moduleNames[i.toNat]!
  let mut stack : Array Name := #[]
  for n in mine do
    let some c := env.find? n | continue
    let cs := c.getUsedConstantsAsSet.toArray      -- type and value, theorem proofs included
    for m in cs do
      if let some md := modOf m then IO.println s!"WHYD\t{md}\t{m}\t{n}"
    stack := stack ++ cs
  let mut seen : NameSet := {}
  let mut byMod : NameMap (Nat × Array Name) := {}
  let mut fuel := 10000000
  while fuel > 0 do
    fuel := fuel - 1
    match stack.back? with
    | none => break
    | some m =>
      stack := stack.pop
      if seen.contains m then continue
      seen := seen.insert m
      let some c := env.find? m | continue
      if let some md := modOf m then
        let (k, ex) : Nat × Array Name := byMod.getD md (0, #[])
        byMod := byMod.insert md (k + 1, if ex.size < 3 then ex.push m else ex)
      stack := stack ++ c.getUsedConstantsAsSet.toArray
  for (md, (k, ex)) in byMod.toList do
    IO.println s!"WHYT\t{md}\t{k}\t{",".intercalate (ex.toList.map toString)}"
'''


def die(msg):
    print(f"trim_imports: {msg}", file=sys.stderr); sys.exit(2)


def run_lean(ws, path, timeout=3600):
    env = dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + os.pathsep + os.environ.get("PATH", ""))
    p = subprocess.run(["lake", "env", "lean", str(path)], cwd=ws, capture_output=True, text=True, timeout=timeout, env=env)
    return p.returncode, (p.stdout or "") + (p.stderr or "")


def own_mod(line):
    return line.strip()[len("import "):].strip()


def module_exists(ws, mod):
    parts = mod.split(".")
    if parts[0] == "Mathlib":
        return (ws / ".lake/packages/mathlib" / pathlib.Path(*parts)).with_suffix(".lean").exists()
    return True  # other packages: trust the name


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("file"); ap.add_argument("--apply", action="store_true"); ap.add_argument("--ws")
    ap.add_argument("--why", action="store_true", help="print which constant each suggested module supplies")
    a = ap.parse_args()
    ws = pathlib.Path(a.ws or os.environ.get("CIPHERLEAN_WS") or os.path.expanduser("~/cipherlean")).resolve()
    if not (ws / "lakefile.toml").exists():
        die(f"no lakefile in {ws}: run scripts/setup_env.sh --install (or set --ws / CIPHERLEAN_WS)")
    f = pathlib.Path(a.file).resolve(); src = f.read_text(encoding="utf-8")
    lines = src.splitlines()
    idx = [i for i, l in enumerate(lines) if MATHLIB_IMPORT.match(l.strip())]
    if not idx:
        print("nothing to do: the file imports nothing from Mathlib"); return
    umbrella = any(lines[i].strip() == "import Mathlib" for i in idx)
    current = sorted({lines[i].strip()[len("import "):] for i in idx})
    scratch = pathlib.Path(tempfile.mkdtemp(prefix="trim_", dir=ws / ".lake"))
    try:
        # 1. ask Mathlib for the minimal imports (the command itself needs Mathlib.Tactic.MinImports)
        probe = scratch / "probe.lean"
        head = lines[:]
        if not umbrella:
            head[idx[-1]] = lines[idx[-1]] + "\nimport Mathlib.Tactic.MinImports"
        probe.write_text("\n".join(head) + "\n\n#min_imports\n" + (WHY if a.why else ""), encoding="utf-8")
        t0 = time.time(); rc, out = run_lean(ws, probe)
        if rc != 0 and a.why:
            # the file may be fine and only the --why snippet broken (a Lean version drift): retry without it
            probe.write_text("\n".join(head) + "\n\n#min_imports\n", encoding="utf-8")
            rc2, out2 = run_lean(ws, probe)
            if rc2 == 0:
                print("(--why snippet failed on this Lean version; continuing without it)\n" + out[-800:])
                rc, out, a.why = rc2, out2, False
        if rc != 0:
            print(out[-3000:]); die("the file does not compile as it is; fix it before trimming")
        suggested = sorted({m.group(2) for m in re.finditer(r"^(public )?import (\S+)", out, re.M)})
        print(f"#min_imports suggests {len(suggested)} modules ({time.time() - t0:.0f} s): " + ", ".join(suggested))
        if a.why:
            direct, trans = {}, {}
            for line in out.splitlines():
                if line.startswith("WHYD\t"):
                    _, mod, const, decl = line.split("\t", 3)
                    direct.setdefault(mod, {}).setdefault(const, set()).add(decl)
                elif line.startswith("WHYT\t"):
                    _, mod, k, ex = line.split("\t", 3)
                    trans[mod] = (int(k), [e for e in ex.split(",") if e])
            print("why (per suggested module: constants the file's declarations use directly; the transitive closure #min_imports looks at):")
            for mod in suggested:
                cs = direct.get(mod, {})
                shown = ", ".join(f"`{c}` (in {', '.join(sorted(d)[:2])})" for c, d in sorted(cs.items())[:4])
                k, ex = trans.get(mod, (0, []))
                print(f"  {mod}: direct " + (shown + (f", … {len(cs)} constants" if len(cs) > 4 else "") if cs else "none")
                      + f"; transitive {k}" + (f", e.g. " + ", ".join(f"`{e}`" for e in ex) if ex else ""))
        if not umbrella:
            plus, minus = sorted(set(suggested) - set(current)), sorted(set(current) - set(suggested))
            if not plus and not minus:
                print("RESULT: the file's Mathlib imports are already the ones #min_imports suggests; nothing to change")
                return
            print("difference to the file's imports: " + ", ".join(f"+{m}" for m in plus) + (" " if plus and minus else "") + ", ".join(f"-{m}" for m in minus))
        # 2. tactic umbrellas
        extra = []
        for pat, mod in TACTIC_UMBRELLAS.items():
            if mod and re.search(pat, src) and module_exists(ws, mod) and mod not in suggested:
                extra.append(mod)
        if extra:
            print("tactics used, adding: " + ", ".join(extra))
        # a suggested module the file already imports on its own line (a sibling piece, a library module)
        # keeps that line; the block holds the rest
        others = [i for i, l in enumerate(lines) if l.startswith("import ") and i not in idx]
        own = {lines[i].strip()[len("import "):].strip(): i for i in others}
        base = [m for m in suggested if module_exists(ws, m) and m not in own] + extra
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
            print(log[-2500:]); print("RESULT: kept the file's imports (no trimmed import set compiled)"); sys.exit(1)
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
        # 4b. a suggested Mathlib module may be needed only because it was imported (a late instance won
        #     the typeclass search, see the docstring): try the file without each one, one at a time
        candidates = [m for m in chosen if m.startswith("Mathlib.") and m not in extra]
        if len(candidates) > 8:
            print(f"({len(candidates)} suggested Mathlib modules: not trying the file without each; do it by hand for a surprising one)")
            candidates = []
        for m in candidates:
            mods = [x for x in chosen if x != m]
            block = "\n".join(f"import {x}" for x in mods)
            trial = lines[:]; trial[idx[0]] = block
            for j in idx[1:]: trial[j] = ""
            cand = scratch / "without.lean"; cand.write_text("\n".join(trial) + "\n", encoding="utf-8")
            t0 = time.time(); rc, out = run_lean(ws, cand)
            if rc == 0 and ": error" not in out:
                chosen = mods; print(f"not needed once it is not imported, dropped: {m} ({time.time() - t0:.0f} s)")
            else:
                print(f"needed: {m} ({time.time() - t0:.0f} s)")
        block = "\n".join(f"import {m}" for m in chosen)
        # 5. other import lines of the header (an umbrella such as `import CipherLean`) are dropped one by
        #    one when the file still compiles without them (2026-11-02: the umbrella stayed behind once);
        #    a line #min_imports itself asked for is kept without a trial
        dropped = []
        for i in others:
            if own_mod(lines[i]) in suggested:
                continue
            trial = lines[:]; trial[idx[0]] = block
            for j in idx[1:]: trial[j] = ""
            for j in dropped + [i]: trial[j] = ""
            cand = scratch / "drop.lean"; cand.write_text("\n".join(trial) + "\n", encoding="utf-8")
            rc, out = run_lean(ws, cand)
            if rc == 0 and ": error" not in out:
                dropped.append(i); print(f"redundant, dropped: {lines[i].strip()}")
        if not umbrella and chosen == current and not dropped:
            print("RESULT: the file's imports are already minimal; nothing to change"); return
        kept = [lines[i].strip() for i in others if i not in dropped]
        print("RESULT:\n" + block + ("\n(kept as they are: " + ", ".join(kept) + ")" if kept else ""))
        if a.apply:
            new = lines[:]; new[idx[0]] = block
            for j in idx[1:]: new[j] = ""
            for j in dropped: new[j] = ""
            f.write_text("\n".join(new) + "\n", encoding="utf-8")
            print(f"applied to {f}; rebuild with lake_build.sh")
        else:
            print("(dry run: add --apply to rewrite the file)")
    finally:
        shutil.rmtree(scratch, ignore_errors=True)


if __name__ == "__main__":
    main()
