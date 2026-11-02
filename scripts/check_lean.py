#!/usr/bin/env python3
"""check_lean.py — build one Lean file of the cipherlean workspace and check it.

What it does (the trust model of the cipherlean skill):
  1. `lake build <Module>` for the file (module name derived from its path; symlinked
     `CipherLean/<Slug>` directories are resolved).
  2. Loads the module in a scratch Lean file and prints, for EVERY non-internal
     declaration of the module, its kind, the axioms it depends on, and its elaborated
     statement (so a human can compare it with the paper).
  3. Classifies each declaration:
       PASS    axioms ⊆ {propext, Classical.choice, Quot.sound}
       NATIVE  additionally Lean.ofReduceBool / Lean.trustCompiler or a generated
               `<decl>._native.native_decide.ax_*` axiom (native_decide, decide +native,
               bv_decide when it needs a SAT certificate — trusts the compiler)
       FAIL    sorryAx (a `sorry`, even one hidden in a macro) or any custom axiom
  4. Greps the source for `sorry`, `native_decide`, `bv_decide`, `axiom`, `unsafe`,
     `implemented_by`, `extern`, `admit` and lists the lines for human attention.
Exit code 0 iff no FAIL (and no NATIVE unless --allow-native). Use --json for machines.
The declaration count names two numbers apart: the source declarations and the auxiliary ones
Lean generates on first use (`foo.congr_simp` from `simp`, `foo.match_1`, `foo.proof_1`, `foo.eq_1`),
which `status.py` does not see in the source. A module with no declaration of its own (an aggregator
that only imports the pieces of a split theorem) passes with "0 declarations".

usage: check_lean.py <file.lean> [--ws DIR] [--allow-native] [--json] [--timeout SEC]
"""
import argparse, json, os, pathlib, re, shutil, subprocess, sys, tempfile

STANDARD = {"propext", "Classical.choice", "Quot.sound"}
NATIVE = {"Lean.ofReduceBool", "Lean.trustCompiler"}


AUX_RE = re.compile(r"\.(congr_simp|match_\d+|proof_\d+|eq_\d+|_cstage\d*)$")


def is_auxiliary(name):
    """Declarations Lean generates next to a user's: `foo.congr_simp` (simp's first use of `foo`),
    `foo.match_1`, `foo.proof_1`, `foo.eq_1`. They carry axioms like any other, so the check keeps
    them, but they are counted apart from the source declarations."""
    return bool(AUX_RE.search(name))


def is_native(ax):
    """`native_decide` / `bv_decide` axioms: `Lean.ofReduceBool`, `Lean.trustCompiler`, and the
    per-declaration axioms Lean ≥ 4.3x generates, e.g. `foo._native.native_decide.ax_1_1`."""
    return ax in NATIVE or "native_decide" in ax or "._native." in ax
GREP = ["sorry", "native_decide", "bv_decide", r"\baxiom\b", r"\bunsafe\b",
        "implemented_by", r"\bextern\b", r"\badmit\b", "decide +native"]

LEAN_LISTING = r'''
import Lean
import {module}

open Lean Elab Command Meta

/-- List every non-internal constant of one module: name, kind, axioms, statement. -/
def listModuleDecls (modName : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some idx := env.getModuleIdx? modName
    | throwError "module {{modName}} is not loaded"
  let names : Array Name := env.constants.fold (init := #[]) fun acc n _ =>
    if env.getModuleIdxFor? n == some idx && !n.isInternalDetail then acc.push n else acc
  let names := names.qsort (fun a b => a.toString < b.toString)
  for n in names do
    let some c := env.find? n | continue
    let kind := match c with
      | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
      | .opaqueInfo _ => "opaque" | .inductInfo _ => "inductive" | .quotInfo _ => "quot"
      | .ctorInfo _ => "ctor" | .recInfo _ => "rec"
    if kind == "ctor" || kind == "rec" || kind == "quot" then continue
    let axioms ← collectAxioms n
    let axStr := ",".intercalate (axioms.toList.map toString)
    let tyStr ← liftTermElabM do
      let fmt ← Meta.ppExpr c.type
      pure (fmt.pretty 100000)
    let tyOne := (tyStr.replace "\n" " ").replace "\t" " "
    IO.println s!"DECL\t{{n}}\t{{kind}}\t{{axStr}}\t{{tyOne}}"

#eval listModuleDecls `{module}
'''


def die(msg, code=2):
    print(f"check_lean: {msg}", file=sys.stderr)
    sys.exit(code)


def find_workspace(arg):
    ws = arg or os.environ.get("CIPHERLEAN_WS") or os.path.expanduser("~/cipherlean")
    ws = pathlib.Path(ws).resolve()
    if not (ws / "lakefile.toml").exists() and not (ws / "lakefile.lean").exists():
        die(f"no lakefile in workspace {ws}: run scripts/setup_env.sh --install (or set --ws / CIPHERLEAN_WS)")
    return ws


def module_name(ws, file):
    f = pathlib.Path(file).resolve()
    if f.suffix != ".lean":
        die(f"not a .lean file: {file}")
    try:
        rel = f.relative_to(ws)
        return ".".join(rel.with_suffix("").parts)
    except ValueError:
        pass
    formal = ws / "CipherLean"
    if formal.is_dir():
        for link in sorted(formal.iterdir()):
            if link.is_symlink():
                try:
                    rel = f.relative_to(link.resolve())
                    return ".".join(["CipherLean", link.name, *rel.with_suffix("").parts])
                except ValueError:
                    continue
    die(f"{f} is not inside the workspace {ws} (directly or through a CipherLean/<Slug> symlink)")


def lake():
    exe = shutil.which("lake") or os.path.expanduser("~/.elan/bin/lake")
    if not os.path.exists(exe):
        die("lake not found; install elan (https://lean-lang.org/install/)")
    return exe


def run(cmd, cwd, timeout):
    """Run `cmd` in the workspace under the shared build lock (one Lean job per workspace)."""
    import fcntl
    lock_path = pathlib.Path(cwd) / ".lake" / "cipherlean-build.lock"
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    # ~/.elan/bin first: non-login ssh shells do not have it on PATH (SKILL-NOTES item 2)
    env = dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + os.pathsep + os.environ.get("PATH", ""))
    with open(lock_path, "w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        try:
            p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout, env=env)
        except subprocess.TimeoutExpired:
            die(f"timed out after {timeout}s: {' '.join(cmd)}")
    return p.returncode, (p.stdout or "") + (p.stderr or "")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("file")
    ap.add_argument("--ws")
    ap.add_argument("--allow-native", action="store_true")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--timeout", type=int, default=3600)
    ap.add_argument("--no-build", action="store_true", help="skip `lake build` (the module was just built)")
    a = ap.parse_args()
    import time as _time
    _t0 = _time.time()

    ws = find_workspace(a.ws)
    mod = module_name(ws, a.file)
    src = pathlib.Path(a.file).resolve().read_text(encoding="utf-8")
    report = {"workspace": str(ws), "module": mod, "file": str(pathlib.Path(a.file).resolve())}

    # 1. build
    if a.no_build:
        rc, out = 0, ""
    else:
        rc, out = run([lake(), "build", mod], ws, a.timeout)
    report["build_ok"] = rc == 0
    report["build_seconds"] = round(_time.time() - _t0, 1)
    report["build_sorry_warnings"] = [l.strip() for l in out.splitlines() if "declaration uses 'sorry'" in l]
    if rc != 0:
        report["build_output"] = out[-6000:]
        emit(report, a, decls=[], verdict="FAIL (build error)")
        sys.exit(1)

    # 2. axioms + statements
    with tempfile.TemporaryDirectory(prefix="check_lean_") as td:
        listing = pathlib.Path(td) / "Listing.lean"
        listing.write_text(LEAN_LISTING.format(module=mod), encoding="utf-8")
        _t1 = _time.time()
        rc2, out2 = run([lake(), "env", "lean", str(listing)], ws, a.timeout)
        report["listing_seconds"] = round(_time.time() - _t1, 1)
    decls = []
    for line in out2.splitlines():
        if not line.startswith("DECL\t"):
            continue
        _, name, kind, axs, ty = (line.split("\t", 4) + [""] * 5)[:5]
        axioms = [x for x in axs.split(",") if x]
        bad = [x for x in axioms if x not in STANDARD and not is_native(x)]
        if "sorryAx" in axioms or bad:
            status = "FAIL"
        elif any(is_native(x) for x in axioms):
            status = "NATIVE"
        else:
            status = "PASS"
        decls.append({"name": name, "kind": kind, "axioms": axioms, "status": status, "statement": ty,
                      "auxiliary": is_auxiliary(name)})
    if rc2 != 0:
        report["listing_output"] = out2[-4000:]
        emit(report, a, decls, verdict="FAIL (could not list declarations)")
        sys.exit(1)
    report["declarations_source"] = sum(1 for d in decls if not d["auxiliary"])
    report["declarations_auxiliary"] = sum(1 for d in decls if d["auxiliary"])

    # 3. source greps
    report["source_hits"] = source_hits(src)

    fails = [d for d in decls if d["status"] == "FAIL"]
    natives = [d for d in decls if d["status"] == "NATIVE"]
    if fails:
        verdict = "FAIL"
    elif not decls:
        verdict = "PASS (0 declarations: the module only imports)"
    elif natives and not a.allow_native:
        verdict = "FAIL (native axioms; rerun with --allow-native if these are finite checks)"
    elif natives:
        verdict = "PASS (with native-trusting finite checks)"
    else:
        verdict = "PASS"
    emit(report, a, decls, verdict)
    sys.exit(0 if verdict.startswith("PASS") else 1)


def strip_comments(src):
    """Yield (lineno, code) with `--` line comments and `/- ... -/` block comments removed."""
    depth = 0
    for i, line in enumerate(src.splitlines(), 1):
        out, j = [], 0
        while j < len(line):
            if depth == 0 and line.startswith("--", j):
                break
            if line.startswith("/-", j):
                depth += 1; j += 2; continue
            if depth > 0 and line.startswith("-/", j):
                depth -= 1; j += 2; continue
            if depth == 0:
                out.append(line[j])
            j += 1
        yield i, "".join(out)


def source_hits(src):
    hits = []
    for i, code in strip_comments(src):
        for pat in GREP:
            if re.search(pat, code):
                hits.append({"line": i, "pattern": pat, "text": code.strip()})
    return hits


def emit(report, a, decls, verdict):
    report["declarations"] = decls
    report["verdict"] = verdict
    if a.json:
        print(json.dumps(report, indent=1, ensure_ascii=False))
        return
    print(f"# check_lean — {report['module']}")
    print(f"workspace: {report['workspace']}")
    print(f"build: {'ok' if report.get('build_ok') else 'FAILED'} ({report.get('build_seconds', 0)} s; listing {report.get('listing_seconds', 0)} s)")
    for w in report.get("build_sorry_warnings", []):
        print(f"  {w}")
    if "build_output" in report:
        print(report["build_output"])
    if "declarations_source" in report:
        aux = report.get("declarations_auxiliary", 0)
        print(f"declarations: {report['declarations_source']} source"
              + (f" (+ {aux} auxiliary generated by Lean: `*.congr_simp`, `*.match_n`, `*.proof_n`, `*.eq_n`)" if aux else ""))
    if decls:
        print("\n| declaration | kind | status | axioms |\n|---|---|---|---|")
        for d in decls:
            kind = d['kind'] + (" (aux)" if d.get("auxiliary") else "")
            print(f"| `{d['name']}` | {kind} | {d['status']} | {', '.join(d['axioms']) or '—'} |")
        print("\n## Statements (compare with the paper)")
        for d in decls:
            print(f"- `{d['name']}` : {d['statement']}")
    if "listing_output" in report:
        print(report["listing_output"])
    hits = report.get("source_hits", [])
    if hits:
        print("\n## Source lines to look at")
        for h in hits:
            print(f"- L{h['line']} [{h['pattern']}]: {h['text']}")
    print(f"\nVERDICT: {verdict}")


if __name__ == "__main__":
    main()
