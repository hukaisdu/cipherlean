#!/usr/bin/env python3
"""check_lean.py — build one Lean file of the cipherlean workspace and check it.

What it does (the trust model of the cipherlean skill):
  1. `lake build <Module>` for the file (module name derived from its path; symlinked
     `CipherLean/<Slug>` directories are resolved).
  2. Lists, for EVERY non-internal declaration of the module, its kind, the axioms it
     depends on, and its elaborated statement (so a human can compare it with the paper):
     one `lake env lean` run through inspect_lean.py, or the JSON of an earlier run
     (--listing, as status.py --check passes it: one listing for all the piece files).
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

usage: check_lean.py <file.lean> [--ws DIR] [--allow-native] [--json] [--timeout SEC] [--no-build] [--listing FILE.json]
"""
import argparse, json, os, pathlib, re, sys

STANDARD = {"propext", "Classical.choice", "Quot.sound"}
NATIVE = {"Lean.ofReduceBool", "Lean.trustCompiler"}


# the workspace helpers and the auxiliary-name test live in inspect_lean (shared by every check script);
# they keep their names here because chain_check, notation_check, promote_candidates and trim_imports use `ck.*`
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import inspect_lean as il  # noqa: E402
from inspect_lean import is_auxiliary, find_workspace, module_name, lake, run  # noqa: E402,F401


def die(msg, code=2):
    print(f"check_lean: {msg}", file=sys.stderr)
    sys.exit(code)


def is_native(ax):
    """`native_decide` / `bv_decide` axioms: `Lean.ofReduceBool`, `Lean.trustCompiler`, and the
    per-declaration axioms Lean ≥ 4.3x generates, e.g. `foo._native.native_decide.ax_1_1`."""
    return ax in NATIVE or "native_decide" in ax or "._native." in ax
GREP = ["sorry", "native_decide", "bv_decide", r"\baxiom\b", r"\bunsafe\b",
        "implemented_by", r"\bextern\b", r"\badmit\b", "decide +native"]

def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("file")
    ap.add_argument("--ws")
    ap.add_argument("--allow-native", action="store_true")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--timeout", type=int, default=3600)
    ap.add_argument("--no-build", action="store_true", help="skip `lake build` (the module was just built)")
    ap.add_argument("--listing", metavar="FILE.json", help="use this inspect_lean.py listing instead of running Lean")
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

    # 2. axioms + statements (one listing, shared with the other checks)
    _t1 = _time.time()
    if a.listing:
        lst = il.load(a.listing)
        ok = lst.get("ok", True) and mod in lst.get("modules", [])
        if mod not in lst.get("modules", []):
            lst = {"ok": False, "declarations": [], "output": f"{a.listing} does not list {mod} (it lists {', '.join(lst.get('modules', []))})"}
    else:
        lst = il.listing(ws, [a.file], timeout=a.timeout)
        ok = lst["ok"]
    report["listing_seconds"] = round(_time.time() - _t1, 1)
    decls = []
    for d in lst["declarations"]:
        if d["side"] != "PAPER" or d["module"] != mod or d["kind"] in ("ctor", "rec", "quot"):
            continue
        axioms = d["axioms"] or []
        bad = [x for x in axioms if x not in STANDARD and not is_native(x)]
        if "sorryAx" in axioms or bad:
            status = "FAIL"
        elif any(is_native(x) for x in axioms):
            status = "NATIVE"
        else:
            status = "PASS"
        decls.append({"name": d["name"], "kind": d["kind"], "axioms": axioms, "status": status, "statement": d["statement"],
                      "auxiliary": d["auxiliary"]})
    if not ok:
        report["listing_output"] = lst.get("output", "")[-4000:]
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
