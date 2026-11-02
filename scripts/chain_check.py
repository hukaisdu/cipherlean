#!/usr/bin/env python3
"""chain_check.py — compare the proof chain the reader confirmed (CHAIN.md) with the dependency
graph Lean actually used.  (step 7 of the skill, before the report; step 8's reviewer reruns it)

For the paper module(s) it takes, from one `lake env lean` run (inspect_lean.py, or an earlier run's JSON
with --listing), for every declaration the constants its *proof term* uses and the constants its *statement*
(type) uses (within the module and the library CipherLean/Lib), maps CHAIN.md's `lean` column to those names,
and reports:
  - chain edges `A uses B` that Lean realises directly (the proof of A uses B), only in the statement
    of A (its type mentions B, the proof never unfolds it), only transitively, or not at all;
  - Lean dependencies between chain nodes that the chain does not mention (extra edges; proof terms only);
  - chain rows whose `lean` name does not exist, and module declarations absent from the chain
    (the auxiliary declarations Lean generates, `foo.congr_simp` and the like, are left out).
A `lean` cell that is not one identifier (`decide +kernel`, "proved in project X as foo") is listed as a
note and not checked. External rows (kind `external`) are not checked. Exit 1 if an edge is missing or a
name unknown.

usage: chain_check.py CHAIN.md <file.lean> [<file2.lean> ...] [--ws DIR] [--listing FILE.json]
(several files = the pieces of one formalization; all of them count as the paper module)
"""
import argparse, os, pathlib, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check_lean as ck  # noqa: E402
import chain_graph as cg  # noqa: E402
import inspect_lean as il  # noqa: E402

# a `lean` cell is one declaration name: letters, digits, `_`, `.`, `'`, `!`, `?`, subscripts, `«»`;
# anything else (spaces, `:`, `+`, several names) is a note
IDENT = re.compile(r"^[^\W\d][\w.'!?₀-₉«»]*$")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("chain"); ap.add_argument("files", nargs="+"); ap.add_argument("--ws"); ap.add_argument("--timeout", type=int, default=1800)
    ap.add_argument("--listing", metavar="FILE.json", help="use this inspect_lean.py listing instead of running Lean")
    a = ap.parse_args()
    ws = ck.find_workspace(a.ws)
    mods = [ck.module_name(ws, f) for f in a.files]
    mod = ", ".join(mods)
    if a.listing:
        lst = il.load(a.listing)
        if not lst.get("ok", True) or any(m not in lst.get("modules", []) for m in mods):
            ck.die(f"{a.listing} does not list {mod}")
    else:
        lst = il.listing(ws, a.files, timeout=a.timeout)
        if not lst["ok"]:
            ck.die(f"dependency listing failed for {mod} (built? `lake_build.sh <module>` for each):\n{lst.get('output', '')[-2000:]}")
    deps, tdeps, side = {}, {}, {}
    for d in lst["declarations"]:
        if d["kind"] in ("ctor", "rec", "quot"):
            continue
        n = d["name"]
        deps[n] = set(d["proof_consts"]) - {n}; tdeps[n] = set(d["type_consts"]) - {n}
        side[n] = "PAPER" if d["side"] == "PAPER" and d["module"] in mods else "LIB"

    rows = cg.parse_chain(pathlib.Path(a.chain).read_text(encoding="utf-8"))
    nodes, edges = cg.nodes_edges(rows)
    lean_of, notes = {}, {}
    for r in rows:
        nid = r["id"].strip("`"); ln = r.get("lean", "").strip().strip("`").strip()
        if nid in nodes and ln and ln != "—":
            if IDENT.match(ln):
                lean_of[nid] = ln
            else:
                notes[nid] = ln          # item 9: a note, not a name; listed, never UNKNOWN
    # transitive closure of the Lean graph (proof terms and statements)
    closure = {}
    def reach(n):
        if n in closure:
            return closure[n]
        seen, stack = set(), list(deps.get(n, set()) | tdeps.get(n, set()))
        while stack:
            m = stack.pop()
            if m in seen:
                continue
            seen.add(m); stack.extend(deps.get(m, set()) | tdeps.get(m, set()))
        closure[n] = seen
        return seen

    report, bad = [], 0
    report.append(f"# Chain check — `{mod}` against `{pathlib.Path(a.chain).name}`\n")
    outside = {nid for nid, ln in lean_of.items() if ln not in deps and nodes[nid]["kind"] in ("external", "assumption")}
    for nid in sorted(outside):
        report.append(f"- `{nid}` → `{lean_of[nid]}` is outside the module and the library (Mathlib or a type): not checked")
    for nid, ln in notes.items():
        report.append(f"- `{nid}`: the `lean` cell is a note, not a declaration name (\"{ln}\"): not checked")
    unknown = [(nid, ln) for nid, ln in lean_of.items() if ln not in deps and nid not in outside]
    for nid, ln in unknown:
        report.append(f"- UNKNOWN `{nid}` → `{ln}` is not a declaration of the module or the library"); bad += 1
    report.append("\n## Chain edges (paper: A uses B)\n\n| A | B | in Lean |\n|---|---|---|")
    for A, B, opt in edges:
        if nodes[A]["kind"] in ("external", "assumption") or nodes[B]["kind"] in ("external", "assumption") \
                or A in outside or B in outside:
            report.append(f"| `{A}` | `{B}` | external / assumption, not checked |"); continue
        la, lb = lean_of.get(A), lean_of.get(B)
        if not la or not lb or la not in deps:
            report.append(f"| `{A}` | `{B}` | no Lean name on one side |"); continue
        if lb in deps.get(la, set()):
            report.append(f"| `{A}` | `{B}` | direct |")
        elif lb in tdeps.get(la, set()):
            report.append(f"| `{A}` | `{B}` | statement (the type of `{la}` mentions `{lb}`; the proof does not unfold it) |")
        elif lb in reach(la):
            report.append(f"| `{A}` | `{B}` | transitive (through helpers) |")
        elif la == lb:
            report.append(f"| `{A}` | `{B}` | same declaration |")
        elif opt:
            report.append(f"| `{A}` | `{B}` | paper's route only (`{A}` marked `{B}?`); Lean proves it another way |")
        else:
            report.append(f"| `{A}` | `{B}` | **MISSING**: `{la}` does not use `{lb}` |"); bad += 1
    chain_closure = {}
    def creach(n):
        if n in chain_closure:
            return chain_closure[n]
        seen, stack = set(), [b for (x, b, _) in edges if x == n]
        while stack:
            m = stack.pop()
            if m in seen:
                continue
            seen.add(m); stack.extend(b for (x, b, _) in edges if x == m)
        chain_closure[n] = seen
        return seen
    report.append("\n## Lean edges between chain nodes that the chain does not mention\n")
    inv = {ln: nid for nid, ln in lean_of.items()}
    extra = 0
    for la, used in deps.items():
        A = inv.get(la)
        if not A or side.get(la) != "PAPER":
            continue
        for lb in used:
            B = inv.get(lb)
            if B and B != A and B not in creach(A) and nodes[B]["kind"] not in ("external", "assumption"):
                report.append(f"- `{A}` (`{la}`) uses `{B}` (`{lb}`) in Lean; add it to `uses` or explain"); extra += 1
    if not extra:
        report.append("- none")
    report.append("\n## Module declarations not in the chain\n")
    missing = [n for n, s in side.items() if s == "PAPER" and n not in inv and not ck.is_auxiliary(n)]
    report.append(", ".join(f"`{n}`" for n in missing) if missing else "- none")
    n_aux = sum(1 for n, s in side.items() if s == "PAPER" and ck.is_auxiliary(n))
    if n_aux:
        report.append(f"\n({n_aux} auxiliary declaration(s) generated by Lean, `*.congr_simp` and the like, left out)")
    report.append(f"\nVERDICT: {'CONSISTENT' if bad == 0 else 'INCONSISTENT'} ({bad} missing edge(s)/unknown name(s), {extra} extra edge(s)"
                  + (f", {len(notes)} lean cell(s) that are notes" if notes else "") + ")")
    print("\n".join(report))
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
