#!/usr/bin/env python3
"""promote_candidates.py — which declarations of a finished formalization belong in the shared
library CipherLean/Lib?  (step 7b of the skill)

For one paper file (or every .lean file of a paper directory) it loads the module next to the
library, lists every declaration with its elaborated statement and the constants that statement
uses, and sorts them into:

  A  lemma about library objects only, general in the index type      -> strong candidate
  B  general, but its statement uses an object the paper defined      -> candidate together with
                                                                          that object (see E)
  E  an object the paper defined (def / abbrev / structure)           -> decide: general notion
                                                                          (promote with its lemmas)
                                                                          or paper-specific (keep)
  F  general, uses only Mathlib (no library object)                   -> candidate for F2/Vec or a
                                                                          new module, low priority
  C  concrete sizes (toy instances, counterexamples, named test S-boxes) -> stays with the paper
  D  the same statement already exists in the library                 -> delete the copy, import

and suggests a target module from the objects the statement mentions.  The output is a Markdown
report (stdout, or PROMOTE.md next to the file with --write) that the agent reads and the user
decides on; the mechanical move is described in references/promotion.md.

usage: promote_candidates.py <file.lean | CipherLean/<Slug>/> [--ws DIR] [--write] [--json]
"""
import argparse, json, os, pathlib, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check_lean as ck  # noqa: E402  (find_workspace, module_name, lake, run, die)

LEAN = r'''
import Lean
import CipherLean
import {paper}

open Lean Elab Command Meta

set_option maxRecDepth 8192

def listDecls : CommandElabM Unit := do
  let env ← getEnv
  let some pidx := env.getModuleIdx? `{paper} | throwError "paper module not loaded"
  let libMods : List Name := [{libmods}]
  let lidxs := libMods.filterMap env.getModuleIdx?
  let names : Array Name := env.constants.fold (init := #[]) fun acc n _ =>
    match env.getModuleIdxFor? n with
    | some i => if (i == pidx || lidxs.contains i) && !n.isInternalDetail
                  && !(n.components.getLast?.map (fun c => c.toString == "congr_simp" || (c.toString.startsWith "match_") || (c.toString.startsWith "proof_") || (c.toString.startsWith "eq_")) |>.getD false)
               then acc.push n else acc
    | none => acc
  let names := names.qsort (fun a b => a.toString < b.toString)
  for n in names do
    let some c := env.find? n | continue
    let kind := match c with
      | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
      | .opaqueInfo _ => "opaque" | .inductInfo _ => "inductive" | .quotInfo _ => "quot"
      | .ctorInfo _ => "ctor" | .recInfo _ => "rec"
    if kind == "ctor" || kind == "rec" || kind == "quot" then continue
    let side := if env.getModuleIdxFor? n == some pidx then "PAPER" else "LIB"
    let tyStr ← liftTermElabM do
      let fmt ← Meta.ppExpr c.type
      pure (fmt.pretty 100000)
    let tyOne := (tyStr.replace "\n" " ").replace "\t" " "
    let used := ",".intercalate (c.type.getUsedConstants.toList.map toString)
    IO.println s!"DECL\t{{n}}\t{{side}}\t{{kind}}\t{{tyOne}}\t{{used}}"
  -- duplicates: a paper declaration whose type is definitionally equal to a library declaration's
  let libNames := names.filter fun n => env.getModuleIdxFor? n != some pidx
  for n in names do
    if env.getModuleIdxFor? n != some pidx then continue
    let some c := env.find? n | continue
    for m in libNames do
      let some d := env.find? m | continue
      if c.levelParams.length != d.levelParams.length then continue
      let same ← liftTermElabM do
        let us ← mkFreshLevelMVars c.levelParams.length
        let t1 := c.type.instantiateLevelParams c.levelParams us
        let t2 := d.type.instantiateLevelParams d.levelParams us
        -- reducible transparency: a duplicate is the same statement up to notation, and full
        -- unfolding can recurse without bound on finite checks (maxRecDepth, 2026-11-02)
        withoutModifyingState (try withReducible (isDefEq t1 t2) catch _ => pure false)
      if same then IO.println s!"DUP\t{{n}}\t{{m}}"

#eval listDecls
'''

TARGETS = [  # (regex on the statement, suggested module)
    (r"\b(walsh|linCount|correlation)\b", "CipherLean/Lib/Walsh.lean"),
    (r"\b(ddt|diffUniformity|IsAPN|ddtMatrix)\b", "CipherLean/Lib/DDT.lean"),
    (r"\b(ann|coset|IsSubspace|dotForm|toSub)\b", "CipherLean/Lib/F2/Subspace.lean"),
    (r"\b(ofTable|toFun|toPerm|Sbox)\b", "CipherLean/Lib/Sbox.lean"),
    (r"\b(chi|sgn|toVec|ofVec|bvEquiv|Vec)\b", "CipherLean/Lib/F2/Vec.lean"),
]
CONCRETE = re.compile(r"\b(Fin|BitVec|Vector [^ ]+) \d+\b")
TOYNAME = re.compile(r"(toy|counterexample|Counterexample|_values|bad|present|cube|Table\b|check)", re.I)
INSTNAME = re.compile(r"(^|\.)inst[A-Z]")


def short(name, ns):
    for p in ns:
        if name.startswith(p + "."):
            return name[len(p) + 1:]
    return name


def norm_type(t, ns):
    t = re.sub(r"\s+", " ", t)
    for p in ns:
        t = t.replace(p + ".", "")
    t = re.sub(r"\[[A-Za-z_0-9✝']+ : ", "[", t)        # instance binder names
    t = re.sub(r"Type u_\d+", "Type u", t)              # universe names
    return t.strip()


def classify(paper_decls, lib_decls, paper_ns, dups=None):
    dups = dups or {}
    lib_names = {d["name"] for d in lib_decls}
    lib_by_type = {}
    for d in lib_decls:
        lib_by_type.setdefault(norm_type(d["type"], ["CipherLean"]), []).append(d["name"])
    paper_defs = {d["name"] for d in paper_decls if d["kind"] in ("def", "inductive", "opaque")}
    rows = []
    for d in paper_decls:
        name, ty, used = d["name"], d["type"], set(d["used"])
        if INSTNAME.search(name):
            continue
        uses_lib = sorted(short(u, ["CipherLean"]) for u in used if u in lib_names)
        uses_paper = sorted(short(u, paper_ns) for u in used if u in paper_defs and u != name)
        concrete = bool(CONCRETE.search(ty)) or bool(TOYNAME.search(short(name, paper_ns)))
        dup = dups.get(name) or lib_by_type.get(norm_type(ty, ["CipherLean"] + paper_ns))
        if dup:
            cls, why = "D", f"same statement as library `{'`, `'.join(short(x, ['CipherLean']) for x in dup)}`"
        elif concrete:
            cls, why = "C", "concrete sizes or a named test instance"
        elif d["kind"] != "theorem":
            cls, why = "E", "object defined by the paper: general notion or paper-specific?"
        elif uses_paper:
            cls, why = "B", "statement uses paper objects " + ", ".join(f"`{u}`" for u in uses_paper)
        elif uses_lib:
            cls, why = "A", "only library objects: " + ", ".join(f"`{u}`" for u in uses_lib)
        else:
            cls, why = "F", "general, Mathlib only"
        target = next((m for rx, m in TARGETS if re.search(rx, ty)), "new module under CipherLean/Lib/")
        if cls in ("C", "D"):
            target = "—"
        rows.append({"name": short(name, paper_ns), "full": name, "kind": d["kind"], "class": cls,
                     "why": why, "target": target, "type": re.sub(r"\s+", " ", ty),
                     "uses_paper": uses_paper, "uses_lib": uses_lib})
    return rows


def report(rows, module, file):
    order = {"A": 0, "B": 1, "E": 2, "F": 3, "D": 4, "C": 5}
    rows = sorted(rows, key=lambda r: (order[r["class"]], r["name"]))
    counts = {k: sum(1 for r in rows if r["class"] == k) for k in "ABEFDC"}
    out = [f"# Promotion candidates — `{module}`", "",
           f"Source: `{file}`. Classes: A lemma about library objects only · B general but uses a paper",
           "object · E object defined here · F general, Mathlib only · D duplicate of a library statement ·",
           "C concrete / toy. Counts: " + ", ".join(f"{k} {v}" for k, v in counts.items()) + ".", "",
           "| class | declaration | kind | why | suggested target |", "|---|---|---|---|---|"]
    for r in rows:
        out.append(f"| {r['class']} | `{r['name']}` | {r['kind']} | {r['why']} | `{r['target']}` |" if r["target"] != "—"
                   else f"| {r['class']} | `{r['name']}` | {r['kind']} | {r['why']} | — |")
    out += ["", "## Statements (for the fidelity check before moving)", ""]
    for r in rows:
        if r["class"] in ("A", "B", "E", "F"):
            out.append(f"- `{r['name']}` : `{r['type']}`")
    out += ["", "Decide per row (references/promotion.md): A and F move as they are; E moves only if the",
            "object is a general notion (then its B lemmas follow); D is deleted in favour of the import;",
            "C stays. After moving: rebuild `CipherLean`, run check_lean.py on the module, add the rows to",
            "`CipherLean/Lib/NOTATION.md`, re-check the paper file."]
    return "\n".join(out) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("path", help="a .lean file or a paper directory CipherLean/<Slug>/")
    ap.add_argument("--ws")
    ap.add_argument("--write", action="store_true", help="also write PROMOTE.md next to the file(s)")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--timeout", type=int, default=1800)
    a = ap.parse_args()
    ws = ck.find_workspace(a.ws)
    p = pathlib.Path(a.path).resolve()
    files = sorted(p.glob("*.lean")) if p.is_dir() else [p]
    if not files:
        ck.die(f"no .lean file in {p}")
    lib_dir = ws / "CipherLean" / "Lib"
    libmods = sorted(".".join(["CipherLean", "Lib", *f.relative_to(lib_dir).with_suffix("").parts])
                     for f in lib_dir.rglob("*.lean"))
    scratch_dir = ws / ".lake" / "promote"
    scratch_dir.mkdir(parents=True, exist_ok=True)
    all_rows = {}
    for f in files:
        mod = ck.module_name(ws, f)
        scratch = scratch_dir / (mod.replace(".", "_") + ".lean")
        scratch.write_text(LEAN.format(paper=mod, libmods=", ".join("`" + m for m in libmods)), encoding="utf-8")
        code, out = ck.run([ck.lake(), "env", "lean", str(scratch)], cwd=str(ws), timeout=a.timeout)
        if code != 0 or "DECL\t" not in out:
            ck.die(f"listing failed for {mod} (is the module built? `lake_build.sh {mod}`):\n{out[-2000:]}")
        paper, lib, dups = [], [], {}
        for line in out.splitlines():
            if line.startswith("DUP\t"):
                _, pn, ln = line.split("\t", 2)
                dups.setdefault(pn, []).append(ln)
                continue
            if not line.startswith("DECL\t"):
                continue
            _, name, side, kind, ty, used = line.split("\t", 5)
            d = {"name": name, "kind": kind, "type": ty, "used": [u for u in used.split(",") if u]}
            (paper if side == "PAPER" else lib).append(d)
        paper_ns = sorted({n.rsplit(".", 1)[0] for n in (d["name"] for d in paper) if "." in n}, key=len, reverse=True)
        rows = classify(paper, lib, paper_ns, dups)
        all_rows[mod] = rows
        text = report(rows, mod, f.relative_to(ws) if str(f).startswith(str(ws)) else f)
        if a.json:
            print(json.dumps({"module": mod, "rows": rows}, ensure_ascii=False, indent=1))
        else:
            print(text)
        if a.write:
            (f.parent / "PROMOTE.md").write_text(text if len(files) == 1 else
                                                  ((f.parent / "PROMOTE.md").read_text() if (f.parent / "PROMOTE.md").exists() and f != files[0] else "") + text,
                                                  encoding="utf-8")
            print(f"[written {f.parent / 'PROMOTE.md'}]", file=sys.stderr)


if __name__ == "__main__":
    main()
