#!/usr/bin/env python3
"""promote_candidates.py — which declarations of a finished formalization belong in the shared
library CipherLean/Lib?  (step 7b of the skill)

For the paper file(s) given — several files are the pieces of one theorem, a directory is every built,
non-template .lean file in it — it loads the modules next to the library in one Lean process (inspect_lean.py
with --dups, or an earlier run's JSON with --listing), lists every declaration with its elaborated statement and
the constants that statement uses, and sorts them into:

  A  lemma about library objects only, general in the index type      -> strong candidate
  B  general, but its statement uses an object the paper defined      -> candidate together with
                                                                          that object (see E)
  E  an object the paper defined (def / abbrev / structure)           -> decide: general notion
                                                                          (promote with its lemmas)
                                                                          or paper-specific (keep)
  F  general, uses only Mathlib (no library object)                   -> candidate for F2/Vec or a
                                                                          new module, low priority
  C  concrete sizes (toy instances, counterexamples, named test S-boxes,
     a paper definition applied to numerals such as `map 3 3 0 1`)    -> stays with the paper
  D  the same statement already exists in the library (theorems only) -> delete the copy, import

"Paper objects" are the definitions of all the files given, so a lemma of piece C about piece B's
`Bout` is B, not A. The output is one Markdown report with one table per module (stdout; with --write it is
appended as a dated section to the paper directory's PROMOTE.md, one file per paper whatever the number of
pieces or runs) that the agent reads and the user decides on; the mechanical move is described in
references/promotion.md, the re-pointing of the .md files is `repoint_names.py`.

usage: promote_candidates.py <file.lean | CipherLean/<Slug>/> [<file2.lean> ...] [--ws DIR] [--write] [--json] [--listing FILE.json]
"""
import argparse, datetime, json, os, pathlib, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check_lean as ck  # noqa: E402  (find_workspace, module_name, die)
import inspect_lean as il  # noqa: E402

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
    # a paper definition applied to numerals (`map 3 3 0 1`, `cell 3 …`) makes a statement concrete (item 39)
    def_shorts = sorted({short(n, paper_ns) for n in paper_defs}, key=len, reverse=True)
    applied = re.compile(r"(?<![\w.'])(?:[\w']+\.)*(?:" + "|".join(re.escape(s) for s in def_shorts) + r")(?:\s+\d+)+(?![\w'])") if def_shorts else None
    rows = []
    for d in paper_decls:
        name, ty, used = d["name"], d["type"], set(d["used"])
        if INSTNAME.search(name):
            continue
        uses_lib = sorted(short(u, ["CipherLean"]) for u in used if u in lib_names)
        uses_paper = sorted(short(u, paper_ns) for u in used if u in paper_defs and u != name)
        concrete = bool(CONCRETE.search(ty)) or bool(TOYNAME.search(short(name, paper_ns))) or bool(applied and applied.search(ty))
        # D only for theorems: for a def the "statement" is its type, and two unrelated maps of the same
        # type (`internalPart`, `chiMap` : Vec (Fin r) → Vec (Fin r)) are not duplicates (2026-11-02)
        dup = (dups.get(name) or lib_by_type.get(norm_type(ty, ["CipherLean"] + paper_ns))) if d["kind"] == "theorem" else None
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
                     "uses_paper": uses_paper, "uses_lib": uses_lib, "module": d["module"]})
    return rows


def report(rows, module, file, context=""):
    order = {"A": 0, "B": 1, "E": 2, "F": 3, "D": 4, "C": 5}
    rows = sorted(rows, key=lambda r: (order[r["class"]], r["name"]))
    counts = {k: sum(1 for r in rows if r["class"] == k) for k in "ABEFDC"}
    out = [f"### Candidates — `{module}`", "",
           f"Source: `{file}`. Classes: A lemma about library objects only · B general but uses a paper",
           "object · E object defined here · F general, Mathlib only · D duplicate of a library statement ·",
           "C concrete / toy. Counts: " + ", ".join(f"{k} {v}" for k, v in counts.items()) + "."
           + (f" Paper objects: the definitions of {context}." if context else ""), "",
           "| class | declaration | kind | why | suggested target |", "|---|---|---|---|---|"]
    for r in rows:
        out.append(f"| {r['class']} | `{r['name']}` | {r['kind']} | {r['why']} | `{r['target']}` |" if r["target"] != "—"
                   else f"| {r['class']} | `{r['name']}` | {r['kind']} | {r['why']} | — |")
    out += ["", "#### Statements (for the fidelity check before moving)", ""]
    for r in rows:
        if r["class"] in ("A", "B", "E", "F"):
            out.append(f"- `{r['name']}` : `{r['type']}`")
    return "\n".join(out) + "\n"


FOOTER = ("Decide per row (references/promotion.md): A and F move as they are; E moves only if the object is a general\n"
          "notion (then its B lemmas follow); D is deleted in favour of the import; C stays. After moving: rebuild\n"
          "`CipherLean`, run check_lean.py on the module, add the rows to `CipherLean/Lib/NOTATION.md`, re-check the\n"
          "paper file, re-point the .md files (`repoint_names.py`).\n")


def is_template(f):
    s = f.read_text(encoding="utf-8", errors="replace")
    return "<Slug>" in s or "theorem main : True" in s        # the untouched Main.lean of new_paper.sh


def collect(ws, paths):
    """The .lean files to list: as given, or for a directory its built, non-template files."""
    files = []
    for p in paths:
        p = pathlib.Path(p).resolve()
        if p.is_dir():
            for f in sorted(p.glob("*.lean")):
                mod = ck.module_name(ws, f)
                if is_template(f):
                    print(f"[skipped: untouched template] {f.name}", file=sys.stderr); continue
                if not (ws / ".lake" / "build" / "lib" / "lean" / pathlib.Path(*mod.split("."))).with_suffix(".olean").exists():
                    print(f"[skipped: not built] {f.name} (`lake_build.sh {mod}`)", file=sys.stderr); continue
                files.append(f)
        elif p.suffix == ".lean":
            files.append(p)
        else:
            ck.die(f"not a .lean file or a directory: {p}")
    if not files:
        ck.die("no built, non-template .lean file to list")
    return files


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("paths", nargs="+", help=".lean files (the pieces of one formalization) or a paper directory CipherLean/<Slug>/")
    ap.add_argument("--ws")
    ap.add_argument("--write", action="store_true", help="also append the report, dated, to PROMOTE.md next to the first file")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--timeout", type=int, default=1800)
    ap.add_argument("--listing", metavar="FILE.json", help="use this inspect_lean.py --dups listing instead of running Lean")
    a = ap.parse_args()
    ws = ck.find_workspace(a.ws)
    files = collect(ws, a.paths)
    mods = [ck.module_name(ws, f) for f in files]
    if a.listing:
        lst = il.load(a.listing)
        if not lst.get("ok", True) or any(m not in lst.get("modules", []) for m in mods):
            ck.die(f"{a.listing} does not list {', '.join(mods)}")
        if "dups" not in lst:
            ck.die(f"{a.listing} was made without --dups")
    else:
        lst = il.listing(ws, files, dups=True, timeout=a.timeout)
        if not lst["ok"]:
            ck.die(f"listing failed for {', '.join(mods)} (built? `lake_build.sh <module>` for each):\n{lst.get('output', '')[-2000:]}")
    paper, lib, dups = [], [], lst.get("dups", {})
    for d in lst["declarations"]:
        if d["kind"] in ("ctor", "rec", "quot") or d["auxiliary"]:
            continue
        row = {"name": d["name"], "kind": d["kind"], "type": d["statement"], "used": d["type_consts"],
               "module": d["module"] if d["side"] == "PAPER" and d["module"] in mods else "LIB"}
        (paper if row["module"] != "LIB" else lib).append(row)
    paper_ns = sorted({n.rsplit(".", 1)[0] for n in (d["name"] for d in paper) if "." in n}, key=len, reverse=True)
    rows = classify(paper, lib, paper_ns, dups)     # one context: the paper objects of every piece
    rel = lambda f: f.relative_to(ws) if str(f).startswith(str(ws)) else f
    context = ", ".join(f"`{m}`" for m in mods) if len(mods) > 1 else ""
    texts, out_json = [], []
    for f, mod in zip(files, mods):
        mrows = [r for r in rows if r["module"] == mod]
        texts.append(report(mrows, mod, rel(f), context))
        out_json.append({"module": mod, "rows": mrows})
    text = "\n".join(texts) + "\n" + FOOTER
    if a.json:
        print(json.dumps(out_json, ensure_ascii=False, indent=1))
    else:
        print(text)
    if a.write:
        dest = files[0].parent / "PROMOTE.md"
        slug = files[0].parent.name
        head = f"# PROMOTE — {slug}: library candidates (step 7), one dated report per run, newest last\n"
        stamp = datetime.datetime.now().strftime("%Y-%m-%d %H:%M")
        section = f"\n## {stamp} — " + ", ".join(f"`{m}`" for m in mods) + "\n\n" + text
        old = dest.read_text(encoding="utf-8") if dest.exists() else ""
        dest.write_text((old if old.startswith("# PROMOTE — ") else head + old) + section, encoding="utf-8")
        print(f"[appended to {dest}]", file=sys.stderr)


if __name__ == "__main__":
    main()
