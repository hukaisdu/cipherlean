#!/usr/bin/env python3
"""notation_check.py — do the Lean names that NOTATION.md cites exist?  (step 7 of the skill)

The first independent review of a formalization found a NOTATION row naming a Lean identifier that did not
exist. This script reads every table row of NOTATION.md, takes the backticked snippets of its "Lean name"
column (the second column), extracts the leading identifier of each snippet and checks it: first against
the declarations of the paper modules given and of the library CipherLean/Lib (one `lake env lean` listing),
then, for what is left, with `#check @name` (so Mathlib names pass too). Snippets that are binders
(`hbij : …`), start with a symbol, or whose leading token is one or two characters (a variable) are skipped.

usage: notation_check.py CipherLean/<Slug>/NOTATION.md <file.lean> [<file2.lean> ...] [--ws DIR] [--open NS ...]
Exit 1 if a name is UNKNOWN. Read the list: a stray prose word in backticks is reported as unknown too.
"""
import argparse, os, pathlib, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check_lean as ck  # noqa: E402

LIST = r'''
import Lean
import CipherLean
{imports}
open Lean Elab Command
def listNames : CommandElabM Unit := do
  let env ← getEnv
  let mods : List Name := [{mods}]
  let idxs := mods.filterMap env.getModuleIdx?
  for (n, _) in env.constants.toList do
    if n.isInternalDetail then continue
    match env.getModuleIdxFor? n with
    | some i => if idxs.contains i then IO.println s!"NAME\t{{n}}"
    | none => pure ()
#eval listNames
'''
CHECK = r'''
import CipherLean
{imports}
open {opens}
{checks}
'''
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_.'!?₀-₉]*")
SKIP_FIRST = {"fun", "if", "then", "else", "let", "have", "show", "by", "no", "the", "written", "see", "or"}


def snippets(notation_text):
    out = []
    for line in notation_text.splitlines():
        if not line.strip().startswith("|"):
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) < 2 or cells[0] in ("paper symbol", "---"):
            continue
        for snip in re.findall(r"`([^`]+)`", cells[1]):
            s = snip.strip()
            if not s or not (s[0].isalpha() or s[0] == "_"):
                continue
            if re.match(r"^[A-Za-z_][A-Za-z0-9_']*\s*:\s", s):      # a binder `h : P`
                continue
            m = IDENT.match(s)
            if not m:
                continue
            tok = m.group(0).rstrip(".")
            if len(tok) <= 2 or tok in SKIP_FIRST:
                continue
            out.append((tok, cells[0][:50], snip))
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("notation"); ap.add_argument("files", nargs="+"); ap.add_argument("--ws")
    ap.add_argument("--open", nargs="*", default=None, help="namespaces to open for #check (default: CipherLean and the slug)")
    ap.add_argument("--timeout", type=int, default=600)
    a = ap.parse_args()
    ws = ck.find_workspace(a.ws)
    mods = [ck.module_name(ws, f) for f in a.files]
    slug = mods[0].split(".")[1] if mods[0].count(".") >= 2 else mods[0].split(".")[-1]
    opens = a.open if a.open is not None else ["CipherLean", slug]
    lib_dir = ws / "CipherLean" / "Lib"
    libmods = sorted(".".join(["CipherLean", "Lib", *f.relative_to(lib_dir).with_suffix("").parts]) for f in lib_dir.rglob("*.lean"))
    scratch_dir = ws / ".lake" / "promote"; scratch_dir.mkdir(parents=True, exist_ok=True)
    s1 = scratch_dir / "notation_names.lean"
    s1.write_text(LIST.format(imports="\n".join(f"import {m}" for m in mods), mods=", ".join("`" + m for m in mods + libmods)), encoding="utf-8")
    code, out = ck.run([ck.lake(), "env", "lean", str(s1)], cwd=str(ws), timeout=a.timeout)
    if "NAME\t" not in out:
        ck.die(f"name listing failed (modules built?):\n{out[-2000:]}")
    names = {l.split("\t", 1)[1].strip() for l in out.splitlines() if l.startswith("NAME\t")}
    shorts = {}
    for n in names:
        shorts.setdefault(n.split(".")[-1], set()).add(n)
    cands = snippets(pathlib.Path(a.notation).read_text(encoding="utf-8"))
    seen, todo, known = set(), [], {}
    for tok, row, snip in cands:
        if tok in seen:
            continue
        seen.add(tok)
        full = [n for n in names if n == tok or n.endswith("." + tok)]
        if full:
            known[tok] = sorted(full)[0]
        else:
            todo.append(tok)
    unknown = []
    if todo:
        checks = "\n".join(f"#check @{tok}" for tok in todo)
        s2 = scratch_dir / "notation_check.lean"
        s2.write_text(CHECK.format(imports="\n".join(f"import {m}" for m in mods), opens=" ".join(opens), checks=checks), encoding="utf-8")
        code, out = ck.run([ck.lake(), "env", "lean", str(s2)], cwd=str(ws), timeout=a.timeout)
        bad = set(re.findall(r"[Uu]nknown (?:identifier|constant) `?([^`'\s]+)", out))
        for tok in todo:
            if tok in bad or any(b.endswith("." + tok) or tok.endswith("." + b) for b in bad):
                unknown.append(tok)
            else:
                known[tok] = "(Mathlib / resolved by #check)"
    print(f"# NOTATION names — `{a.notation}` against {', '.join(mods)} and CipherLean/Lib\n")
    print("| name in NOTATION | resolves to |\n|---|---|")
    for tok in sorted(known):
        print(f"| `{tok}` | `{known[tok]}` |")
    for tok in unknown:
        rows = [row for t, row, _ in cands if t == tok]
        print(f"| `{tok}` | **UNKNOWN** (row: {rows[0]}) |")
    print(f"\nVERDICT: {'OK' if not unknown else 'UNKNOWN NAMES'} ({len(known)} resolved, {len(unknown)} unknown)")
    sys.exit(1 if unknown else 0)


if __name__ == "__main__":
    main()
