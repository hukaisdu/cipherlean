#!/usr/bin/env python3
"""notation_check.py — do the Lean names that NOTATION.md (and README.md, CHAIN.md) cite exist?  (step 7)

The first independent review of a formalization found a NOTATION row naming a Lean identifier that did not
exist; the third found a stale name in README's Departures after a promotion rename. This script reads every
table row of NOTATION.md, takes the backticked snippets of its "Lean name" column (the second column),
extracts the leading identifier of each snippet and checks it: first against the declarations of the paper
modules given and of the library CipherLean/Lib (one `lake env lean` listing through inspect_lean.py, or an
earlier run's JSON with --listing), then, for what is left, with
`#check @name` (so Mathlib names pass too). Snippets that are binders (`hbij : …`), start with a symbol, are
a path or a file name (`Lib/LinStruct.lean`, `check_lemma24.py`), name a module that exists as a file
(`CipherLean.Lib.DDT`), or whose leading token is one or two characters (a variable, also `S.symm`, a
projection on one) are skipped.

`--also README.md CHAIN.md …` scans every backticked snippet of those files as well: a name qualified by
one of the formalization's namespaces (`WHConj3.foo`, `CipherLean.bar`) must exist, a short name counts as
resolved when it matches a declaration's last component or `#check` (a Mathlib lemma), and short
lemma-looking names that match nothing are listed for reading (prose, a name of another project, or stale?)
without failing the verdict.

usage: notation_check.py CipherLean/<Slug>/NOTATION.md <file.lean> [<file2.lean> ...] [--also <md> ...] [--ws DIR] [--open NS ...] [--listing FILE.json]
Exit 1 if a name is UNKNOWN. Read the list: a stray prose word in backticks is reported as unknown too.
"""
import argparse, os, pathlib, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import check_lean as ck  # noqa: E402
import inspect_lean as il  # noqa: E402

CHECK = r'''
import CipherLean
{imports}
open {opens}
{checks}
'''
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_.'!?₀-₉]*")
SKIP_FIRST = {"fun", "if", "then", "else", "let", "have", "show", "by", "no", "the", "written", "see", "or"}
PATHLIKE = re.compile(r"/|\.(lean|md|py|sh|tex|pdf|json|toml|txt|log|olean)\b")   # item 43: paths and file names


def ident_token(snip):
    """The leading identifier of a backticked snippet, or None when the snippet is not a name."""
    s = snip.strip()
    if not s or not (s[0].isalpha() or s[0] == "_"):
        return None
    if PATHLIKE.search(s):
        return None
    if re.match(r"^[A-Za-z_][A-Za-z0-9_']*\s*:\s", s):      # a binder `h : P`
        return None
    m = IDENT.match(s)
    if not m:
        return None
    tok = m.group(0).rstrip(".")
    if len(tok) <= 2 or tok in SKIP_FIRST or len(tok.split(".")[0]) <= 2:     # `S.symm`: a projection on a variable
        return None
    return tok


def snippets(notation_text):
    """(token, row label, snippet) for the Lean-name column of every table row of NOTATION.md."""
    out = []
    for line in notation_text.splitlines():
        if not line.strip().startswith("|"):
            continue
        cells = [c.strip() for c in line.strip().strip("|").split("|")]
        if len(cells) < 2 or cells[0] in ("paper symbol", "---"):
            continue
        for snip in re.findall(r"`([^`]+)`", cells[1]):
            tok = ident_token(snip)
            if tok:
                out.append((tok, cells[0][:50], snip))
    return out


def also_snippets(text):
    """(token, line number, snippet) for every backticked snippet anywhere in a Markdown file."""
    out = []
    for i, line in enumerate(text.splitlines(), 1):
        for snip in re.findall(r"`([^`\n]+)`", line):
            tok = ident_token(snip)
            if tok:
                out.append((tok, i, snip))
    return out


def is_module(ws, tok):
    """A token that names a module file (`CipherLean.Lib.DDT`, `Mathlib.Data.ZMod.Basic`): not a declaration."""
    rel = pathlib.Path(*tok.split(".")).with_suffix(".lean")
    return (ws / rel).exists() or (ws / ".lake" / "packages" / "mathlib" / rel).exists()


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("notation"); ap.add_argument("files", nargs="+"); ap.add_argument("--ws")
    ap.add_argument("--open", nargs="*", default=None, help="namespaces to open for #check (default: CipherLean and the slug)")
    ap.add_argument("--also", nargs="*", default=[], metavar="MD", help="more Markdown files to scan (README.md, CHAIN.md)")
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("--listing", metavar="FILE.json", help="use this inspect_lean.py listing instead of running Lean")
    a = ap.parse_args()
    ws = ck.find_workspace(a.ws)
    mods = [ck.module_name(ws, f) for f in a.files]
    slug = mods[0].split(".")[1] if mods[0].count(".") >= 2 else mods[0].split(".")[-1]
    opens = a.open if a.open is not None else ["CipherLean", slug]
    scratch_dir = ws / ".lake" / "inspect"; scratch_dir.mkdir(parents=True, exist_ok=True)
    if a.listing:
        lst = il.load(a.listing)
        if not lst.get("ok", True) or any(m not in lst.get("modules", []) for m in mods):
            ck.die(f"{a.listing} does not list {', '.join(mods)}")
    else:
        lst = il.listing(ws, a.files, timeout=a.timeout)
        if not lst["ok"]:
            ck.die(f"name listing failed (modules built?):\n{lst.get('output', '')[-2000:]}")
    names = {d["name"] for d in lst["declarations"]}
    shorts = {}
    for n in names:
        shorts.setdefault(n.split(".")[-1], set()).add(n)
    namespaces = {n.split(".")[0] for n in names if "." in n}

    # 1. NOTATION.md: every name is checked (library listing, then #check)
    cands = snippets(pathlib.Path(a.notation).read_text(encoding="utf-8"))
    seen, todo, known, modules = set(), [], {}, set()
    for tok, row, snip in cands:
        if tok in seen:
            continue
        seen.add(tok)
        full = [n for n in names if n == tok or n.endswith("." + tok)]
        if full:
            known[tok] = sorted(full)[0]
        elif is_module(ws, tok):
            modules.add(tok)
        else:
            todo.append(tok)
    # 2. --also files: qualified names must exist; short names resolve by their last component, by #check,
    #    or are listed
    also_known, also_unknown, also_short = {}, [], {}
    for md in a.also:
        text = pathlib.Path(md).read_text(encoding="utf-8")
        for tok, line, snip in also_snippets(text):
            if "." in tok and tok.split(".")[0] in namespaces:
                if tok in names:
                    also_known[tok] = tok
                elif is_module(ws, tok):
                    modules.add(tok)
                elif tok not in [t for _, t, _ in also_unknown]:
                    also_unknown.append((md, tok, line))
            elif "." not in tok:
                if tok in shorts:
                    also_known[tok] = sorted(shorts[tok])[0]
                elif "_" in tok and tok not in also_short:
                    also_short[tok] = f"{pathlib.Path(md).name}:{line}"
    unknown = []
    todo_short = [t for t in also_short if t not in todo and t not in known]
    if todo or todo_short:
        checks = "\n".join(f"#check @{tok}" for tok in todo + todo_short)
        s2 = scratch_dir / "notation_check.lean"
        s2.write_text(CHECK.format(imports="\n".join(f"import {m}" for m in mods), opens=" ".join(opens), checks=checks), encoding="utf-8")
        code, out = ck.run([ck.lake(), "env", "lean", str(s2)], cwd=str(ws), timeout=a.timeout)
        bad = set(re.findall(r"[Uu]nknown (?:identifier|constant) `?([^`'\s]+)", out))
        for tok in todo:
            if tok in bad or any(b.endswith("." + tok) or tok.endswith("." + b) for b in bad):
                unknown.append(tok)
            else:
                known[tok] = "(Mathlib / resolved by #check)"
        for tok in todo_short:
            if not (tok in bad or any(b.endswith("." + tok) or tok.endswith("." + b) for b in bad)):
                also_known[tok] = "(Mathlib / resolved by #check)"; also_short.pop(tok, None)
    for tok in list(also_short):
        if tok in known:
            also_known[tok] = known[tok]; also_short.pop(tok)

    print(f"# NOTATION names — `{a.notation}` against {', '.join(mods)} and CipherLean/Lib"
          + (f"; also {', '.join(pathlib.Path(m).name for m in a.also)}" if a.also else "") + "\n")
    print("| name | resolves to |\n|---|---|")
    for tok in sorted(known):
        print(f"| `{tok}` | `{known[tok]}` |")
    for tok in sorted(set(also_known) - set(known)):
        print(f"| `{tok}` | `{also_known[tok]}` (--also) |")
    for tok in unknown:
        rows = [row for t, row, _ in cands if t == tok]
        print(f"| `{tok}` | **UNKNOWN** (NOTATION row: {rows[0]}) |")
    for md, tok, line in also_unknown:
        print(f"| `{tok}` | **UNKNOWN** ({pathlib.Path(md).name}:{line}) |")
    if modules:
        print(f"\nModule names, not checked: " + ", ".join(f"`{m}`" for m in sorted(modules)))
    if also_short:
        print("\n## Short names in the --also files matching no declaration (prose, or stale? read them)\n")
        for tok, where in sorted(also_short.items()):
            print(f"- `{tok}` ({where})")
    n_unknown = len(unknown) + len(also_unknown)
    print(f"\nVERDICT: {'OK' if not n_unknown else 'UNKNOWN NAMES'} ({len(known) + len(set(also_known) - set(known))} resolved, {n_unknown} unknown"
          + (f", {len(also_short)} short names to read" if also_short else "") + ")")
    sys.exit(1 if n_unknown else 0)


if __name__ == "__main__":
    main()
