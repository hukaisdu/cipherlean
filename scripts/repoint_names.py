#!/usr/bin/env python3
"""repoint_names.py — after a promotion (step 7b), re-point the moved names in the paper directory's
Markdown files from `<Slug>.name` to `CipherLean.name` (and `old` to `new` when the move renamed it).

Why: every promotion so far re-pointed by hand the `lean` cells of CHAIN.md, the Lean-name column of
NOTATION.md, the status table and the Departures of README.md, PROMOTE.md's Done section, a REVIEW.md note
(about forty places for piece C of WHConj3, one of them a rename), and `chain_check.py` / `notation_check.py`
only report the stale ones after the move. This script lists them before the move and rewrites them after.

Without --apply it lists every occurrence of each name (qualified `<from>.name` anywhere; the bare `name`
as a whole word inside backticks), per file and line, in the directory's *.md files, with --lib also in
`CipherLean/Lib/NOTATION.md` and `CipherLean/Lib/README.md`; .lean files are listed for information only (the
Lean side of the move is done by hand and the build reports what is left). With --apply it rewrites the
Markdown files: `<from>.name` → `<to>.new` everywhere, and the bare backticked `name` → `new` when renamed.

usage: repoint_names.py CipherLean/<Slug>/ <name>[=<new>] ... [--from NS] [--to NS] [--lib] [--apply] [--ws DIR]
  <name>=<new>   the declaration was renamed on the way (bias_eq_iff=sum_chi_deriv_eq_iff_mem_constMasks)
  --from NS      the paper's namespace (default: the directory name, the Slug)
  --to NS        the library's namespace (default: CipherLean)
"""
import argparse, os, pathlib, re, sys


def occurrences(text, qualified, bare):
    """Line numbers where `qualified` occurs, and where `bare` occurs as a whole word inside backticks."""
    hits = []
    for i, line in enumerate(text.splitlines(), 1):
        if qualified in line:
            hits.append((i, "qualified", line.strip()))
        elif any(re.search(rf"(?<![\w.']){re.escape(bare)}(?![\w'])", snip) for snip in re.findall(r"`([^`\n]+)`", line)):
            hits.append((i, "bare", line.strip()))
    return hits


def rewrite(text, qualified, new_qualified, bare, new_bare):
    text = text.replace(qualified, new_qualified)
    if new_bare != bare:
        def fix(m):
            return "`" + re.sub(rf"(?<![\w.']){re.escape(bare)}(?![\w'])", new_bare, m.group(1)) + "`"
        text = re.sub(r"`([^`\n]+)`", fix, text)
    return text


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("directory"); ap.add_argument("names", nargs="+", metavar="name[=new]")
    ap.add_argument("--from", dest="src", help="paper namespace (default: the directory name)")
    ap.add_argument("--to", dest="dst", default="CipherLean")
    ap.add_argument("--lib", action="store_true", help="also CipherLean/Lib/NOTATION.md and README.md")
    ap.add_argument("--apply", action="store_true")
    ap.add_argument("--ws", default=os.environ.get("CIPHERLEAN_WS", str(pathlib.Path.home() / "cipherlean")))
    a = ap.parse_args()
    d = pathlib.Path(a.directory).resolve()
    if not d.is_dir():
        sys.exit(f"repoint_names: {d} is not a directory")
    src = a.src or d.name
    files = sorted(d.glob("*.md")) + sorted(d.glob("*.lean"))
    if a.lib:
        lib = pathlib.Path(a.ws) / "CipherLean" / "Lib"
        files += [lib / "NOTATION.md", lib / "README.md"]
    pairs = []
    for spec in a.names:
        old, _, new = spec.partition("=")
        pairs.append((old.strip(), (new or old).strip()))
    total, changed = 0, []
    for f in files:
        if not f.exists():
            continue
        text = f.read_text(encoding="utf-8")
        new_text = text
        for old, new in pairs:
            q, nq = f"{src}.{old}", f"{a.dst}.{new}"
            hits = occurrences(text, q, old)
            if hits:
                print(f"## {f.relative_to(pathlib.Path(a.ws)) if str(f).startswith(a.ws) else f}: `{old}`"
                      + (f" → `{new}`" if new != old else "") + f" ({len(hits)})")
                for i, kind, line in hits:
                    print(f"- L{i} [{kind}] {line[:160]}")
                total += len(hits)
            if f.suffix == ".md":
                new_text = rewrite(new_text, q, nq, old, new)
        if a.apply and f.suffix == ".md" and new_text != text:
            f.write_text(new_text, encoding="utf-8"); changed.append(f.name)
    print(f"\n{total} occurrence(s) of {len(pairs)} name(s) under {d}"
          + (f"; rewritten: {', '.join(changed)}" if a.apply else "; dry run (add --apply to rewrite the .md files; .lean files are never touched)"))
    if a.apply:
        print("next: chain_check.py, notation_check.py --also README.md CHAIN.md, and a read of the lines above")


if __name__ == "__main__":
    main()
