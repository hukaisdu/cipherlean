#!/usr/bin/env python3
"""status.py — the status board of one formalization directory, for the reader who was not watching.

usage: status.py <Slug> [--ws DIR] [--check]

Prints, from the files alone (no Lean run unless --check): every .lean file with its line and `sorry`
counts; CHAIN.md rows by status (pending / stated / proved / cited / assumed) and the open questions for
the reader; the README status table; REVIEW.md rounds, the last verdict and the objections still without
a formalizer answer; PROMOTE.md if present. With --check it also runs check_lean.py (--no-build) and
chain_check.py once over all the .lean files (the pieces) and prints their verdict lines. Run it at the end of every step and
paste the board into the chat, and say on which machine a long job is running.
"""
import argparse, os, pathlib, re, subprocess, sys

def table_rows(text, header_start):
    rows = []
    lines = text.splitlines()
    for i, l in enumerate(lines):
        if l.strip().startswith(header_start):
            for l2 in lines[i + 2:]:
                if not l2.strip().startswith("|"):
                    break
                rows.append([c.strip() for c in l2.strip().strip("|").split("|")])
            break
    return rows

def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("slug"); ap.add_argument("--ws", default=os.environ.get("CIPHERLEAN_WS", str(pathlib.Path.home() / "cipherlean")))
    ap.add_argument("--check", action="store_true")
    a = ap.parse_args()
    ws = pathlib.Path(a.ws); d = ws / "CipherLean" / a.slug
    if not d.is_dir():
        sys.exit(f"status: {d} does not exist")
    print(f"# Status — {a.slug} ({d})\n")
    leans = sorted(d.glob("*.lean"))
    print("## Lean files")
    for f in leans:
        t = f.read_text(encoding="utf-8", errors="replace")
        n_sorry = len(re.findall(r"\bsorry\b", t)); n_native = len(re.findall(r"\bnative_decide\b", t))
        decls = len(re.findall(r"^(?:theorem|lemma|def|abbrev|instance|structure)\s", t, re.M))
        tag = "template, untouched" if "<Slug>" in t or "theorem main : True" in t else ""
        print(f"- `{f.name}`: {len(t.splitlines())} lines, {decls} declarations, sorry {n_sorry}, native_decide {n_native} {tag}".rstrip())
    chain = d / "CHAIN.md"
    if chain.exists():
        rows = table_rows(chain.read_text(encoding="utf-8"), "| id |")
        counts = {}
        for r in rows:
            if len(r) >= 9 and not r[0].startswith("<"):
                counts[r[8]] = counts.get(r[8], 0) + 1
        print("\n## CHAIN.md: " + ", ".join(f"{k} {v}" for k, v in sorted(counts.items())) + f" (of {sum(counts.values())} rows)")
        proved = [r[0] for r in rows if len(r) >= 9 and r[8] == "proved"]
        if proved: print("- proved: " + ", ".join(proved))
        q = re.search(r"## Questions for the reader\n(.*?)\n## ", chain.read_text(encoding="utf-8"), re.S)
        if q:
            nq = len(re.findall(r"^\s*\d+\.", q.group(1), re.M))
            print(f"- questions for the reader: {nq} (CHAIN.md, section \"Questions for the reader\")")
    readme = d / "README.md"
    if readme.exists():
        rows = table_rows(readme.read_text(encoding="utf-8"), "| paper label |")
        if rows:
            print("\n## README status table")
            for r in rows:
                if len(r) >= 3: print(f"- {r[0]}: {r[2]}")
    review = d / "REVIEW.md"
    if review.exists():
        t = review.read_text(encoding="utf-8")
        rounds = re.findall(r"^## Round (\d+) — (reviewer|formalizer)", t, re.M)
        verdicts = re.findall(r"^VERDICT: (\w+)", t, re.M)
        print(f"\n## REVIEW.md: rounds {', '.join(f'{n} {w}' for n, w in rounds) or 'none'}; last verdict {verdicts[-1] if verdicts else 'none'}")
        obj = re.findall(r"^\| (R\d+\.\d+) \| (BLOCKER|MAJOR|MINOR) \|", t, re.M)
        ans = re.findall(r"^\| (R\d+\.\d+) \| (fixed|rejected|needs the user)", t, re.M)
        answered = {i for i, _ in ans}
        open_ = [f"{i} ({s})" for i, s in obj if i not in answered]
        print("- objections without a formalizer answer: " + (", ".join(open_) if open_ else "none"))
    if (d / "PROMOTE.md").exists():
        m = re.search(r"Counts: (.*)", (d / "PROMOTE.md").read_text(encoding="utf-8"))
        print(f"\n## PROMOTE.md: {m.group(1) if m else 'present'}")
    if a.check:
        skill = pathlib.Path(__file__).resolve().parent
        print("\n## Live checks")
        files = [f for f in leans if "<Slug>" not in f.read_text(encoding="utf-8", errors="replace")]
        for f in files:
            out = subprocess.run([sys.executable, str(skill / "check_lean.py"), str(f.relative_to(ws)), "--no-build"], cwd=ws, capture_output=True, text=True).stdout
            v = re.findall(r"^VERDICT: .*", out, re.M); print(f"- check_lean {f.name}: {v[-1] if v else 'no verdict (build it first)'}")
        if chain.exists() and files:
            # one run over all the pieces: chain_check treats every file given as the paper module
            out = subprocess.run([sys.executable, str(skill / "chain_check.py"), str(chain), *[str(f) for f in files]], cwd=ws, capture_output=True, text=True).stdout
            v = re.findall(r"^VERDICT: .*", out, re.M); print(f"- chain_check {', '.join(f.name for f in files)}: {v[-1] if v else 'no verdict'}")

if __name__ == "__main__":
    main()
