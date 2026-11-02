#!/usr/bin/env python3
"""status.py — the status board of one formalization directory, for the reader who was not watching.

usage: status.py <Slug> [--ws DIR] [--check] [--position]

Prints first the Position block — where the whole theorem stands: the end the user chose and its milestones
(the "## Roadmap" section of CHAIN.md), the rows by status, the pieces done of those planned with the
size-weighted progress in sessions (actual sizes for the done pieces, estimates for the rest), the remaining
pieces in order with their estimates, the next piece, and any row no piece lists or piece whose status cell
disagrees with its rows. `--position` prints only that block (paste it into README's Roadmap section at every
stop). Then, from the files alone (no Lean run unless --check): every .lean file with its line, source
declaration and `sorry` counts (source declarations = `theorem/lemma/def/...` lines; check_lean.py counts
the module's environment, which adds the auxiliary lemmas Lean generates, so its number can be larger);
CHAIN.md rows by status and the open questions for the reader; the README status table; REVIEW.md rounds,
the last verdict and the objections still without a formalizer answer; every classification table of
PROMOTE.md (every run's table). With --check it runs one Lean listing (inspect_lean.py) over all the .lean files (the
pieces), then check_lean.py (--no-build) per file and chain_check.py once, offline on that listing, and prints their
verdict lines with the declaration counts. Run it at the end of every
step and at every stop, paste the board into the chat, and say on which machine a long job is running.
"""
import argparse, datetime, os, pathlib, re, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import chain_graph as cg  # noqa: E402  (parse_chain, nodes_edges, parse_roadmap, position, position_text)

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
    ap.add_argument("--position", action="store_true", help="print only the Position block")
    a = ap.parse_args()
    ws = pathlib.Path(a.ws); d = ws / "CipherLean" / a.slug
    if not d.is_dir():
        sys.exit(f"status: {d} does not exist")
    chain = d / "CHAIN.md"
    when = datetime.datetime.now().strftime("%Y-%m-%d %H:%M")
    if chain.exists():
        text = chain.read_text(encoding="utf-8")
        try:
            nodes, _ = cg.nodes_edges(cg.parse_chain(text))
        except SystemExit:
            nodes = {}
        block = cg.position_text(a.slug, cg.position(nodes, cg.parse_roadmap(text)), when)
    else:
        block = f"## Position — {a.slug} ({when})\n- no CHAIN.md yet: nothing is sized, nothing is proved"
    if a.position:
        print(block); return
    print(f"# Status — {a.slug} ({d})\n")
    print(block + "\n")
    leans = sorted(d.glob("*.lean"))
    print("## Lean files")
    for f in leans:
        t = f.read_text(encoding="utf-8", errors="replace")
        n_sorry = len(re.findall(r"\bsorry\b", t)); n_native = len(re.findall(r"\bnative_decide\b", t))
        decls = len(re.findall(r"^(?:theorem|lemma|def|abbrev|instance|structure)\s", t, re.M))
        tag = "template, untouched" if "<Slug>" in t or "theorem main : True" in t else ""
        print(f"- `{f.name}`: {len(t.splitlines())} lines, {decls} source declarations, sorry {n_sorry}, native_decide {n_native} {tag}".rstrip())
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
    for pf in sorted(d.glob("PROMOTE*.md")):
        # one classification table per module and run: each heading "### Candidates — `Module`" (older
        # files: "# Promotion candidates — `Module`") with the "Counts: ..." line that follows it
        t = pf.read_text(encoding="utf-8")
        heads = [(m.group(1), m.start()) for m in re.finditer(r"^#+ (?:Promotion candidates|Candidates) — `([^`]+)`", t, re.M)]
        parts = []
        for i, (mod, start) in enumerate(heads):
            end = heads[i + 1][1] if i + 1 < len(heads) else len(t)
            c = re.search(r"[Cc]ounts: ([^.)]*)", t[start:end])     # the script's line, or a hand-written "(counts: A 9, ...)"
            parts.append(f"`{mod.split('.')[-1]}` {' '.join(c.group(1).split()) if c else '(no counts line)'}")
        print(f"\n## {pf.name}: " + ("; ".join(parts) if parts else "present"))
    if a.check:
        skill = pathlib.Path(__file__).resolve().parent
        print("\n## Live checks")
        def is_template(f):
            s = f.read_text(encoding="utf-8", errors="replace")
            return "<Slug>" in s or "theorem main : True" in s     # the untouched Main.lean of new_paper.sh
        files = [f for f in leans if not is_template(f)]
        listing = ws / ".lake" / "inspect" / f"status_{a.slug.replace('/', '_')}.json"
        listing.parent.mkdir(parents=True, exist_ok=True)
        # one `lake env lean` run over all the pieces (inspect_lean.py); check_lean and chain_check then read it
        p = subprocess.run([sys.executable, str(skill / "inspect_lean.py"), *[str(f) for f in files], "--ws", str(ws), "--out", str(listing)],
                           cwd=ws, capture_output=True, text=True)
        if p.returncode != 0:
            print(f"- listing failed (build the files first): {(p.stderr or p.stdout).strip()[-600:]}")
        else:
            print(f"- listing: {p.stdout.strip()}")
        for f in files:
            out = subprocess.run([sys.executable, str(skill / "check_lean.py"), str(f.relative_to(ws)), "--ws", str(ws), "--no-build", "--listing", str(listing)],
                                 cwd=ws, capture_output=True, text=True).stdout
            v = re.findall(r"^VERDICT: .*", out, re.M); n = re.findall(r"^declarations: (.*)", out, re.M)
            print(f"- check_lean {f.name}: {v[-1] if v else 'no verdict (build it first)'}" + (f"; {n[-1]}" if n else ""))
        if chain.exists() and files:
            # one run over all the pieces: chain_check treats every file given as the paper module
            out = subprocess.run([sys.executable, str(skill / "chain_check.py"), str(chain), *[str(f) for f in files], "--ws", str(ws), "--listing", str(listing)],
                                 cwd=ws, capture_output=True, text=True).stdout
            v = re.findall(r"^VERDICT: .*", out, re.M); print(f"- chain_check {', '.join(f.name for f in files)}: {v[-1] if v else 'no verdict'}")

if __name__ == "__main__":
    main()
