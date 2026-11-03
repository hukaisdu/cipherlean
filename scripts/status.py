#!/usr/bin/env python3
"""status.py — the status board of one formalization directory, for the reader who was not watching.

usage: status.py <Slug> [--ws DIR] [--check] [--position] [--json]

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

`--json` prints the same board as one JSON object instead (with --check: the verdicts too), plus what the project
page needs: every chain row with its columns, piece and the file that declares its Lean name, the roadmap pieces
with their session, start and end, the REVIEW rounds with the piece each one covered, and the text of the questions
for the reader. `project_page.py` turns it into PROJECT.html.
"""
import argparse, datetime, json, os, pathlib, re, subprocess, sys
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

DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*"
                  r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque)\s+([^\s:({\[]+)", re.M)

def decl_files(d, ws):
    """Last component of every declared name → the file that declares it: the paper's .lean files first,
    then the shared library (shown as `Lib/<path>`)."""
    where = {}
    lib = ws / "CipherLean" / "Lib"
    files = [(f, f.name) for f in sorted(d.glob("*.lean"))]
    if lib.is_dir():
        files += [(f, "Lib/" + str(f.relative_to(lib))) for f in sorted(lib.rglob("*.lean"))]
    for f, shown in files:
        for m in DECL.finditer(f.read_text(encoding="utf-8", errors="replace")):
            where.setdefault(m.group(1).split(".")[-1], shown)
    return where

def run_checks(d, ws, slug, leans, chain):
    """The --check verdicts: one Lean listing, check_lean per file, chain_check once over all the pieces."""
    skill = pathlib.Path(__file__).resolve().parent
    def is_template(f):
        s = f.read_text(encoding="utf-8", errors="replace")
        return "<Slug>" in s or "theorem main : True" in s     # the untouched Main.lean of new_paper.sh
    files = [f for f in leans if not is_template(f)]
    res = {"when": datetime.datetime.now().strftime("%Y-%m-%d %H:%M"), "listing_ok": True, "listing": "", "files": [], "chain": None}
    listing = ws / ".lake" / "inspect" / f"status_{slug.replace('/', '_')}.json"
    listing.parent.mkdir(parents=True, exist_ok=True)
    # one `lake env lean` run over all the pieces (inspect_lean.py); check_lean and chain_check then read it
    p = subprocess.run([sys.executable, str(skill / "inspect_lean.py"), *[str(f) for f in files], "--ws", str(ws), "--out", str(listing)],
                       cwd=ws, capture_output=True, text=True)
    if p.returncode != 0:
        res["listing_ok"], res["listing"] = False, (p.stderr or p.stdout).strip()[-600:]
    else:
        res["listing"] = p.stdout.strip()
    for f in files:
        out = subprocess.run([sys.executable, str(skill / "check_lean.py"), str(f.relative_to(ws)), "--ws", str(ws), "--no-build", "--listing", str(listing)],
                             cwd=ws, capture_output=True, text=True).stdout
        v = re.findall(r"^VERDICT: .*", out, re.M); n = re.findall(r"^declarations: (.*)", out, re.M)
        res["files"].append({"file": f.name, "verdict": v[-1] if v else "", "declarations": n[-1] if n else ""})
    if chain.exists() and files:
        # one run over all the pieces: chain_check treats every file given as the paper module
        out = subprocess.run([sys.executable, str(skill / "chain_check.py"), str(chain), *[str(f) for f in files], "--ws", str(ws), "--listing", str(listing)],
                             cwd=ws, capture_output=True, text=True).stdout
        v = re.findall(r"^VERDICT: .*", out, re.M)
        res["chain"] = {"files": [f.name for f in files], "verdict": v[-1] if v else ""}
    return res

def collect(slug, ws, check=False):
    """Everything the board shows, as one dict: the --json output and the input of project_page.py."""
    ws = pathlib.Path(ws); d = ws / "CipherLean" / slug
    if not d.is_dir():
        sys.exit(f"status: {d} does not exist")
    chain = d / "CHAIN.md"
    when = datetime.datetime.now().strftime("%Y-%m-%d %H:%M")
    data = {"slug": slug, "dir": str(d), "when": when, "title": "", "position": None, "position_text": "", "rows": [],
            "edges": [], "lean_files": [], "chain_counts": None, "proved": [], "questions": None, "readme_status": [],
            "review": None, "promote": [], "checks": None}
    nodes, edges = {}, []
    if chain.exists():
        text = chain.read_text(encoding="utf-8")
        data["title"] = cg.chain_title(text)
        try:
            raw = cg.parse_chain(text)
            nodes, edges = cg.nodes_edges(raw)
        except SystemExit:
            raw, nodes = [], {}
        roadmap = cg.parse_roadmap(text)
        pos = cg.position(nodes, roadmap)
        data["position"] = pos
        data["position_text"] = cg.position_text(slug, pos, when)
        piece_of = {}
        for p in pos["pieces"]:
            for r in p["rows"]:
                piece_of.setdefault(r, p["piece"])
        gaps = cg.gap_rows(nodes, roadmap)
        files = decl_files(d, ws)
        for r in raw:
            nid = r.get("id", "").strip("`")
            if nid not in nodes:
                continue
            lean = [t.split(".")[-1] for t in re.findall(r"[A-Za-z_][\w.'₀-₉!?]*", r.get("lean", ""))]
            data["rows"].append({**{k: v.strip() for k, v in r.items()}, "id": nid, "kind": nodes[nid]["kind"],
                                 "where_short": nodes[nid]["where"], "piece": piece_of.get(nid, ""), "gap": nid in gaps,
                                 "files": sorted({files[t] for t in lean if t in files})})
        data["edges"] = [{"from": a, "to": b, "optional": o} for a, b, o in edges]
        crow = table_rows(text, "| id |")
        counts = {}
        for r in crow:
            if len(r) >= 9 and not r[0].startswith("<"):
                counts[r[8]] = counts.get(r[8], 0) + 1
        data["chain_counts"] = dict(sorted(counts.items()))
        data["proved"] = [r[0] for r in crow if len(r) >= 9 and r[8] == "proved"]
        q = re.search(r"## Questions for the reader\n(.*?)\n## ", text, re.S)
        if q:
            data["questions"] = {"count": len(re.findall(r"^\s*\d+\.", q.group(1), re.M)), "text": q.group(1).strip()}
    else:
        data["position_text"] = f"## Position — {slug} ({when})\n- no CHAIN.md yet: nothing is sized, nothing is proved"
    for f in sorted(d.glob("*.lean")):
        t = f.read_text(encoding="utf-8", errors="replace")
        data["lean_files"].append({"file": f.name, "lines": len(t.splitlines()),
                                   "decls": len(re.findall(r"^(?:theorem|lemma|def|abbrev|instance|structure)\s", t, re.M)),
                                   "sorry": len(re.findall(r"\bsorry\b", t)), "native_decide": len(re.findall(r"\bnative_decide\b", t)),
                                   "template": "<Slug>" in t or "theorem main : True" in t})
    readme = d / "README.md"
    if readme.exists():
        data["readme_status"] = table_rows(readme.read_text(encoding="utf-8"), "| paper label |")
    review = d / "REVIEW.md"
    if review.exists():
        t = review.read_text(encoding="utf-8")
        heads = list(re.finditer(r"^## Round (\d+) — (reviewer|formalizer)(?: \(([^)]*)\))?", t, re.M))
        rounds = []
        for i, m in enumerate(heads):
            body = t[m.end():heads[i + 1].start() if i + 1 < len(heads) else len(t)]
            body = body[:re.search(r"^## ", body, re.M).start()] if re.search(r"^## ", body, re.M) else body
            sc = re.search(r"[Ss]cope[^:\n]*:\s*piece (\w+)", body[:600])
            v = re.findall(r"^VERDICT: (\w+)", body, re.M)
            rounds.append({"round": int(m.group(1)), "role": m.group(2), "date": m.group(3) or "",
                           "piece": sc.group(1) if sc else "", "verdict": v[-1] if v else ""})
        # a formalizer round answers the reviewer round of the same number: it covers the same piece
        for r in rounds:
            if not r["piece"]:
                r["piece"] = next((x["piece"] for x in rounds if x["round"] == r["round"] and x["piece"]), "")
        obj = re.findall(r"^\| (R\d+\.\d+) \| (BLOCKER|MAJOR|MINOR) \|", t, re.M)
        answered = {i for i, _ in re.findall(r"^\| (R\d+\.\d+) \| (fixed|rejected|needs the user)", t, re.M)}
        verdicts = re.findall(r"^VERDICT: (\w+)", t, re.M)
        data["review"] = {"rounds": rounds, "heads": [(m.group(1), m.group(2)) for m in heads],
                          "last_verdict": verdicts[-1] if verdicts else "",
                          "open": [f"{i} ({s})" for i, s in obj if i not in answered]}
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
        data["promote"].append({"file": pf.name, "parts": parts})
    if check:
        data["checks"] = run_checks(d, ws, slug, sorted(d.glob("*.lean")), chain)
    return data

def print_checks(res):
    print("\n## Live checks")
    if not res["listing_ok"]:
        print(f"- listing failed (build the files first): {res['listing']}")
    else:
        print(f"- listing: {res['listing']}")
    for f in res["files"]:
        print(f"- check_lean {f['file']}: {f['verdict'] or 'no verdict (build it first)'}" + (f"; {f['declarations']}" if f["declarations"] else ""))
    if res["chain"]:
        print(f"- chain_check {', '.join(res['chain']['files'])}: {res['chain']['verdict'] or 'no verdict'}")

def print_board(data):
    print(f"# Status — {data['slug']} ({data['dir']})\n")
    print(data["position_text"] + "\n")
    print("## Lean files")
    for f in data["lean_files"]:
        tag = "template, untouched" if f["template"] else ""
        print(f"- `{f['file']}`: {f['lines']} lines, {f['decls']} source declarations, sorry {f['sorry']}, native_decide {f['native_decide']} {tag}".rstrip())
    if data["chain_counts"] is not None:
        c = data["chain_counts"]
        print("\n## CHAIN.md: " + ", ".join(f"{k} {v}" for k, v in c.items()) + f" (of {sum(c.values())} rows)")
        if data["proved"]: print("- proved: " + ", ".join(data["proved"]))
        if data["questions"]:
            print(f"- questions for the reader: {data['questions']['count']} (CHAIN.md, section \"Questions for the reader\")")
    if data["readme_status"]:
        print("\n## README status table")
        for r in data["readme_status"]:
            if len(r) >= 3: print(f"- {r[0]}: {r[2]}")
    rv = data["review"]
    if rv:
        print(f"\n## REVIEW.md: rounds {', '.join(f'{n} {w}' for n, w in rv['heads']) or 'none'}; last verdict {rv['last_verdict'] or 'none'}")
        print("- objections without a formalizer answer: " + (", ".join(rv["open"]) if rv["open"] else "none"))
    for p in data["promote"]:
        print(f"\n## {p['file']}: " + ("; ".join(p["parts"]) if p["parts"] else "present"))

def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("slug"); ap.add_argument("--ws", default=os.environ.get("CIPHERLEAN_WS", str(pathlib.Path.home() / "cipherlean")))
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--position", action="store_true", help="print only the Position block")
    ap.add_argument("--json", action="store_true", help="print the board as one JSON object (the input of project_page.py)")
    a = ap.parse_args()
    if a.json:
        print(json.dumps(collect(a.slug, a.ws, check=a.check), ensure_ascii=False, indent=1)); return
    data = collect(a.slug, a.ws)
    if a.position:
        print(data["position_text"]); return
    print_board(data)
    if a.check:     # the board first, so the reader has it while the Lean listing runs
        ws = pathlib.Path(a.ws); d = ws / "CipherLean" / a.slug
        print_checks(run_checks(d, ws, a.slug, sorted(d.glob("*.lean")), d / "CHAIN.md"))

if __name__ == "__main__":
    main()
