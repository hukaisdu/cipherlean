#!/usr/bin/env python3
"""chain_graph.py — draw the dependency graph of a proof chain (CHAIN.md) with TikZ, and keep a
mermaid copy inside CHAIN.md.  (step 3 of the skill: the graph is part of what the reader confirms)

Reads the `| id | kind | title | statement | uses | ... |` table of CHAIN.md, lays the nodes out in
layers (the target theorem on top, definitions and cited results at the bottom; a node sits one
layer below everything that uses it), writes CHAIN.tex (standalone TikZ) next to CHAIN.md, compiles
it with latexmk in a temporary directory unless --no-pdf (only CHAIN.tex and CHAIN.pdf stay next to
CHAIN.md), and rewrites the mermaid block between `<!-- chain-graph:begin -->` and
`<!-- chain-graph:end -->` in CHAIN.md.

Each node shows the row's id, its title, and (in gray) where it lives in the paper: the first
clause of the `where` column, cut at the first ";" — so write that column as "§7.3 Lemma 24
(lem:conjecture3-two-active); <longer notes>" and the graph shows the part before the ";".
The H1 line of CHAIN.md ("# CHAIN — <Slug>: ...") is printed above the graph as its title, so
it should name the paper the sections refer to.

The graph is the map of the formalization: the border of a node says what kind of row it is (thick blue the
target, dashed a proof step, double a cited result, dotted an assumption), its fill says where the row stands
(green proved, yellow stated with `sorry`, red pending, gray cited or assumed), and the legend counts the rows by
status. When CHAIN.md has a "## Roadmap" section (the end the user chose, the pieces with their route and size
in sessions; see assets/CHAIN-template.md), the legend also gives the pieces done and the size-weighted
progress — the same numbers `status.py` prints in its Position block.

A sub-chain, for confirming one piece of a theorem split into pieces (a 54-node chain is not readable
as one picture): `--focus <id>` draws the rows reachable from `<id>` through `uses` (`?`-edges included,
dashed as always; `--depth N` stops N edges away, so `--focus thm:5 --depth 1` is the target with its direct
premises), `--rows a,b,c` exactly those rows and the edges among them, `--gaps` only what remains to be
proved (every row that is not proved or cited, plus the rows of every unfinished piece of the roadmap).
The sub-chain is written to `CHAIN-<id>.tex` / `.pdf` (`CHAIN-gaps`, `CHAIN-rows`) next to CHAIN.md
(`--out <stem>` to choose the name) and CHAIN.md's mermaid block is left alone: it stays the whole chain.
`--per-row N` widens a layer (default 6 nodes per line).

usage: chain_graph.py CHAIN.md [--no-pdf] [--tex-only] [--focus <id> [--depth N] | --rows a,b,c | --gaps] [--out <stem>] [--per-row N]
"""
import argparse, pathlib, re, shutil, subprocess, sys, tempfile

KINDS = ["theorem", "lemma", "step", "def", "external", "assumption"]
STATUSES = ["proved", "stated", "pending", "cited", "assumed"]
# the border says what kind of row it is, the fill where the row stands
STYLE = {
    "theorem": "draw=blue!60!black, very thick, rounded corners",
    "lemma": "draw=blue!60!black, thick, rounded corners",
    "step": "draw, dashed, rounded corners",
    "def": "draw",
    "external": "draw, double",
    "assumption": "draw, dotted",
}
FILL = {"proved": "green!22", "stated": "yellow!35", "pending": "red!14", "cited": "gray!18", "assumed": "gray!18"}
MERMAID_STYLE = {
    "theorem": "stroke:#1f3a93,stroke-width:3px",
    "lemma": "stroke:#1f3a93,stroke-width:2px",
    "step": "stroke:#333,stroke-dasharray:4 3",
    "def": "stroke:#333",
    "external": "stroke:#333,stroke-width:3px",
    "assumption": "stroke:#333,stroke-dasharray:1 3",
}
MERMAID_FILL = {"proved": "#d4f0d4", "stated": "#fff3b0", "pending": "#f8d0d0", "cited": "#e6e6e6", "assumed": "#e6e6e6", "": "#ffffff"}


def parse_roadmap(text):
    """The "## Roadmap" section of CHAIN.md: {"end": str, "milestones": [str], "pieces": [row dicts]} or None.
    The section holds a line "End …: <the end the user chose>", optional "Milestone …: …" lines and the
    pieces table `| piece | rows | route | size | status | actual |` (assets/CHAIN-template.md)."""
    m = re.search(r"^## Roadmap.*?$", text, re.M)
    if not m:
        return None
    body = text[m.end():]
    nxt = re.search(r"^## ", body, re.M)
    body = body[:nxt.start()] if nxt else body
    rm = {"end": "", "milestones": [], "pieces": []}
    lines = body.splitlines()
    for i, l in enumerate(lines):
        if re.match(r"^\s*End\b[^:]*:", l):
            rm["end"] = l.split(":", 1)[1].strip()
        elif re.match(r"^\s*Milestone\b", l):
            rm["milestones"].append(l.strip())
        elif l.strip().startswith("| piece |"):
            header = [c.strip() for c in split_row(l)]
            for l2 in lines[i + 2:]:
                if not l2.strip().startswith("|"):
                    break
                cells = split_row(l2)
                cells += [""] * (len(header) - len(cells))
                r = dict(zip(header, cells))
                if r.get("piece", "").strip() and not r["piece"].strip().startswith("<"):
                    rm["pieces"].append(r)
    return rm


SESSIONS = re.compile(r"(\d+(?:\.\d+)?)(?:\s*[–-]\s*(\d+(?:\.\d+)?))?\s*sessions?")


def sessions_of(cell):
    """(low, high) sessions named in a size or actual cell ("6–8 sessions (…)", "1 session"), else None."""
    m = SESSIONS.search(cell or "")
    if not m:
        return None
    lo = float(m.group(1)); hi = float(m.group(2)) if m.group(2) else lo
    return lo, hi


def piece_rows(piece):
    return [r.strip("` ?") for r in re.split(r"[,\s]+", piece.get("rows", "")) if r.strip("` ?") and r.strip("` ") != "—"]


def is_work(piece):
    """A piece that costs sessions: route `prove …` or `port …` (not `assume by citation`, not `hypothesis`)."""
    return bool(re.match(r"\s*(prove|port)", piece.get("route", ""), re.I))


def is_done(piece):
    return bool(re.match(r"\s*done", piece.get("status", ""), re.I))


def position(nodes, roadmap):
    """The numbers of the Position block: rows by status, pieces done / planned, sessions done / total
    (actuals for the done pieces, estimates for the rest), the remaining pieces in order, the next piece,
    and the rows no piece lists. `nodes` is the dict of nodes_edges()."""
    by_status = {s: 0 for s in STATUSES}
    for n, info in nodes.items():
        by_status[info["status"] if info["status"] in by_status else "pending"] += 1
    pos = {"rows": by_status, "total_rows": len(nodes), "pieces": [], "done": [], "remaining": [], "next": None,
           "sessions_done": 0.0, "sessions_total_lo": 0.0, "sessions_total_hi": 0.0, "sessions_total_mid": 0.0,
           "unsized": [], "unassigned": [], "warnings": [], "end": "", "milestones": []}
    if not roadmap:
        return pos
    pos["end"], pos["milestones"] = roadmap["end"], roadmap["milestones"]
    listed = set()
    for p in roadmap["pieces"]:
        name = p["piece"].strip("` ")
        rows = piece_rows(p)
        listed.update(rows)
        est = sessions_of(p.get("size", "")); act = sessions_of(p.get("actual", ""))
        done = is_done(p); work = is_work(p)
        missing = [r for r in rows if r not in nodes]
        if missing:
            pos["warnings"].append(f"piece {name} names rows that are not in the table: {', '.join(missing)}")
        # a row of a piece to prove is settled when it is proved (a definition: once stated)
        unproved = [r for r in rows if r in nodes and not (nodes[r]["status"] == "proved"
                    or (nodes[r]["kind"] == "def" and nodes[r]["status"] == "stated"))]
        if work and done and unproved:
            pos["warnings"].append(f"piece {name} is marked done but its rows {', '.join(unproved)} are not proved")
        if work and not done and rows and not unproved:
            pos["warnings"].append(f"piece {name}: every row proved but the status cell says '{p.get('status', '').strip()}' (mark it done, with the actual size)")
        entry = {"piece": name, "rows": rows, "route": p.get("route", "").strip(), "size": p.get("size", "").strip(),
                 "status": p.get("status", "").strip(), "actual": p.get("actual", "").strip(), "est": est, "act": act,
                 "done": done, "work": work, "title": p.get("title", "").strip()}
        pos["pieces"].append(entry)
        if not work:
            continue
        if done:
            pos["done"].append(entry)
            s = act or est
            if s:
                pos["sessions_done"] += (s[0] + s[1]) / 2
                pos["sessions_total_lo"] += s[0]; pos["sessions_total_hi"] += s[1]; pos["sessions_total_mid"] += (s[0] + s[1]) / 2
            else:
                pos["unsized"].append(name)
        else:
            pos["remaining"].append(entry)
            if est:
                pos["sessions_total_lo"] += est[0]; pos["sessions_total_hi"] += est[1]; pos["sessions_total_mid"] += (est[0] + est[1]) / 2
            else:
                pos["unsized"].append(name)
    nxt = [e for e in pos["remaining"] if re.match(r"\s*(next|in progress|running)", e["status"], re.I)]
    pos["next"] = (nxt or pos["remaining"] or [None])[0]
    pos["unassigned"] = [n for n in nodes if n not in listed]
    return pos


def position_text(slug, pos, when=""):
    """The Position block, as status.py prints it and README's Roadmap section records it."""
    out = [f"## Position — {slug}" + (f" ({when})" if when else "")]
    if pos["end"]:
        out.append(f"- End: {pos['end']}")
        for m in pos["milestones"]:
            out.append(f"- {m}")
    else:
        out.append("- End: not chosen yet — CHAIN.md has no \"## Roadmap\" section (the sizing of the chain step writes it: "
                   "the end, the pieces, route and size per piece)")
    r = pos["rows"]
    out.append(f"- Rows: {r['proved']} proved · {r['stated']} stated · {r['pending']} pending · {r['cited']} cited · "
               f"{r['assumed']} assumed (of {pos['total_rows']})")
    if pos["pieces"]:
        work = [e for e in pos["pieces"] if e["work"]]
        done = ", ".join(e["piece"] for e in pos["done"]) or "none"
        pct = f"{100 * pos['sessions_done'] / pos['sessions_total_mid']:.0f} %" if pos["sessions_total_mid"] else "—"
        lo, hi = pos["sessions_total_lo"], pos["sessions_total_hi"]
        total = f"≈ {lo:g}" if lo == hi else f"≈ {lo:g}–{hi:g}"
        out.append(f"- Pieces: {len(pos['done'])} done of {len(work)} ({done}); sessions {pos['sessions_done']:g} of {total}"
                   f" (size-weighted progress {pct})" + (f"; no size on {', '.join(pos['unsized'])}" if pos["unsized"] else ""))
        if pos["remaining"]:
            out.append(f"- Remaining, in order ({len(pos['remaining'])} pieces):")
            for e in pos["remaining"]:
                size = e["size"].split("(")[0].strip() or "no size"
                out.append(f"  - {e['piece']}" + (f" {e['title']}" if e["title"] else "") + f" — {size}"
                           + (f"; {e['status']}" if e["status"] and not e["status"].startswith("planned") else ""))
            n = pos["next"]
            out.append(f"- Next: {n['piece']}" + (f" — {n['title']}" if n["title"] else "") + f"; route: {n['route']}; size: {n['size']}"
                       + (f"; status: {n['status']}" if n["status"] else ""))
        else:
            out.append("- Remaining: nothing — the end is reached" if pos["done"] else "- Remaining: no piece with a route `prove`/`port` in the table")
    if pos["unassigned"] and pos["pieces"]:
        out.append(f"- Rows on no piece: {', '.join(pos['unassigned'])}")
    for w in pos["warnings"]:
        out.append(f"- Check: {w}")
    return "\n".join(out)


def split_row(line):
    cells, cur, esc = [], "", False
    for ch in line.strip().strip("|"):
        if esc:
            cur += ch; esc = False
        elif ch == "\\":
            esc = True
        elif ch == "|":
            cells.append(cur.strip()); cur = ""
        else:
            cur += ch
    cells.append(cur.strip())
    return cells


def chain_title(text):
    """The H1 line of CHAIN.md without the leading '# ' (used as the figure title)."""
    for l in text.splitlines():
        if l.startswith("# "):
            return l[2:].strip()
    return ""


def where_short(w):
    """The part of a `where` cell shown in the graph: up to the first ';', at most 60 characters."""
    w = w.strip().strip("`")
    w = w.split(";")[0].strip()
    return (w[:57] + "...") if len(w) > 60 else w


def parse_chain(text):
    lines = text.splitlines()
    for i, l in enumerate(lines):
        if l.strip().startswith("| id |"):
            header = [c.strip() for c in split_row(l)]
            rows = []
            for l2 in lines[i + 2:]:
                if not l2.strip().startswith("|"):
                    break
                cells = split_row(l2)
                if len(cells) < len(header):
                    cells += [""] * (len(header) - len(cells))
                rows.append(dict(zip(header, cells)))
            return rows
    sys.exit("chain_graph: no table with header `| id | kind | title | statement | uses | ...` found")


def nodes_edges(rows):
    nodes = {}
    for r in rows:
        nid = r["id"].strip("`")
        if not nid or nid.startswith("<"):
            continue
        kind = r.get("kind", "").strip() or "step"
        if kind not in KINDS:
            print(f"chain_graph: unknown kind {kind!r} for {nid}, drawn as step", file=sys.stderr); kind = "step"
        nodes[nid] = {"kind": kind, "title": r.get("title", "").strip(), "status": r.get("status", "").strip(),
                      "where": where_short(r.get("where", ""))}
    edges = []
    for r in rows:
        nid = r["id"].strip("`")
        if nid not in nodes:
            continue
        for u in re.split(r"[,\s]+", r.get("uses", "")):
            u = u.strip("` ")
            if u and u != "—":
                optional = u.endswith("?")      # `id?`: the paper's route; Lean may prove it another way
                u = u.rstrip("?")
                if u not in nodes:
                    print(f"chain_graph: {nid} uses unknown id {u}", file=sys.stderr); continue
                edges.append((nid, u, optional))
    return nodes, edges


def layers(nodes, edges):
    users = {n: [] for n in nodes}
    for a, b, _ in edges:
        users[b].append(a)
    depth, state = {}, {}

    def d(n):
        if n in depth:
            return depth[n]
        if state.get(n) == 1:
            print(f"chain_graph: cycle through {n}", file=sys.stderr); return 0
        state[n] = 1
        depth[n] = 0 if not users[n] else 1 + max(d(u) for u in users[n])
        state[n] = 2
        return depth[n]
    for n in nodes:
        d(n)
    bottom = max(depth.values()) if depth else 0
    for n in nodes:
        if not users[n] and nodes[n]["kind"] in ("def", "external", "assumption"):
            depth[n] = bottom
    return depth


SYMBOLS = {"↦": r"$\mapsto$", "⊕": r"$\oplus$", "→": r"$\to$", "←": r"$\leftarrow$", "≤": r"$\le$",
           "≥": r"$\ge$", "≠": r"$\ne$", "∈": r"$\in$", "∉": r"$\notin$", "⊥": r"$\perp$", "Σ": r"$\Sigma$",
           "ᵀ": r"$^{\mathsf T}$", "·": r"$\cdot$", "×": r"$\times$", "∘": r"$\circ$", "⊆": r"$\subseteq$",
           "∀": r"$\forall$", "∃": r"$\exists$", "⁻¹": r"$^{-1}$", "₀": r"$_0$", "₁": r"$_1$", "₂": r"$_2$",
           "ι": r"$\iota$", "κ": r"$\kappa$", "φ": r"$\varphi$", "ψ": r"$\psi$", "Φ": r"$\Phi$", "θ": r"$\theta$",
           "λ": r"$\lambda$", "α": r"$\alpha$", "β": r"$\beta$", "δ": r"$\delta$", "ε": r"$\varepsilon$",
           "η": r"$\eta$", "μ": r"$\mu$", "χ": r"$\chi$", "Δ": r"$\Delta$", "∩": r"$\cap$", "∪": r"$\cup$",
           "ℓ": r"$\ell$", "₃": r"$_3$", "§": r"\S{}", "′": "'", "ʹ": "'", "−": "-", "…": r"\dots{}",
           "—": "--", "–": "--", "’": "'", "“": "``", "”": "''", "≈": r"$\approx$", "⇒": r"$\Rightarrow$",
           "⟨": r"$\langle$", "⟩": r"$\rangle$", "∑": r"$\sum$", "ℤ": r"$\mathbb{Z}$", "ℕ": r"$\mathbb{N}$"}


def tex_escape(s):
    """Escape LaTeX specials and replace the Unicode symbols pdflatex cannot typeset; any other
    non-ASCII character is dropped (titles should be short plain words)."""
    s = re.sub(r"([_&%#$^{}~])", lambda m: {"^": r"\^{}", "~": r"\~{}"}.get(m.group(1), "\\" + m.group(1)), s)
    for k, v in SYMBOLS.items():
        s = s.replace(k, v)
    s = s.replace("|", "$|$")
    # <, > and => print as inverted ?/! in text mode; use math mode
    s = s.replace("<=", "$\\le$").replace(">=", "$\\ge$").replace("=>", "$\\Rightarrow$")
    s = s.replace("<", "$<$").replace(">", "$>$")
    return "".join(ch if ord(ch) < 128 else "?" for ch in s)


def gap_rows(nodes, roadmap):
    """What remains: every row that is not proved or cited (a `def` counts as done once it is stated), plus
    the rows of every unfinished `prove`/`port` piece of the roadmap."""
    keep = set()
    for n, info in nodes.items():
        st, kind = info["status"], info["kind"]
        if kind == "assumption" or st == "proved" or (kind == "external" and st == "cited") or (kind == "def" and st == "stated"):
            continue
        keep.add(n)
    for p in (roadmap or {}).get("pieces", []):
        if is_work(p) and not is_done(p):
            keep.update(r for r in piece_rows(p) if r in nodes)
    return keep


def sub_chain(nodes, edges, focus=None, rows=None, depth=None):
    """The rows of a sub-chain: everything reachable from `focus` through `uses` (at most `depth` edges
    away when given), or exactly `rows`; with the edges among them."""
    if focus is not None:
        if focus not in nodes:
            sys.exit(f"chain_graph: --focus {focus}: no such id in the table")
        keep, stack = set(), [(focus, 0)]
        while stack:
            n, d = stack.pop()
            if n in keep:
                continue
            keep.add(n)
            if depth is None or d < depth:
                stack.extend((b, d + 1) for (a, b, _) in edges if a == n)
    else:
        keep = set()
        for r in rows:
            if r in nodes:
                keep.add(r)
            else:
                print(f"chain_graph: --rows: unknown id {r}, skipped", file=sys.stderr)
        if not keep:
            sys.exit("chain_graph: --rows named no row of the table")
    sub_nodes = {n: nodes[n] for n in nodes if n in keep}      # table order kept
    sub_edges = [(a, b, o) for (a, b, o) in edges if a in keep and b in keep]
    return sub_nodes, sub_edges


def tikz(nodes, edges, depth, title="", per_row=6, legend_extra=""):
    by_layer = {}
    for n in nodes:
        by_layer.setdefault(depth[n], []).append(n)
    order = {k: KINDS.index(k) for k in KINDS}
    out = [r"\documentclass[tikz,border=8pt]{standalone}", r"\usetikzlibrary{arrows.meta}",
           r"\begin{document}", r"\begin{tikzpicture}[>=Stealth, every node/.style={font=\scriptsize, align=center, text width=2.4cm, inner sep=3pt}]"]
    pos = {}
    y = 0.0
    for L in sorted(by_layer):
        ns = sorted(by_layer[L], key=lambda n: (order[nodes[n]["kind"]], n))
        rows = [ns[i:i + per_row] for i in range(0, len(ns), per_row)]
        for ri, row in enumerate(rows):
            width = (len(row) - 1) * 3.0
            for i, n in enumerate(row):
                x = i * 3.0 - width / 2 + (0.6 if ri % 2 else 0)
                pos[n] = (x, y - ri * 1.3)
                label = r"\texttt{" + tex_escape(n) + "}"
                if nodes[n]["title"]:
                    label += r"\\" + tex_escape(nodes[n]["title"])
                if nodes[n]["where"]:
                    label += r"\\{\tiny\color{gray!60!black} " + tex_escape(nodes[n]["where"]) + "}"
                fill = FILL.get(nodes[n]["status"], "white")
                out.append(f"\\node[{STYLE[nodes[n]['kind']]}, fill={fill}] ({tikz_id(n)}) at ({x:.2f},{pos[n][1]:.2f}) {{{label}}};")
        y -= 2.2 + 1.3 * (len(rows) - 1)
    for a, b, opt in edges:
        style = "->, gray!70!black, dashed" if opt else "->, gray!70!black"
        out.append(f"\\draw[{style}] ({tikz_id(a)}) -- ({tikz_id(b)});")
    # figure title (the H1 of CHAIN.md: names the paper the sections refer to)
    if title:
        tx = min(p[0] for p in pos.values()) - 1.2
        out.append(f"\\node[anchor=south west, font=\\small\\bfseries, text width=14cm, align=left] at ({tx:.2f},0.9) {{"
                   + tex_escape(title) + "};")
    # legend: border = kind, fill = status (with the counts), then the roadmap progress
    counts = {s: sum(1 for i in nodes.values() if i["status"] == s) for s in STATUSES}
    lx = max(p[0] for p in pos.values()) + 3.4
    out.append(f"\\node[anchor=north west, text width=3.6cm, font=\\scriptsize, align=left] at ({lx:.2f},0.6) {{"
               r"\textbf{Legend}\\ border: thick blue target, blue lemma, dashed proof step, plain definition, double cited result, dotted assumption\\ "
               r"fill: \colorbox{green!22}{proved " + str(counts["proved"]) + r"} \colorbox{yellow!35}{stated " + str(counts["stated"])
               + r"} \colorbox{red!14}{pending " + str(counts["pending"]) + r"} \colorbox{gray!18}{cited " + str(counts["cited"])
               + " / assumed " + str(counts["assumed"]) + r"}\\ gray line: where in the paper\\ arrow: uses; dashed: the paper's route, Lean may differ"
               + (r"\\ " + legend_extra if legend_extra else "") + "};")
    out += [r"\end{tikzpicture}", r"\end{document}"]
    return "\n".join(out) + "\n"


def tikz_id(n):
    return re.sub(r"[^A-Za-z0-9]", "", n) or "n"


def mermaid(nodes, edges):
    out = ["```mermaid", "graph TD"]
    for n, info in nodes.items():
        label = n + ("<br/>" + info["title"] if info["title"] else "") + ("<br/>" + info["where"] if info["where"] else "")
        out.append(f'  {tikz_id(n)}["{label}"]')
    for a, b, opt in edges:
        out.append(f"  {tikz_id(a)} {'-.->' if opt else '-->'} {tikz_id(b)}")
    for k, st in MERMAID_STYLE.items():
        for s, fill in MERMAID_FILL.items():
            members = [tikz_id(n) for n, i in nodes.items() if i["kind"] == k and (i["status"] if i["status"] in MERMAID_FILL else "") == s]
            if members:
                cls = k + ("_" + s if s else "")
                out.append(f"  classDef {cls} fill:{fill},{st}")
                out.append(f"  class {','.join(members)} {cls}")
    out.append("```")
    return "\n".join(out)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("chain")
    ap.add_argument("--no-pdf", action="store_true")
    ap.add_argument("--tex-only", action="store_true", help="do not touch CHAIN.md's mermaid block")
    ap.add_argument("--focus", metavar="ID", help="draw the sub-chain reachable from this id (CHAIN-<id>.tex/pdf)")
    ap.add_argument("--depth", type=int, metavar="N", help="with --focus: stop N edges away from the id")
    ap.add_argument("--rows", metavar="a,b,c", help="draw exactly these rows and the edges among them")
    ap.add_argument("--gaps", action="store_true", help="draw only what remains to be proved (CHAIN-gaps.tex/pdf)")
    ap.add_argument("--out", metavar="STEM", help="file stem of a sub-chain (default CHAIN-<id> or CHAIN-rows)")
    ap.add_argument("--per-row", type=int, default=6, metavar="N", help="nodes per line within a layer (default 6)")
    a = ap.parse_args()
    if sum(bool(x) for x in (a.focus, a.rows, a.gaps)) > 1:
        sys.exit("chain_graph: give one of --focus, --rows, --gaps")
    path = pathlib.Path(a.chain).resolve()
    text = path.read_text(encoding="utf-8")
    rows = parse_chain(text)
    nodes, edges = nodes_edges(rows)
    if not nodes:
        sys.exit("chain_graph: the table has no rows yet")
    title = chain_title(text)
    roadmap = parse_roadmap(text)
    pos = position(nodes, roadmap)
    legend_extra = ""
    if roadmap and pos["pieces"]:
        work = [e for e in pos["pieces"] if e["work"]]
        pct = f"{100 * pos['sessions_done'] / pos['sessions_total_mid']:.0f}\\%" if pos["sessions_total_mid"] else "?"
        legend_extra = (r"\textbf{Progress}: pieces " + f"{len(pos['done'])}/{len(work)} done, sessions {pos['sessions_done']:g} of "
                        + tex_escape(f"≈ {pos['sessions_total_lo']:g}–{pos['sessions_total_hi']:g}") + f" ({pct}); next: "
                        + (tex_escape(pos["next"]["piece"]) if pos["next"] else "none"))
    stem = "CHAIN"
    if a.focus or a.rows or a.gaps:
        if a.gaps:
            keep = gap_rows(nodes, roadmap)
            if not keep:
                sys.exit("chain_graph: --gaps: nothing remains (every row proved or cited)")
            nodes, edges = sub_chain(nodes, edges, rows=sorted(keep, key=list(nodes).index))
            stem, title = "CHAIN-gaps", f"{title} — the remaining gaps ({len(nodes)} rows)"
        else:
            nodes, edges = sub_chain(nodes, edges, focus=a.focus, rows=[r.strip("` ") for r in (a.rows or "").split(",") if r.strip("` ")],
                                     depth=a.depth)
        if a.focus:
            stem = "CHAIN-" + re.sub(r"[^A-Za-z0-9]+", "-", a.focus).strip("-")
            title = f"{title} — sub-chain from {a.focus}" + (f" (depth {a.depth})" if a.depth is not None else "")
        elif a.rows:
            stem, title = "CHAIN-rows", f"{title} — rows {', '.join(nodes)}"
        if a.out:
            stem = a.out
    depth = layers(nodes, edges)
    tex = path.with_name(stem + ".tex")
    tex.write_text(tikz(nodes, edges, depth, title, per_row=a.per_row, legend_extra=legend_extra), encoding="utf-8")
    print(f"{len(nodes)} nodes, {len(edges)} edges, {max(depth.values()) + 1} layers -> {tex}")
    if a.focus or a.rows or a.gaps:
        print(f"sub-chain: CHAIN.md's mermaid block untouched (it stays the whole chain)")
    elif not a.tex_only:
        mm = mermaid(nodes, edges)
        if "<!-- chain-graph:begin -->" in text:
            text = re.sub(r"<!-- chain-graph:begin -->.*?<!-- chain-graph:end -->",
                          "<!-- chain-graph:begin -->\n" + mm + "\n<!-- chain-graph:end -->", text, flags=re.S)
        else:
            text += "\n## Dependency graph\n\n<!-- chain-graph:begin -->\n" + mm + "\n<!-- chain-graph:end -->\n"
        path.write_text(text, encoding="utf-8")
        print(f"mermaid block updated in {path.name}")
    if not a.no_pdf:
        lm = shutil.which("latexmk")
        if not lm:
            print("latexmk not found; CHAIN.tex written, PDF not compiled", file=sys.stderr); return
        pdf = tex.with_suffix(".pdf")
        with tempfile.TemporaryDirectory(prefix="chain_graph_") as td:      # no .aux/.log/.fls litter next to CHAIN.md
            shutil.copy(tex, td)
            p = subprocess.run([lm, "-pdf", "-interaction=nonstopmode", "-halt-on-error", tex.name],
                               cwd=td, capture_output=True, text=True)
            if p.returncode == 0:
                shutil.copy(pathlib.Path(td) / pdf.name, pdf)
                print(f"compiled {pdf}")
            else:
                print(p.stdout[-1500:], file=sys.stderr); sys.exit("chain_graph: latexmk failed")


if __name__ == "__main__":
    main()
