#!/usr/bin/env python3
"""chain_graph.py — draw the dependency graph of a proof chain (CHAIN.md) with TikZ, and keep a
mermaid copy inside CHAIN.md.  (step 1b of the skill: the graph is part of what the reader confirms)

Reads the `| id | kind | title | statement | uses | ... |` table of CHAIN.md, lays the nodes out in
layers (the target theorem on top, definitions and cited results at the bottom; a node sits one
layer below everything that uses it), writes CHAIN.tex (standalone TikZ) next to CHAIN.md, compiles
it with latexmk (-pdf -synctex=1) unless --no-pdf, and rewrites the mermaid block between
`<!-- chain-graph:begin -->` and `<!-- chain-graph:end -->` in CHAIN.md.

usage: chain_graph.py CHAIN.md [--no-pdf] [--tex-only]
"""
import argparse, pathlib, re, shutil, subprocess, sys

KINDS = ["theorem", "lemma", "step", "def", "external", "assumption"]
STYLE = {
    "theorem": "draw, very thick, rounded corners, fill=blue!10",
    "lemma": "draw, thick, rounded corners, fill=blue!4",
    "step": "draw, dashed, rounded corners",
    "def": "draw, fill=gray!12",
    "external": "draw, double, fill=yellow!15",
    "assumption": "draw, dotted, fill=red!5",
}
MERMAID_STYLE = {
    "theorem": "fill:#dbe6fb,stroke:#1f3a93,stroke-width:3px",
    "lemma": "fill:#eef3fd,stroke:#1f3a93,stroke-width:2px",
    "step": "fill:#ffffff,stroke:#333,stroke-dasharray:4 3",
    "def": "fill:#e6e6e6,stroke:#333",
    "external": "fill:#fff6cc,stroke:#333,stroke-width:3px",
    "assumption": "fill:#fdeaea,stroke:#333,stroke-dasharray:1 3",
}


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
        nodes[nid] = {"kind": kind, "title": r.get("title", "").strip(), "status": r.get("status", "").strip()}
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
           "—": "--", "–": "--", "’": "'", "“": "``", "”": "''"}


def tex_escape(s):
    """Escape LaTeX specials and replace the Unicode symbols pdflatex cannot typeset; any other
    non-ASCII character is dropped (titles should be short plain words)."""
    s = re.sub(r"([_&%#$^{}~])", lambda m: {"^": r"\^{}", "~": r"\~{}"}.get(m.group(1), "\\" + m.group(1)), s)
    for k, v in SYMBOLS.items():
        s = s.replace(k, v)
    s = s.replace("|", "$|$")
    return "".join(ch if ord(ch) < 128 else "?" for ch in s)


def tikz(nodes, edges, depth):
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
        per_row = 6
        rows = [ns[i:i + per_row] for i in range(0, len(ns), per_row)]
        for ri, row in enumerate(rows):
            width = (len(row) - 1) * 3.0
            for i, n in enumerate(row):
                x = i * 3.0 - width / 2 + (0.6 if ri % 2 else 0)
                pos[n] = (x, y - ri * 1.3)
                label = r"\texttt{" + tex_escape(n) + "}"
                if nodes[n]["title"]:
                    label += r"\\" + tex_escape(nodes[n]["title"])
                out.append(f"\\node[{STYLE[nodes[n]['kind']]}] ({tikz_id(n)}) at ({x:.2f},{pos[n][1]:.2f}) {{{label}}};")
        y -= 2.2 + 1.3 * (len(rows) - 1)
    for a, b, opt in edges:
        style = "->, gray!70!black, dashed" if opt else "->, gray!70!black"
        out.append(f"\\draw[{style}] ({tikz_id(a)}) -- ({tikz_id(b)});")
    # legend
    lx = max(p[0] for p in pos.values()) + 3.4
    out.append(f"\\node[anchor=north west, text width=3.2cm, font=\\scriptsize, align=left] at ({lx:.2f},0.6) {{"
               r"\textbf{Legend}\\ thick blue: target theorem\\ blue: lemma\\ dashed box: proof step\\ gray: definition\\ double: cited result\\ dotted: assumption\\ arrow: uses\\ dashed arrow: the paper's route, Lean may differ};")
    out += [r"\end{tikzpicture}", r"\end{document}"]
    return "\n".join(out) + "\n"


def tikz_id(n):
    return re.sub(r"[^A-Za-z0-9]", "", n) or "n"


def mermaid(nodes, edges):
    out = ["```mermaid", "graph TD"]
    for n, info in nodes.items():
        label = n + ("<br/>" + info["title"] if info["title"] else "")
        out.append(f'  {tikz_id(n)}["{label}"]')
    for a, b, opt in edges:
        out.append(f"  {tikz_id(a)} {'-.->' if opt else '-->'} {tikz_id(b)}")
    for k, st in MERMAID_STYLE.items():
        members = [tikz_id(n) for n, i in nodes.items() if i["kind"] == k]
        if members:
            out.append(f"  classDef {k} {st}")
            out.append(f"  class {','.join(members)} {k}")
    out.append("```")
    return "\n".join(out)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("chain")
    ap.add_argument("--no-pdf", action="store_true")
    ap.add_argument("--tex-only", action="store_true", help="do not touch CHAIN.md's mermaid block")
    a = ap.parse_args()
    path = pathlib.Path(a.chain).resolve()
    text = path.read_text(encoding="utf-8")
    rows = parse_chain(text)
    nodes, edges = nodes_edges(rows)
    if not nodes:
        sys.exit("chain_graph: the table has no rows yet")
    depth = layers(nodes, edges)
    tex = path.with_name("CHAIN.tex")
    tex.write_text(tikz(nodes, edges, depth), encoding="utf-8")
    print(f"{len(nodes)} nodes, {len(edges)} edges, {max(depth.values()) + 1} layers -> {tex}")
    if not a.tex_only:
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
        p = subprocess.run([lm, "-pdf", "-synctex=1", "-interaction=nonstopmode", "-halt-on-error", tex.name],
                           cwd=tex.parent, capture_output=True, text=True)
        if p.returncode == 0:
            print(f"compiled {tex.with_suffix('.pdf')}")
        else:
            print(p.stdout[-1500:], file=sys.stderr); sys.exit("chain_graph: latexmk failed")


if __name__ == "__main__":
    main()
