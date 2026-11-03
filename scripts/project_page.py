#!/usr/bin/env python3
"""project_page.py — the project page of one formalization: PROJECT.html next to CHAIN.md.

usage: project_page.py <Slug> [--ws DIR] [--check] [--out FILE] [--per-row N]

One self-contained HTML file (no network; it opens from disk) built from `status.py --json`:
- the header: the chain's title, the end the user chose and its milestones, when the first piece started;
- the progress strip: one block per piece to prove, as wide as its size in sessions (the actual size for a done
  piece, the estimate for the rest), with the rows by status under it;
- what waits for the reader: pieces whose status cell starts with `waiting`, the position's checks, rows on no
  piece, review objections without an answer;
- the pieces (Roadmap table): session, start, end, size against actual; a click shows the piece's rows, the files
  that declare their Lean names, the review rounds that covered it, and lights its rows up in the graph;
- the proof chain as a graph with CHAIN.pdf's encoding (fill = status, border = kind; layers as in
  chain_graph.py); a click on a row shows its columns, its premises and its users;
- the Lean files with the verdicts (only with --check, which reruns them), and the questions for the reader.
The `session`, `start` and `end` columns of the Roadmap table are optional; a URL in the session cell becomes a link.
Regenerate the page at every stop, after the Roadmap table is updated.
"""
import argparse, json, os, pathlib, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import chain_graph as cg  # noqa: E402
import status  # noqa: E402

NODE_W, NODE_H, PITCH, ROW_GAP, LAYER_GAP = 168, 58, 184, 16, 44


def layout(data, per_row):
    """Node centres: the layers of chain_graph.layers (target on top), each layer ordered by the mean position of
    the rows that use its nodes (fewer crossings than CHAIN.pdf's order by kind), wrapped at `per_row`."""
    nodes = {r["id"]: {"kind": r["kind"]} for r in data["rows"]}
    edges = [(e["from"], e["to"], e["optional"]) for e in data["edges"]]
    if not nodes:
        return {"pos": {}, "w": 0, "h": 0, "nw": NODE_W, "nh": NODE_H}
    depth = cg.layers(nodes, edges)
    users = {n: [] for n in nodes}
    for a, b, _ in edges:
        users[b].append(a)
    kind_order = {k: i for i, k in enumerate(cg.KINDS)}
    index = {r["id"]: i for i, r in enumerate(data["rows"])}
    by_layer = {}
    for n in nodes:
        by_layer.setdefault(depth[n], []).append(n)
    cols = min(per_row, max(len(v) for v in by_layer.values()))
    x, y, top = {}, {}, 0.0
    for L in sorted(by_layer):
        def key(n):
            xs = [x[u] for u in users[n] if u in x]
            return (sum(xs) / len(xs) if xs else 1e9, kind_order[nodes[n]["kind"]], index[n])
        ns = sorted(by_layer[L], key=key)
        for i in range(0, len(ns), per_row):
            chunk = ns[i:i + per_row]
            off = (cols - len(chunk)) * PITCH / 2
            for j, n in enumerate(chunk):
                x[n], y[n] = off + j * PITCH + PITCH / 2, top + NODE_H / 2
            top += NODE_H + ROW_GAP
        top += LAYER_GAP - ROW_GAP
    return {"pos": {n: [round(x[n], 1), round(y[n] + 8, 1)] for n in nodes}, "w": cols * PITCH, "h": round(top + 8, 1),
            "nw": NODE_W, "nh": NODE_H}


def sub_projects(data, ws):
    """Other formalization directories a piece's route names (`CipherLean/<X>/`): link their page, else their chain."""
    out = {}
    for p in (data["position"] or {}).get("pieces", []):
        links = []
        for x in dict.fromkeys(re.findall(r"CipherLean/([A-Za-z0-9_/]+?)/?`", p["route"])):
            d = pathlib.Path(ws) / "CipherLean" / x
            for f in ("PROJECT.html", "CHAIN.md"):
                if (d / f).exists():
                    links.append({"slug": x, "href": (d / f).resolve().as_uri(), "file": f}); break
        out[p["piece"]] = links
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("slug")
    ap.add_argument("--ws", default=os.environ.get("CIPHERLEAN_WS", str(pathlib.Path.home() / "cipherlean")))
    ap.add_argument("--check", action="store_true", help="rerun check_lean and chain_check for the page (one Lean listing)")
    ap.add_argument("--out", help="output file (default CipherLean/<Slug>/PROJECT.html)")
    ap.add_argument("--per-row", type=int, default=8, help="nodes per line of a layer in the graph (default 8)")
    a = ap.parse_args()
    data = status.collect(a.slug, a.ws, check=a.check)
    data["layout"] = layout(data, a.per_row)
    data["sub"] = sub_projects(data, a.ws)
    out = pathlib.Path(a.out) if a.out else pathlib.Path(data["dir"]) / "PROJECT.html"
    payload = json.dumps(data, ensure_ascii=False).replace("</", "<\\/")
    page = (pathlib.Path(HERE).parent / "assets" / "project-page.html").read_text(encoding="utf-8")
    page = page.replace("__SLUG__", a.slug.replace("<", "&lt;")).replace("__DATA__", payload)
    out.write_text(page, encoding="utf-8")
    pos = data["position"] or {}
    print(f"project_page: wrote {out} ({len(page) // 1024} KB; {len(data['rows'])} rows, {len(pos.get('pieces', []))} pieces"
          + ("; verdicts rerun" if a.check else "; verdicts not rerun (--check)") + ")")


if __name__ == "__main__":
    main()
