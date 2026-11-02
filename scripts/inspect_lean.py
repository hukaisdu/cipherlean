#!/usr/bin/env python3
"""inspect_lean.py — one Lean listing for every check of the skill.

One `lake env lean` run loads the given paper module(s) next to the built modules of the shared library and emits, per declaration
of those modules and of `CipherLean/Lib`: its name, module, side (PAPER = a module given, LIB = the library),
kind, axioms (PAPER side only; `collectAxioms`), elaborated statement, the constants its proof term uses and the
constants its statement (type) uses — both within the paper modules and the library, with Lean's auxiliary
constants (`foo._proof_1`, `foo.match_1`, …) expanded through their own values so that a shared auxiliary proof
is never attributed to the declaration it happens to be named after. With --dups it also reports every paper
theorem whose statement is definitionally equal (reducible transparency) to a library theorem's.

`check_lean.py` (axioms + statements), `chain_check.py` (proof and statement dependencies), `notation_check.py`
(names), `promote_candidates.py` (statements, type constants, duplicates) and `status.py --check` (all of them
at once, one listing for all the piece files) consume this listing instead of running their own; their CLIs,
verdict lines and exit codes are unchanged. The file is named `inspect_lean`, not `inspect`, because the scripts
put their own directory first on `sys.path` and a module called `inspect` would shadow Python's.

usage: inspect_lean.py <file.lean> [<file2.lean> ...] [--ws DIR] [--out FILE] [--dups] [--timeout SEC]
Prints the JSON listing (or writes it to --out). Exit 2 when the listing fails (a module not built, say).
"""
import argparse, json, os, pathlib, re, shutil, subprocess, sys, time

AUX_RE = re.compile(r"\.(congr_simp|match_\d+|proof_\d+|eq_\d+|_cstage\d*)$")


def is_auxiliary(name):
    """Declarations Lean generates next to a user's: `foo.congr_simp` (simp's first use of `foo`), `foo.match_1`,
    `foo.proof_1`, `foo.eq_1`. They carry axioms like any other, so the checks keep them, counted apart."""
    return bool(AUX_RE.search(name))


def die(msg, code=2):
    print(f"inspect_lean: {msg}", file=sys.stderr)
    sys.exit(code)


def find_workspace(arg=None):
    ws = arg or os.environ.get("CIPHERLEAN_WS") or os.path.expanduser("~/cipherlean")
    ws = pathlib.Path(ws).resolve()
    if not (ws / "lakefile.toml").exists() and not (ws / "lakefile.lean").exists():
        die(f"no lakefile in workspace {ws}: run scripts/setup_env.sh --install (or set --ws / CIPHERLEAN_WS)")
    return ws


def module_name(ws, file):
    """`CipherLean/Foo/Main.lean` → `CipherLean.Foo.Main`; a file reached through a `CipherLean/<Slug>` symlink
    (`new_paper.sh --paper-dir`) is named by the link."""
    f = pathlib.Path(file).resolve()
    if f.suffix != ".lean":
        die(f"not a .lean file: {file}")
    if f == (ws / "CipherLean.lean").resolve():        # the umbrella, a symlink into the skill
        return "CipherLean"
    try:
        rel = f.relative_to(ws)
        return ".".join(rel.with_suffix("").parts)
    except ValueError:
        pass
    formal = ws / "CipherLean"
    if formal.is_dir():
        for link in sorted(formal.iterdir()):
            if link.is_symlink():
                try:
                    rel = f.relative_to(link.resolve())
                    return ".".join(["CipherLean", link.name, *rel.with_suffix("").parts])
                except ValueError:
                    continue
    die(f"{f} is not inside the workspace {ws} (directly or through a CipherLean/<Slug> symlink)")


def lake():
    exe = shutil.which("lake") or os.path.expanduser("~/.elan/bin/lake")
    if not os.path.exists(exe):
        die("lake not found; install elan (https://lean-lang.org/install/)")
    return exe


def run(cmd, cwd, timeout):
    """Run `cmd` in the workspace under the shared build lock (one Lean job per workspace)."""
    import fcntl
    lock_path = pathlib.Path(cwd) / ".lake" / "cipherlean-build.lock"
    lock_path.parent.mkdir(parents=True, exist_ok=True)
    # ~/.elan/bin first: non-login ssh shells do not have it on PATH
    env = dict(os.environ, PATH=os.path.expanduser("~/.elan/bin") + os.pathsep + os.environ.get("PATH", ""))
    with open(lock_path, "w") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX)
        try:
            p = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, timeout=timeout, env=env)
        except subprocess.TimeoutExpired:
            die(f"timed out after {timeout}s: {' '.join(cmd)}")
    return p.returncode, (p.stdout or "") + (p.stderr or "")


def lib_modules(ws, built_only=False):
    """The library modules; with built_only those whose .olean exists (a fresh workspace checks Smoke.lean before the
    library is compiled, and the listing must not import what is not built yet)."""
    lib_dir = ws / "CipherLean" / "Lib"
    if not lib_dir.is_dir():
        return []
    mods = sorted(".".join(["CipherLean", "Lib", *f.relative_to(lib_dir).with_suffix("").parts]) for f in lib_dir.rglob("*.lean"))
    if built_only:
        mods = [m for m in mods if (ws / ".lake" / "build" / "lib" / "lean" / pathlib.Path(*m.split("."))).with_suffix(".olean").exists()]
    return mods


LEAN = r'''
import Lean
{imports}

open Lean Elab Command Meta

set_option maxRecDepth 8192

/-- Constants a term uses, with Lean's auxiliary constants (`foo._proof_1`, `foo._simp_1_2`, `foo.match_1`, ...)
expanded through their own values, restricted to the modules in scope. -/
def depsOf (env : Environment) (inScope : Name → Bool) (root : Name) (v : Expr) : Array Name := Id.run do
  let mut seen : NameSet := {{}}
  let mut acc : Array Name := #[]
  let mut stack : Array Name := v.getUsedConstants
  let mut fuel := 100000
  while fuel > 0 do
    fuel := fuel - 1
    match stack.back? with
    | none => break
    | some m =>
      stack := stack.pop
      if seen.contains m || m == root then continue
      seen := seen.insert m
      if m.isInternalDetail || (m.toString.splitOn "._").length > 1 then
        match env.find? m with
        | some (.defnInfo d) => stack := stack ++ d.value.getUsedConstants
        | some (.thmInfo t) => stack := stack ++ t.value.getUsedConstants
        | _ => pure ()
      else if inScope m then
        acc := acc.push m
  return acc

def listAll (withDups : Bool) : CommandElabM Unit := do
  let env ← getEnv
  let paperMods : List Name := [{papers}]
  let pidxs := paperMods.filterMap env.getModuleIdx?
  if pidxs.length != paperMods.length then throwError "paper module not loaded"
  let libMods : List Name := [{libmods}]
  let lidxs := libMods.filterMap env.getModuleIdx?
  let inScope (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some i => pidxs.contains i || lidxs.contains i
    | none => false
  let isPaper (n : Name) : Bool :=
    match env.getModuleIdxFor? n with
    | some i => pidxs.contains i
    | none => false
  let names : Array Name := env.constants.fold (init := #[]) fun acc n _ =>
    if inScope n && !n.isInternalDetail then acc.push n else acc
  let names := names.qsort (fun a b => a.toString < b.toString)
  for n in names do
    let some c := env.find? n | continue
    let kind := match c with
      | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
      | .opaqueInfo _ => "opaque" | .inductInfo _ => "inductive" | .quotInfo _ => "quot"
      | .ctorInfo _ => "ctor" | .recInfo _ => "rec"
    if kind == "ctor" || kind == "rec" || kind == "quot" then continue
    let modName := match env.getModuleIdxFor? n with
      | some i => toString (env.header.moduleNames[i.toNat]!)
      | none => ""
    let side := if isPaper n then "PAPER" else "LIB"
    let axStr ← if isPaper n then do
        let axioms ← collectAxioms n
        pure (",".intercalate (axioms.toList.map toString))
      else pure "-"
    let tyStr ← liftTermElabM do
      let fmt ← Meta.ppExpr c.type
      pure (fmt.pretty 100000)
    let tyOne := (tyStr.replace "\n" " ").replace "\t" " "
    let val? : Option Expr := match c with
      | .defnInfo d => some d.value | .thmInfo t => some t.value | .opaqueInfo o => some o.value | _ => none
    let used := match val? with
      | some v => (depsOf env inScope n v).toList
      | none => []
    let tused := (depsOf env inScope n c.type).toList
    IO.println s!"DECL\t{{n}}\t{{modName}}\t{{side}}\t{{kind}}\t{{axStr}}\t{{tyOne}}\t{{",".intercalate (used.map toString)}}\t{{",".intercalate (tused.map toString)}}"
  if withDups then
    -- duplicates: a paper theorem whose statement is definitionally equal to a library declaration's
    -- (reducible transparency: a duplicate is the same statement up to notation, and full unfolding can
    -- recurse without bound on finite checks)
    let libNames := names.filter fun n => !isPaper n
    for n in names do
      if !isPaper n then continue
      let some c := env.find? n | continue
      let isThm := match c with | .thmInfo _ => true | _ => false
      if !isThm then continue
      for m in libNames do
        let some d := env.find? m | continue
        if c.levelParams.length != d.levelParams.length then continue
        let same ← liftTermElabM do
          let us ← mkFreshLevelMVars c.levelParams.length
          let t1 := c.type.instantiateLevelParams c.levelParams us
          let t2 := d.type.instantiateLevelParams d.levelParams us
          withoutModifyingState (try withReducible (isDefEq t1 t2) catch _ => pure false)
        if same then IO.println s!"DUP\t{{n}}\t{{m}}"

#eval listAll {dups}
'''


def listing(ws, files, dups=False, timeout=1800):
    """The listing of the given .lean files (built already) as a dict; dies when Lean fails."""
    mods = [module_name(ws, f) for f in files]
    libmods = [m for m in lib_modules(ws, built_only=True) if m not in mods]     # imported one by one, no umbrella
    scratch_dir = ws / ".lake" / "inspect"
    scratch_dir.mkdir(parents=True, exist_ok=True)
    scratch = scratch_dir / ("_".join(m.replace(".", "_") for m in mods)[:150] + ("_dups" if dups else "") + ".lean")
    scratch.write_text(LEAN.format(imports="\n".join(f"import {m}" for m in mods + libmods), papers=", ".join("`" + m for m in mods),
                                   libmods=", ".join("`" + m for m in libmods), dups="true" if dups else "false"), encoding="utf-8")
    t0 = time.time()
    code, out = run([lake(), "env", "lean", str(scratch)], cwd=str(ws), timeout=timeout)
    decls, dupmap = [], {}
    for line in out.splitlines():
        if line.startswith("DUP\t"):
            _, pn, ln = line.split("\t", 2)
            dupmap.setdefault(pn, []).append(ln)
        elif line.startswith("DECL\t"):
            parts = (line.split("\t", 8) + [""] * 9)[:9]
            _, name, mod, side, kind, axs, ty, used, tused = parts
            decls.append({"name": name, "module": mod, "side": side, "kind": kind,
                          "axioms": None if axs == "-" else [x for x in axs.split(",") if x],
                          "statement": ty, "proof_consts": [u for u in used.split(",") if u and u != name],
                          "type_consts": [u for u in tused.split(",") if u and u != name], "auxiliary": is_auxiliary(name)})
    result = {"workspace": str(ws), "modules": mods, "library_modules": libmods, "declarations": decls, "dups": dupmap,
              "seconds": round(time.time() - t0, 1), "ok": code == 0 and "DECL\t" in out}
    if not result["ok"]:
        result["output"] = out[-4000:]
    return result


def load(path):
    with open(path, encoding="utf-8") as f:
        return json.load(f)


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("files", nargs="+"); ap.add_argument("--ws"); ap.add_argument("--out")
    ap.add_argument("--dups", action="store_true"); ap.add_argument("--timeout", type=int, default=1800)
    a = ap.parse_args()
    ws = find_workspace(a.ws)
    res = listing(ws, a.files, dups=a.dups, timeout=a.timeout)
    text = json.dumps(res, ensure_ascii=False, indent=1)
    if a.out:
        pathlib.Path(a.out).write_text(text, encoding="utf-8")
        print(f"{len(res['declarations'])} declarations ({sum(1 for d in res['declarations'] if d['side'] == 'PAPER')} of {', '.join(res['modules'])}) in {res['seconds']} s -> {a.out}")
    else:
        print(text)
    if not res["ok"]:
        die(f"listing failed for {', '.join(res['modules'])} (built? `lake_build.sh <module>` for each):\n{res.get('output', '')[-2000:]}")


if __name__ == "__main__":
    main()
