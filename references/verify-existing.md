# Verifying an existing Lean formalization (someone else's project)

The skill's workflow (steps 0–8) is for formalizing a theorem yourself in the workspace. A
different job comes up often: a Lean project already exists — written by a colleague, by another
model, months ago — and the question is whether it really proves the paper's theorems. The
lessons below come from one such run (2026-10-31/11-01: a 81-file, 52 000-line project proving
four conjectures, verified in a two-session setup) that took six hours of wall time, most of it
avoidable. Each lesson is a rule; the numbers are what was measured.

## 1. Settle the environment before the first build

- Read `lean-toolchain` and `lake-manifest.json` first. Compare with what is installed (`elan
  toolchain list`, the Mathlib commit under `~/cipherlean/.lake/packages/mathlib`). A project
  pinned to a release candidate (`v4.33.0-rc1`) with a machine that has only the release
  (`v4.33.0`) is **417 Mathlib commits** apart; a result obtained on the wrong pin is a result
  about the wrong pin, and the caveat has to head the report. Decide at this point: install the
  pinned toolchain and cache (only if the network allows: measured 8–22 KB/s that night, so no),
  or verify on the available pin and say so, or change the project's pin and re-verify.
- Never run `lake update` or `lake exe cache get` inside a synced or sandboxed folder: `~/sync` is
  Syncthing (6 GB of `.lake` would have been shipped to every device) and the sandbox refused to
  write `~/.elan`. Copy the project to a scratch directory, symlink `.lake` to a scratch build
  tree, reuse the workspace's Mathlib packages when the pin matches
  (`scripts/sandbox_project.sh` does this and refuses when the pins differ).
- Pin discipline for your own projects: pin releases, not release candidates; keep
  `lean-toolchain`, `lakefile` and the manifest consistent; ship `verify.sh`; run it on a clean
  machine before handing the project over.

## 2. Measure before you wait

- Inventory the computational proofs before building: `scripts/build_profile.py --sites <dir>`
  counts `native_decide`, `decide +kernel`, `bv_decide` per file. That project had 92
  `native_decide` calls in 21 files; one of them was going to take 1 h 49 min.
- Build the heaviest certificate module *alone* first, with a time budget written down before
  starting (that run used 60 min per module). Sample the Lean process (`ps`/psutil: CPU time,
  RSS, swap) every few minutes: 95 % of one core with constant RSS and no swap means progress,
  not a hang; do not kill a progressing build to "try something" unless you have a measured
  reason — a kill at 85 min threw away 58 min of CPU and the rebuilt module needed 1 h 49 min
  anyway.
- After a build, `scripts/build_profile.py <lake build log>` lists module times from the `Built
  X (Ns)` lines; the top entry is where the next hour goes. In that project one module was 96 %
  of 6 799 s.
- One Lean job per machine while timing matters: probes and benchmarks run beside the build
  share the CPU and the `.lake` directory and make every number meaningless.

## 3. Know how `native_decide` evaluates

- Compiled code does not cache a closed `def` that appears inside the term being evaluated: a
  transparent `def` building a 30-million-element `HashSet` was rebuilt at every reference
  inside loops of 32³ and |inv| × 256 iterations. Measured on a reduced copy: three references
  through a `def` 200 s, the same three through an `opaque` 25 s; `let`-binding the value,
  `@[noinline]`, and passing it as a function argument changed nothing (156 s, 212 s, 198 s).
  Rule: a certificate checker refers to large closed data only through `opaque` definitions or
  precomputed literals. The project's author had done this for three closures and missed the
  fourth; the miss cost the whole night.
- A breadth-first closure inside a certificate grows exponentially (rounds K = 1, 4, 8: 1.75 s,
  2.63 s, 272 s; K = 9 over 5 min). Compute closures offline, ship them as data, and let Lean
  check closedness and membership; never search inside the proof.
- Several `native_decide` sites were small enough for `decide +kernel` (the external audit listed
  them). Replace them: fewer compiler axioms, same build time.
- Trust boundary on Lean v4.33.0: each `native_decide` adds a per-declaration axiom
  `<decl>._native.native_decide.ax_*`; the four theorems carried 11/9/55/53 of them (77 distinct).
  Report the count, the list, and the bridge lemma for every group (step 5b).

## 4. Two sessions, and what the second one must not do

- The reviewer must not issue a verdict while the build is `PENDING`: the first-round report said
  PASS with "build pending" and was later contradicted by an external audit on seven points
  (inconsistent verdict labels, an outdated description of the `native_decide` mechanism, wrong
  counts of call sites and warnings, a lemma attributed to the wrong conjecture in the README).
  The round protocol in `review-brief.md` (objections with ids, written answers, chat summaries)
  and the two machine checks (`check_lean.py`, `chain_check.py`) exist so that these are found
  by scripts, not by a second reviewer the next morning.
- Correspondence tables are generated, not written: a README that says "lemma X is derived
  through Y" must be checked against the import graph and the proof terms (`chain_check.py`
  does this for a `CHAIN.md`; for an existing project, write the chain table from the README
  and run it). A redundant special-case branch ((3,3) in that project) and a misattributed
  mechanism were only found this way.

## 5. What "done" means

Not done: build passes on a different pin than the project declares; the one-line `opaque` fix
and the verification reports sit uncommitted; a caveat lives only in a report nobody will read.
Done: `verify.sh` passes on the declared pin (or the pin is changed to the verified one and
committed), `#print axioms` output and the module-time table are in the repository, the README's
correspondence claims were regenerated from the code, every `native_decide` has its bridge and
is listed, and the commit is pushed. Write the completion criteria down at the start, with the
time budget, and report against them.

## Checklist (copy into the task's log)

1. Pin read, environment decided, sandbox copy made (`sandbox_project.sh`).
2. `build_profile.py --sites`: computational sites counted; heaviest module identified.
3. Heaviest module built alone under a written budget; process sampled; result recorded.
4. Full build; `build_profile.py` on the log; `verify.sh`; `#print axioms` saved.
5. `check_lean.py` on every top-level file; chain table from the README; `chain_check.py`.
6. Reviewer round with the build evidence in hand; written answers; `REVIEW.md`.
7. Fixes committed with the evidence; pin consistent; report with the caveats first.
