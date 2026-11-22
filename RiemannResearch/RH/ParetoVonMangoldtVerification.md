# Verification of the Pareto–von Mangoldt manuscript

The four equivalent conditions in the manuscript imply Mathlib’s `RiemannHypothesis`. The finite-trial implication takes the following arithmetic hypothesis.

$$
\forall \varepsilon>0\;\exists N\;\exists m\in M_N:
\quad \lVert J_2-(\log 2)\mathbf1-m\rVert_P^2<\varepsilon .
$$

The conductor-241 theorem supplies these fits for each tolerance exceeding approximately 0.00464918214215. An independent estimate for all positive tolerances remains open.

## Lean verification

The project uses `leanprover/lean4:v4.33.0-rc2`. Building the aggregate target with the following command verifies all project Lean modules.

```sh
bazel build --config=buildbuddy --color=no --curses=no //:RiemannResearch
```

Every one of the 5,097 tracked Lean sources is reachable from the aggregate import. A source scan found zero occurrences of the proof-hole tokens `sorry` and `admit` and zero project-local axiom declarations. The following audit imported the root and inspected the transitive axiom dependencies of every declaration it could attribute to a project module. Lean accepted the transitive dependencies of the project declarations with only `propext`, `Classical.choice`, and `Quot.sound` on the allowlist. The check for a declaration of the bare RH type also covers the project alias `RiemannResearch.RH.Statement`. [Bazel audit invocation](https://app.buildbuddy.io/invocation/78de20a7-253c-4e8e-8dfe-716bb09c3e7a)

```lean
import Lean.Util.CollectAxioms
import RiemannResearch

open Lean in
run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let isProject := fun (name : Name) => (`RiemannResearch).isPrefixOf name
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  let mut used : NameSet := {}
  let mut bare : Array Name := #[]
  for (name, ci) in env.constants do
    let some idx := env.getModuleIdxFor? name | continue
    unless isProject modules[idx.toNat]! do continue
    checked := checked + 1
    if ci.type.isConstOf ``RiemannHypothesis || ci.type.isConstOf ``RiemannResearch.RH.Statement then
      bare := bare.push name
    for ax in ← collectAxioms name do
      unless allowed.contains ax do throwError "unexpected axiom {ax} in {name}"
      used := used.insert ax
  let projectModules := modules.filter isProject
  if checked == 0 then throwError "no imported project declarations available"
  logInfo m!"Project modules {projectModules.size}, declarations {checked}, axioms {used.toArray}, declarations of bare RiemannHypothesis {bare}"
```

## Manuscript build

From this directory, run the following command twice. The five-page PDF passed the cross-reference and page-layout checks.

```sh
pdflatex -halt-on-error -jobname=ParetoVonMangoldtManuscript ParetoVonMangoldtManuscript.tex.md
```

[LaTeX driver](ParetoVonMangoldtManuscript.tex.md) · [LaTeX section](ParetoVonMangoldtReduction.tex.md) · [Finite trial proofs](CenteredParityFiniteTrials.lean) · [Finite-head interpolation](ParetoMixedCenteredParityHeads.lean)
