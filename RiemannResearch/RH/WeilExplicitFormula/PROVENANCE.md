# Compact Weil explicit formula: source and scope

Upstream: [anthropics/formal-math, zeta23](https://github.com/anthropics/formal-math/tree/fbdc36bbf17d20af3fd0447c6d1a8a02773c9844/zeta23).

Pinned upstream commit: `fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`.
The earlier `anthropics/zeta-23-lean` repository URL redirects to this repository.

Lean: `leanprover/lean4:v4.33.0-rc2`.
Mathlib: `51e6992efd06126df61a496bebf8f49482a4e129`.
Both match the existing RiemannResearch project exactly.

## Scope

This directory contains exactly the 57 upstream project modules transitively
imported by `Zeta23.WeilEF.Main`, in their original namespaces. The original upstream
closure contains 18,105 source lines. No headline zero-proportion theorem, trusted
Challenge placeholder, Solution module, XiPrime module, or unrelated file is
included. The linear-algebra and tail modules present here are imported by
the upstream `Hypotheses`/`Tail` dependency chain. They are import-reachable;
no claim is made that every declaration in each imported module occurs in
the final theorem's kernel dependency graph.

The exposed upstream theorem is
`Zeta23.WeilEF.EF_lit_zetaZeroConfig : Zeta23.EF.EF_lit Zeta23.zetaZeroConfig`.
It has no hypotheses. The compact test hypotheses appear when the proposition
`EF_lit` is expanded: `ContDiff ℝ 2 k` and `HasCompactSupport k`.

The carrier is exactly `riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1`, and the
multiplicity is `(analyticOrderAt riemannZeta ρ).toNat`. Positivity and
finiteness of the multiplicities and the necessary symmetries are proved
in the imported seam; no seam hypothesis remains in the exposed theorem.

The formula includes absolute convergence of the zero sum, every von
Mangoldt prime-power term, the two pole terms, and the digamma integral.
It also supplies the unconditional inverse-square zero-sum majorant and
the unit-window zero-count bound. The stronger dyadic Riemann--von Mangoldt
theorem is available upstream but requires 12 additional modules when its
GammaFacts package is closed. Those modules are intentionally excluded here
because the compact formula and inverse-square majorant already suffice
for the intended extension argument.

## Mechanical changes

Each file retains its original copyright and license notices. A new header
records this relocation. Every command of the form `import Zeta23.X` has
been changed to `import RiemannResearch.RH.WeilExplicitFormula.X`. No theorem,
definition, proof body, namespace, attribute, option, or standard dependency
import has been changed. The only other changes are whitespace normalization and the documentation
corrections recorded below; all executable source is preserved.

The closure contains no exact `import Mathlib` command. Its imports are
specific Mathlib modules and one existing standard dependency module,
`Batteries.Tactic.Lemma`, used by `FromPNTPlus/ZetaBounds.lean`.

The upstream `Prelude/InstancePriorities.lean` demotes
`LieAlgebra.toModule` to instance priority 10. This existing upstream
attribute is retained; it does not alter theorem statements, but can
affect instance elaboration in importers.

## Audit boundary

The original source was scanned with nested Lean block comments, line
comments, and string literals excluded. The complete imported closure
contains no executable `axiom`, `sorry`, `admit`, `unsafe`, `native_decide`,
`implemented_by`, `extern`, `mkSorry`, `ofReduceBool`, or `addDecl` token.
Documentation corrections (7 September 2026): the publication audit identified
postulated-constant examples inside the additive-combination documentation,
a line beginning with the corresponding declaration keyword in Hypotheses,
and a proof-status word in StrongPNTPrefix. The example now uses explicit
parameters and hypotheses; the two prose descriptions were reworded. A
nested-comment-aware comparison confirms that executable source is unchanged
in all three files. Copyright and license text is unchanged.

The relocated compact formula passed this project's `efcore1` compiler check.
The combined completion check `job_Krj1svNf3MBDoFYei95fp6xuWVuq_WxM` also passed
and audited the exposed compact formula and downstream endpoints: their only
axioms are propext, Classical.choice, and Quot.sound. The subsequent native
publication checkpoint validates the normal module imports. A source scan
alone is not used as compilation evidence.

The conversion of the Fourier/digamma integral to the spatial subtracted gamma
kernel is supplied by the separate WeilGammaFourierAdapter module. The dominated
extension to noncompact superexponential tests is supplied by
WeilNoncompactExplicitFormula. Both passed the combined completion check; this
compact adapter itself exposes only the compact formula and its majorants.

## License and attribution

Apache License 2.0; see `LICENSE.md` and `NOTICE.md` in this directory.
Copyright 2026 Anthropic, PBC. The `FromPNTPlus` modules preserve notices
for the PrimeNumberTheoremAnd and Mathlib contributors, including original
authors and upstream commit references. The included `NOTICE.md` is copied
unchanged from the upstream zeta23 project.

Whitespace normalization: trailing whitespace and terminal blank lines removed; proof tokens unchanged.
