# Zeta23 import completion — 28 September 2026

## Scope and provenance

Continuation of RiemannResearch commit
14bb23a14bff7db661164db012628091fc86eafb.

Source: [Alpöge–Furman, arXiv:2608.13637](https://arxiv.org/abs/2608.13637)
and [anthropics/formal-math, pinned source](https://github.com/anthropics/formal-math/tree/fbdc36bbf17d20af3fd0447c6d1a8a02773c9844/zeta23).
The upstream source supplies the mathematical statements and proofs of the
zero-proportion, prime-side, and analytic-input results. The project adds
the zero-extraction and Pareto-obstruction specializations.

The existing 57-module compact Weil closure is extended by 83 modules.
This includes Final, FinalMult, and ThmD/Mult and their dependencies.
It excludes Challenge placeholders, Solution wrappers, Dirichlet,
XiPrime, and PairCeiling. Original namespaces and proof bodies are
preserved. Six blanket Mathlib imports are replaced by focused imports;
WeilExplicitFormula/PROVENANCE.md records these changes. The shared Mathlib commit remains
51e6992efd06126df61a496bebf8f49482a4e129. No new dependency is added.

## Imported results

| Declaration | Content | Domain-specific premises |
|---|---|---|
| Zeta23.riemannVonMangoldt_zeta | Full dyadic zero-count asymptotic and local count bound | None |
| Zeta23.MV.mv_hilbert | Weighted bilinear Montgomery–Vaughan inequality with an absolute constant | None beyond the inequality's explicit finite-frequency conditions |
| Zeta23.paperInputs_zeta | All analytic inputs instantiated for the actual zeta zeros | None |
| Zeta23.thmA₀ | Distinct on-line proportion at least 2/3 | None |
| Zeta23.thmB₀_mult | Simple on-line proportion at least 2/3 | None |
| Zeta23.thmC₀_mult | Distinct proportion at least 5/6 | None |
| Zeta23.ThmD.thmD₀_simple_mult | Simple on-line proportion at least 2−1/cStar(1) | None |
| Zeta23.ThmD.thmD₀_dist_mult | Distinct proportion at least (3−1/cStar(1))/2 | None |

Here N counts with multiplicity, while the simple/distinct numerators
count distinct points. Every displayed proportion is the upstream
eventual epsilon-form, with its exact constant; the simple and distinct
results include cumulative versions. These remain upstream results.

## New critical-zero provider

Module: RH/CriticalLineZeros.lean; namespace RiemannResearch.RH.

- simpleCriticalZeroCount_dyadic_tendsto_atTop:
  the number of simple critical-line zeros in (T,2T] tends to infinity.
- eventually_exists_simple_critical_zero_dyadic:
  every sufficiently high dyadic window contains an actual simple zero.
- exists_simple_critical_zero_above:
  for every real H, there is such a zero with Im(rho)>H.
- exists_critical_zero:
  there exists rho with riemannZeta rho=0 and Re(rho)=1/2.

The proof takes epsilon=1/3 in the 2/3 simple-zero proportion, combines it
with Riemann–von Mangoldt growth, and extracts a point from a set of
positive finite cardinality. Thus the proportional inequality cannot be
vacuous. Simplicity uses the original analytic-order multiplicity.

## Unconditional mass obstruction

Module: RH/ProjectedDualMassObstructionUnconditional.lean; namespace
RiemannResearch.RH.Pareto.CoefficientStabilization.CorrectionTail.

exists_coefficient_mass_stretched_barrier has no premises and states:

    exists a>0, exists one fixed d in {2,3}, forall b<a,
      exp(-b Phi(n)) projectedDualCoefficientMass n d^2 -> +infinity.

Phi(n)=((6+log n) log(6+log n))^(1/11).

coefficient_mass_stretched_barrier retains any given arithmetic exponent
a satisfying the explicit eventual canonical-energy estimate; it does
not weaken that exponent. not_cofinal_stretched_coefficient_mass and
not_cofinal_stretched_l2_concentration retain the same energy hypothesis
and rule out the global strict-margin budgets, allowing separate
exponents b_d<a and separate cofinal sets for each d.

The original *_of_critical_zero declarations remain the conditional,
lighter analytic interfaces. The new assembly discharges their zero
premise with a theorem. No axiom is used to assert zero existence.

## Limits of the conclusion

RH remains Open. The endpoint b=a, direct physical-tail bounds, and
cofinal smallness of the signed correction pairing remain Open.
The imported oscillatory and spectral estimates are available for
further research; no estimate for the growing Pareto inverse-Gram
coefficients is inferred without proving the relevant correspondence.
A positive proportion on the line does not exclude every off-line zero.

## Verification boundary

Imported executable source is scanned with nested comments and strings
excluded; no proof holes, project-local axioms, unsafe declarations,
native_decide, or external proof-evaluation hooks are introduced.
The final publication checkpoint compiles the affected module graph.
The full project build succeeded in job
`job_6aCSTLypXtTRqZE5upxJwCctqH4-K7CS`.
The exact-type and 13-endpoint axiom audit succeeded in job
`job_fNxyjrlIIb81oC2E24O0GitQLce2N8lh`: every audited declaration reports
only propext, Classical.choice, and Quot.sound. In particular,
exists_critical_zero and exists_coefficient_mass_stretched_barrier have
no premises. The explicit-energy variants retain exactly their stated
energy hypotheses. The final publication checkpoint validates the
committed affected-module graph.
