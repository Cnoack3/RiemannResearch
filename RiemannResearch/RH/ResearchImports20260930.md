# RH research imports — 30 September 2026

## Source pins and scope

| Development | Upstream commit | Selected scope |
| --- | --- | --- |
| ericlisg/erdos768-lean | e46ab245f1e5eb2d1f0b184874c4e32e02ad16c9 | Two additive/multiplicative large-sieve modules |
| nicholasbulka/li-criterion-rh-equivalence-lean | 35df682f3b709ffe5fbcfdd452dfa964bd622b87 | 33-module closure for the actual Li equivalence and zero-sum fidelity |
| adambornemann-glitch/Spectra | 8dbaaf6728d1342ae16acf79fd7eef7c59b37e63 | Seven operator-core modules: five full sources, two complete declaration excerpts |

The source references support the theorem statements and proof developments.
Original namespaces and licenses are retained. The local Lean v4.33.0-rc2 and
Mathlib commit 51e6992efd06126df61a496bebf8f49482a4e129 remain the target.

## Arithmetic estimates with their exact identities

Analysis/LargeSieve/Additive.lean retains the exact finite Parseval identity
Erdos768LS.parseval_expsum before the sampling/large-sieve estimate. The additive
bound uses delta^(-1) + 4*pi*N, rather than an imported sharp constant.
Analysis/LargeSieve/Multiplicative.lean retains the finite DFT Plancherel and
character orthogonality identities, primitive-character Gauss-sum conditions,
and Farey spacing. Erdos768LS.mult_large_sieve_final supplies the
multiplicative inequality with a universal positive constant, witnessed by
4*pi in its proof.

Concrete RH consumer: finite CRT frequency expansions and conductor-averaged
square-energy bounds, as proposed in RH/RawMobiusFarTailLargeSieve20260924.md.
The dual inequality, exact CRT Fourier identification, and weighted-tail
transfer must still be assembled for any new application. The September-24
note's sharper displayed large-sieve constant is not certified by this import.

## Actual Li criterion and zero-sum fidelity

LiCriterion.li_criterion_rh_iff uses Mathlib's RiemannHypothesis and the actual
completed xi, not a freely chosen coefficient sequence. XiGrowth supplies the
finite-order and order-at-most-one inputs.

LiCriterion.taylorCoeff_eq_li_symmetrized retains both signed exponents,
the factor one-half, and each zero's analytic multiplicity.
LiCriterion.summable_li_symmetrized supplies genuine summability.
The entire Hadamard dependency closure is included; no factorization premise
is installed as an axiom.

Open: positivity of every actual Li coefficient, or a checked bridge from
our signed CRT/Weil forms proving that positivity.

## Unbounded operator core

The port uses Mathlib's LinearPMap domains, adjoints and closure.
Spectra.Operator.isEssentiallySelfAdjoint_of_denseRange_addSub retains
symmetry, dense domain, and density of both shifted ranges. Deficiency-space
identities retain the dense-domain condition.

Concrete RH consumer: the Mellin/Jacobi operator described in
RH/MellinJacobiOperator20260928.md. Its symmetry, dense domain, and dense
shifted ranges still require proofs. This import supplies neither a Carleman
theorem nor an identification of the operator spectrum with zeta zeros.

## Verification

The incremental combined-project build completed successfully with
`lake build RiemannResearch --quiet`: all 42 imported modules and
RiemannResearch.lean compile in the unchanged target environment. The
26-endpoint `#check` / `#print axioms` audit also completed successfully.
The full audit output exceeded the tool response limit, so a compact follow-up
prints all 26 axiom lists for inspection.

The untruncated compact audit reports exactly the ordinary foundations
`propext`, `Classical.choice`, and `Quot.sound` for every endpoint;
no `sorryAx` or domain-specific axiom occurs in these dependencies.

The exact checked Li endpoint is:

```lean
LiCriterion.li_criterion_rh_iff :
  RiemannHypothesis ↔
    ∀ n : ℕ, 0 ≤ (LiCriterion.taylorCoeff LiCriterion.riemannXi n).re
```

The zero identity has coefficient factor one-half and summand
`analyticOrderNatAt riemannXi ρ * ((1 - z^(-(n+1))) + (1 - z^(n+1)))`,
where `z = 1 - 1/ρ`. Its separate summability theorem is included.

This report, source provenance, exports, and catalog are included in the final
checkpoint, which validates the changed modules and reverse dependencies
before publishing.

Reproduce the endpoint audit in the same project:

```lean
import RiemannResearch.Analysis.LargeSieve.Multiplicative
import RiemannResearch.Analysis.LiCriterionImport.Lc.LiCriterion.XiOrderBridge
import RiemannResearch.Analysis.LiCriterionImport.Lc.LiCriterion.Fidelity
import RiemannResearch.Analysis.UnboundedOperatorImport.Operator.EssentialSelfAdjointness
import RiemannResearch.Analysis.UnboundedOperatorImport.Operator.DeficiencySubspace

#check Erdos768LS.parseval_expsum
#print axioms Erdos768LS.parseval_expsum
#check Erdos768LS.additive_large_sieve
#print axioms Erdos768LS.additive_large_sieve
#check Erdos768LS.plancherel_dft
#print axioms Erdos768LS.plancherel_dft
#check Erdos768LS.orthogonality_sum
#print axioms Erdos768LS.orthogonality_sum
#check Erdos768LS.additive_large_sieve_indexed
#print axioms Erdos768LS.additive_large_sieve_indexed
#check Erdos768LS.farey_sum_bound
#print axioms Erdos768LS.farey_sum_bound
#check Erdos768LS.mult_large_sieve_final
#print axioms Erdos768LS.mult_large_sieve_final
#check LiCriterion.li_criterion_rh_iff
#print axioms LiCriterion.li_criterion_rh_iff
#check LiCriterion.taylorCoeff_eq_li_symmetrized
#print axioms LiCriterion.taylorCoeff_eq_li_symmetrized
#check LiCriterion.summable_li_symmetrized
#print axioms LiCriterion.summable_li_symmetrized
#check LiCriterion.taylorCoeff_eq_weighted_tsum
#print axioms LiCriterion.taylorCoeff_eq_weighted_tsum
#check LiCriterion.xi_hasFiniteOrder
#print axioms LiCriterion.xi_hasFiniteOrder
#check LiCriterion.xi_order_le_one
#print axioms LiCriterion.xi_order_le_one
#check Hadamard.General.hadamard_factorization_general
#print axioms Hadamard.General.hadamard_factorization_general
#check Spectra.Operator.isClosable_iff_dense_adjoint_domain
#print axioms Spectra.Operator.isClosable_iff_dense_adjoint_domain
#check Spectra.Operator.closure_adjoint_eq_adjoint
#print axioms Spectra.Operator.closure_adjoint_eq_adjoint
#check Spectra.Operator.adjoint_adjoint_eq_closure_of_isClosable
#print axioms Spectra.Operator.adjoint_adjoint_eq_closure_of_isClosable
#check Spectra.Operator.hasCore_iff_topologicalClosure_graph
#print axioms Spectra.Operator.hasCore_iff_topologicalClosure_graph
#check Spectra.YosidaHille.op_lower_bound
#print axioms Spectra.YosidaHille.op_lower_bound
#check Spectra.YosidaHille.op_range_isClosed
#print axioms Spectra.YosidaHille.op_range_isClosed
#check Spectra.YosidaHille.selfAdjoint_surjective_sub_smul
#print axioms Spectra.YosidaHille.selfAdjoint_surjective_sub_smul
#check Spectra.Operator.isSelfAdjoint_of_surjective_addSub_smul
#print axioms Spectra.Operator.isSelfAdjoint_of_surjective_addSub_smul
#check Spectra.Operator.IsEssentiallySelfAdjoint
#print axioms Spectra.Operator.IsEssentiallySelfAdjoint
#check Spectra.Operator.isEssentiallySelfAdjoint_of_denseRange_addSub
#print axioms Spectra.Operator.isEssentiallySelfAdjoint_of_denseRange_addSub
#check Spectra.Operator.deficiencySubspacePlus_eq_orthogonal
#print axioms Spectra.Operator.deficiencySubspacePlus_eq_orthogonal
#check Spectra.Operator.deficiencySubspaceMinus_eq_orthogonal
#print axioms Spectra.Operator.deficiencySubspaceMinus_eq_orthogonal
```

The axiom audit concerns dependencies of these declarations. It does not
discharge hypotheses appearing in their types or the application obligations
listed above. Upstream style/deprecation warnings remain; no compiler errors
remain after the target compatibility adaptations.
