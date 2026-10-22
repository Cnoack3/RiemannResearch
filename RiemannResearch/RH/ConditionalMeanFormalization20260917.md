# Conditional iid / Cesàro: Lean formalization record

Date: 2026-09-17.

This record distinguishes the new Lean declarations from the mathematical source. The complete source is preserved as `Conditional_IID_Cesaro_Mathematical_Completion_2026-09-17.md`. That document is not itself a machine-checked proof.

## New modules

| Module | Formalized result |
|---|---|
| `RH/ConditionalMeanHeadMinimum.lean` | Unconditional interpolation of every finite positive-coordinate head in the actual legal span; nonempty energy sets; genuine real infima; approximate minimizers; monotonicity; exact head/tail energy decomposition; lower bound N/(N+2); explicit error bound 8/(N+2) for energy-at-most-one witnesses; equivalence between uniform infimum bounds and bounded actual witnesses; uniform infimum bounds imply actual mathlib `RiemannHypothesis`. |
| `RH/CesaroResidueMean.lean` | Exact quotient/remainder formula for the existing normalized residue generators and existing Cesàro mean; complete-period means; nonnegativity and the upper bound 1/2. |
| `RH/ConditionalMeanCorrectionObstruction.lean` | Actual finite conditional-mean correction energies: naive affine-head error at least α²Y/3 and floor-window single-repair error at least β⁵/(9216 D⁴), including the counting-source specialization. |
| `Analysis/FiniteHilbertConstraints.lean` | Actual inverse-Gram constrained minimizer from linearly independent observation vectors; exact energy, signed Pythagorean completion, uniqueness, positivity, and attained minimum. |
| `Analysis/FiniteConstraintClosure.lean` | Exact affine-constraint repair, convergence, and equality of constrained closures, given an actual continuous linear right inverse into the algebraic subspace. |

The infimum theorem uses `conditionalHeadClass`, based on the project's `legalSeedSpan (Set.Ici 1)` and actual `conditionalMeanSquare`. Its finite witnesses are constructed, not postulated. The boundedness premise is substantive and is not proved by the theorem.

The inverse-Gram theorem uses the existing `FiniteHilbertGram.gramEquiv`, whose invertibility follows from linear independence. It preserves signed inner products. The coefficient-space identification with the concrete arithmetic matrix A G⁻¹ Aᵀ is not supplied by the abstract Hilbert theorem.

The closure theorem exposes the continuous right-inverse hypothesis. This file does not construct the concrete J-space observation operator or its right inverse.

## Verification and assumptions

Development uses serialized Lean checks. The publication checkpoint must verify the new modules with their declared imports and the affected project import graph. Successful ephemeral checks are development evidence; successful checkpoint completion establishes the saved project result. Representative declarations are audited with `#print axioms`. Expected foundational dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.

There is no custom RH axiom, no proof placeholder, and no unconditional proof of RH in these additions. In particular:

```lean
riemannHypothesis_of_bounded_conditionalHeadMinimum
  (h : ∃ C : ℝ, ∀ N, conditionalHeadMinimum N ≤ C) : RiemannHypothesis
```

The premise is an unresolved arithmetic estimate. It is distinct from the classical reverse formalization obligation below.

## Remaining mathematical and formalization obligations

1. **Classical reverse provider.** `RH/ThresholdTwoSeedEquivalence.lean` defines `PositiveResidueDensityFromRH`, but the audited project has no proof of it. Hence RH ⇒ density, RH ⇒ E_N=N/(N+2), and the full variational equivalence are not established by the new Lean modules.
2. **Arithmetic strength.** A uniform or cofinal subpolynomial bound for actual signed constrained energies remains unproved. The already available subpolynomial-to-RH implication does not furnish this bound.
3. **Canonical Möbius quantitative construction.** The new finite interpolation is unconditional, but the source's particular Möbius coefficients, bound |m_Y|≤1, and E_Y<2Y are not yet fully assembled in Lean.
4. **Concrete finite-generator minimization.** Identification of the actual arithmetic head and Gram matrices with the abstract constrained minimum, their full rank and tail positive definiteness, and the exact concrete Schur formula remain to be assembled. Existing generic signed Gram and Schur identities are not substitutes for this specialization.
5. **Operator packaging and generality.** A bundled C:H→J operator, dense/nonclosed range, the explicit adjoint and Markov kernel, and the all-H (potentially unbounded) second-difference Mellin pairing remain beyond the audited declarations. The existing bounded-legal-witness pairing suffices for the established actual RH implications.
6. **Probability extensions.** The actual infinite conditional-iid model is already present. The completion's exchangeability, eventual latent recovery, simultaneous strong-law statements, explicit divisibility formulas, and exact diagonal sample-size rate are not all assembled as Lean declarations.
7. **Variational refinements.** Nonattainment in the algebraic legal span and the concrete RH-conditional optimal-infimum theorem remain outside this addition.

The accompanying `ConditionalMeanCoverageAudit.md` identifies existing declarations and precise hypotheses for the probability and Mellin portions. It is a source audit, not a claim to have recompiled every pre-existing theorem separately.
