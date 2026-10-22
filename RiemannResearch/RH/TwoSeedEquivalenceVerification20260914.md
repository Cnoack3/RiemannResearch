# Two-seed rigidity: Lean verification and the remaining classical input

Date: 2026-09-14.

The new two-seed converse argument is formalized in the actual Pareto Hilbert
space. Its analytic rigidity obligation has been discharged. The complete
RH equivalence still has one explicit formalization dependency: the classical
strong Báez-Duarte implication from RH to density of the full remainder span.

That classical theorem is established mathematics, but a kernel-checked
provider for it has not been supplied in this project. Defining its proposition
or passing it as a theorem argument does not prove it.

## Main unconditional results

The sequence theorem is

```lean
RiemannResearch.Analysis.multiplicativeSequence_rigidity
  (a : ℕ → ℝ)
  (h2 : ∀ n, 0 < n → a (2*n) = a n)
  (h3 : ∀ n, 0 < n → a (3*n) = a n)
  (hs : Summable (fun n => (a (n+1)-a n)^2)) :
  ∀ n : ℕ, 0 < n → a n = a 1
```

The conclusion deliberately concerns positive integers. The project's
zero coordinate carries zero Pareto mass and is anchored separately.

In `RiemannResearch.RH.Pareto`, the actual Hilbert-space consequences are:

```lean
hilbertDilationAdjoint_two_three_fixed_iff (f : ThresholdHilbert) :
  (hilbertDilationAdjoint 2 (by norm_num) f = f ∧
   hilbertDilationAdjoint 3 (by norm_num) f = f) ↔
  ∃ c : ℝ, f = c • hilbertOne

twoSeed_density_iff_full_density :
  hilbertLegalClosure {2, 3} = ⊤ ↔
  hilbertLegalClosure {n : ℕ | 0 < n} = ⊤
```

These statements have no RH, completeness, tail bound, or rigidity hypothesis
left over beyond the displayed sequence assumptions where applicable.
The second equivalence compares whether the two closed spaces are the whole
Hilbert space. Equality of the two closures when they are proper remains a
separate question.

All positive integer dilation indices are available. The seeds alone are
restricted to 2 and 3. The weights, inner products, adjoints, means, and
variances are the existing complete Pareto quantities, with every infinite
tail and signed mixed term retained.

## What the proof checks

| Module | Verified content |
|---|---|
| `Analysis/DyadicInvariantEnergy.lean` | Dyadic invariance and square-summable increments imply a uniform bound on average prefix square energy. |
| `Analysis/MultiplicativePrefixPrimitive.lean` | Actual normalized floor-prefix sums converge; their limit satisfies a Hölder estimate and exact 2- and 3-homogeneity. |
| `Analysis/PositiveScalingRigidity.lean` | The estimate gives continuity; the existing irrational prime-log period theorem forces the homogeneous limit to be linear. |
| `Analysis/DyadicBlockRecovery.lean` | Exact block-average increments and a bound by the complete increment tail recover every positive integer value. |
| `Analysis/MultiplicativeSequenceRigidity.lean` | Assembles the unconditional sequence rigidity theorem. |
| `RH/ThresholdNormalizedTail.lean` | Defines the actual weighted tails and normalized tails, and proves scaling, exact increments, and constant-vector recovery. |
| `RH/ThresholdDyadicTailSummability.lean` | Genuine dyadic adjoint fixedness implies square-summable tails and normalized-tail increments. A finite positive kernel with column sums at most four supplies the estimate. |
| `RH/ThresholdJointAdjointRigidity.lean` | Proves the genuine joint fixed-space theorem, discharges the rigidity input in the earlier cocycle argument, and proves the full/two-seed density equivalence. |
| `RH/ParetoMeanOneApproximation.lean` | Target membership, legal density, arbitrarily small exact mean-one variance, and a sequence of finite mean-one packets with variance tending to zero are equivalent. |
| `Analysis/DyadicCellRecovery.lean` | Also verifies the original note's shrinking floor-cell lower bound and recovery from the stated quantitative squared-error rate. |
| `RH/ThresholdTwoSeedEquivalence.lean` | Provides the RH equivalences with the sole remaining classical density-from-RH input explicitly stated. |

The main proof uses a continuous prefix primitive. This supplies the limiting
argument from discrete hypotheses and the necessary coordinate recovery.
The original note's complete local-L2/Fourier construction is not needed by
these declarations; its shrinking-cell recovery step is checked separately.

## Exact boundary of the RH equivalence

The remaining input is defined transparently as

```lean
def PositiveResidueDensityFromRH : Prop :=
  RiemannHypothesis → hilbertLegalClosure {n : ℕ | 0 < n} = ⊤
```

The formal endpoint has precisely that hypothesis:

```lean
riemannHypothesis_iff_twoSeed_closure_of_density_from_rh
  (hfull : PositiveResidueDensityFromRH) :
  RiemannHypothesis ↔ hilbertOne ∈ hilbertLegalClosure {2, 3}
```

There are corresponding checked endpoints for full two-seed density and an
actual sequence of finite legal mean-one packets with variance tending to
zero. Joint-adjoint rigidity is a proved dependency of these declarations,
not an additional input.

**Open formalization obligation:** supply a checked declaration of
`PositiveResidueDensityFromRH`. The relevant mathematical source is
[B. Bagchi, *On Nyman, Beurling and Báez-Duarte's Hilbert space reformulation
of the Riemann hypothesis*, Theorem 1](https://arxiv.org/abs/math/0607733).
Its fractional-part sequences differ from this project's remainders only by
nonzero constant factors, so the finite spans coincide.

For Bagchi's proof route, the next substantial arithmetic obligations are
RH-based bounds and convergence for ordered Möbius Dirichlet partial sums,
and a uniform shifted-zeta-ratio bound near the critical line. The available
absolute-summability lemmas for real part greater than one do not supply
these results. Critical-line Mellin norm transport also remains to be joined
to the existing spatial isometry. This dependency assessment does not add
any of these statements as assumptions to the unconditional rigidity theorem.

The converse direction, approximation implying Mathlib's actual
`RiemannHypothesis`, is already proved in `RH/ThresholdRiemannHypothesis.lean`
using Mellin separation. No external criterion is assumed for that direction.

## Verification scope

The assembled sequence rigidity, actual joint-adjoint rigidity, and
two-seed/full-density equivalence passed Lean with exit code 0. Their axiom
lists are exactly `propext`, `Classical.choice`, and `Quot.sound`.
The conditional RH endpoint has the same foundational axiom list, while its
classical density hypothesis remains visible in its type. An axiom audit does
not discharge theorem arguments.

No proof placeholders, project-local axioms, or unsafe declarations were
introduced. All modules are exported from `RiemannResearch.lean` and are
included in the final project checkpoint. No RH proof, unconditional
approximating sequence, or quantitative rate of approximation is claimed.

Source of the new argument: the conversation and
`RH_Iff_Two_Seed_Approximation_20260914.md`. No mathematical novelty or
publication-priority claim is made.
