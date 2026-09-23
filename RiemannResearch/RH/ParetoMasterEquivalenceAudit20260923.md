# Pareto master equivalence: Lean verification audit

Date: 2026-09-23.

Source: user-provided *Exact Pareto Minimizers and the Master Equivalence*,
uploaded as `Pareto_Master_Equivalence (1).pdf`, dated September 23, 2026.
The source supports the mathematical statements and proof strategy audited here.
PDF SHA-256: `a4fb053e59b0193e3265b0b878f820ca4f0d8a688b2134d2ba79b17ba6d482b8`.

## Conclusion and open obligation

The document does not provide an unconditional proof of RH. Its abstract,
page 5, equation (25), and page 9 explicitly retain the same unresolved assertion:

```math
\forall d\ge2,\qquad c_{\infty,d}=-\mu(d).
```

Unconditional existence of every fixed coefficient limit is established.
Identifying those limits with these specified values is not established.
The exact finite identity
`c_N = -mu_N + G_N^{-1}(b_N + G_N mu_N)` does not discharge the
limit-identification obligation.

The master equivalence and the forward implication to Mathlib's actual
`RiemannHypothesis` are supported by the existing Lean project:

```math
[\forall d\ge2,\ c_{N,d}\longrightarrow-\mu(d)]
\iff \|\mathbf1-F_N\|_P\longrightarrow0
\iff Q_N\longrightarrow1
\iff \mathbf1\in\overline{\bigcup_N V_N},
```

and each of these equivalent conditions implies RH.
These equivalences do not assert that any of their conditions holds.

The cited reverse implication RH => closure membership, at the end of the
PDF, is not needed for this audit and was not newly formalized here.

## Indexing and mathematical identification

The project uses stage `n = N - 1`; `residueAtom i` represents `g_(i+2)`.
It uses the entire Pareto norm with weights `1/(k*(k+1))`, not a finite
truncation of that norm. The coefficient functions extend to all stages;
the fixed-coordinate limits agree with the manuscript once its coordinate
is inside the finite span.

| Document quantity | Existing Lean expression |
|---|---|
| F_N | `projection (N - 1)` |
| c_(N,d) | `coefficient (N - 1) d` |
| c_(infinity,d) | `limitCoefficient d` |
| Q_N | `ProjectionSchur.captured (N - 1)` |
| limiting residual r | `limitResidual` |
| squared norm of r | `limitEnergy` |
| G_N inverse correction | `GramMobiusCorrection.correctionVector (N - 1)` |

The base namespace is
`RiemannResearch.RH.Pareto.CoefficientStabilization`.

## Existing declarations audited

| Document component | Declaration and module |
|---|---|
| Unconditional projection convergence | `projection_tendsto`, `MobiusCoefficientStabilization.lean` |
| Unconditional fixed coefficient convergence | `coefficient_tendsto`, same module |
| Möbius limit identification iff residual zero | `limitCoefficients_eq_mobius_iff_residual_zero`, same module |
| Coefficient convergence implies RH, conditionally | `riemannHypothesis_of_coefficients_tendsto_mobius`, same module |
| Norm convergence iff closure membership | `projection_norm_tendsto_zero_iff_mem`, `ParetoNormClosure.lean` |
| Exact finite Möbius correction | `canonical_mobius_decomposition`, `ResidueGramMobiusCorrection.lean` |
| Correction decay iff norm convergence | `correction_limits_iff_norm`, same module |
| Unique finite minimizer | `canonical_unique`, `ResidueProjectionSchur.lean` |
| Exact complete Gram formula | `normalizedResidueHilbert_inner_digamma`, `ResidueGramDigamma.lean` |
| Exact Schur recurrence | `captured_schur_step`, `ResidueProjectionSchur.lean` |
| Q limit iff coefficient convergence to Möbius values | `captured_tendsto_one_iff_coefficients_tendsto_mobius`, `ResidueSchurLimits.lean` |
| Absolute convergence of coefficient increments | `coefficient_total_variation_summable`, same module |
| Schur tail sum after conductor two | `schur_gain_after_two_hasSum`, same module |

The Mellin implication is supplied by `ThresholdRiemannHypothesis.lean`,
including the explicit exclusion `s ≠ 1` for the pole and the reflection
argument for zeros in the critical strip. No external RH criterion is an
assumption in that forward bridge.

## Exact reproducible verification submission

The following is an audit snippet, not a new permanent API alias.
It reuses existing proved declarations and asserts the full conditional chain.

```lean
import RiemannResearch.RH.ResidueSchurLimits

open Filter
open scoped Topology
open RiemannResearch.RH.Pareto
open RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.RH.Pareto.CoefficientStabilization.ProjectionSchur

-- Manuscript N corresponds to project stage n = N - 1.
-- This checks the exact master chain without assuming any condition is true.
theorem document_master_equivalence_audit :
    ((∀ d : ℕ, 1 < d →
        Tendsto (fun n => coefficient n d) atTop
          (𝓝 (-(ArithmeticFunction.moebius d : ℝ)))) ↔
      Tendsto (fun n => ‖hilbertOne - projection n‖) atTop (𝓝 0)) ∧
    (Tendsto (fun n => ‖hilbertOne - projection n‖) atTop (𝓝 0) ↔
      Tendsto captured atTop (𝓝 1)) ∧
    (Tendsto captured atTop (𝓝 1) ↔ hilbertOne ∈ closedSpace) ∧
    (Tendsto captured atTop (𝓝 1) → RiemannHypothesis) := by
  refine ⟨?_, captured_tendsto_one_iff_norm.symm, ?_,
    riemannHypothesis_of_captured_tendsto_one⟩
  · exact captured_tendsto_one_iff_coefficients_tendsto_mobius.symm.trans
      captured_tendsto_one_iff_norm
  · exact captured_tendsto_one_iff_norm.trans projection_norm_tendsto_zero_iff_mem

#print axioms document_master_equivalence_audit
#check coefficient_tendsto
#check riemannHypothesis_of_coefficients_tendsto_mobius
#print axioms coefficient_tendsto
#print axioms projection_tendsto
#print axioms GramMobiusCorrection.canonical_mobius_decomposition
#print axioms GramMobiusCorrection.correction_limits_iff_norm
#print axioms canonical_unique
#print axioms normalizedResidueHilbert_inner_digamma
#print axioms captured_schur_step
#print axioms coefficient_total_variation_summable
#print axioms limitCoefficients_eq_mobius_iff_residual_zero
#print axioms riemannHypothesis_of_coefficients_tendsto_mobius
#print axioms schur_gain_after_two_hasSum
```

## Verification record

Base project commit: `c6c1161c0327af126f0fce513e7432880e3104a1`.
Workspace: `ws_uMgKeME0VSNytaSCZn2WbXifPdUh-vFV`.
Verification job: `job_n31_KfzDzAXyZ-YM3mUPYJEUdDl0MZ9H`.

Outcome: `succeeded`; `verified: true`; exit code `0`; elapsed 19.707 seconds.
No output truncation. The audit snippet and every listed axiom query returned
only `propext`, `Classical.choice`, and `Quot.sound`. No `sorryAx` or
project-specific axiom occurred in these dependencies.

The exact checked RH theorem type still has the substantive argument:

```lean
(h : ∀ m : ℕ, 1 < m →
  Tendsto (fun n => coefficient n m) atTop
    (𝓝 (-(ArithmeticFunction.moebius m : ℝ)))) :
  RiemannHypothesis
```

Axiom inspection does not discharge this explicit hypothesis.
The isolated snippet verifies the stated equivalences and conditional
implication. It is not an unconditional RH proof, and the documentation
checkpoint does not turn it into one.

No new mathematical theorem or change of open-obligation status is claimed.
The permanent reusable declarations remain in their existing subject modules.
