/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.GaussianHankelInterpolation
import RiemannResearch.Analysis.GaussianGrowingDegreeTail

/-!
The growing-degree Gaussian limit applied to exact polynomial-square witnesses.

The radius is real and all cutoff, summability, core, and numerical tail
hypotheses may hold only eventually.  Actual zero-counting and polynomial-growth
providers are explicit hypotheses.  This module does not assert those providers
for the zeta-zero spectrum or assert its infinite Hankel positivity.
-/

noncomputable section

namespace RiemannResearch.Analysis.GaussianHankelTailBridge

open scoped BigOperators Topology Polynomial
open Filter
open RiemannResearch.Analysis.GaussianHankelInterpolation
open RiemannResearch.Analysis.GaussianGrowingDegreeTail

/-- The numerical envelope whose limit has already been proved. -/
def tailEnvelope (a K : ℝ) (d : ℝ → ℕ) (T : ℝ) : ℝ :=
  K * (9 : ℝ) ^ d T * (T ^ 2 + 1 / 4) ^ (d T + 1) *
    Real.exp (-a * T ^ 2) * (T + 1) * Real.log (T + 3)

/--
A uniform negative finite core survives a summable absolute tail bounded by the
proved Gaussian envelope.  No convergence of the changing-polynomial tail is
assumed separately.
-/
theorem not_polynomialSquareNonneg_of_core_and_growing_degree_tail
    (w : ℂ → ℂ) (s : ℝ → Finset ℂ) (p : ℝ → ℝ[X])
    (η a K : ℝ) (d : ℝ → ℕ) (hη : 0 < η) (ha : 0 < a) (hK : 0 ≤ K)
    (hdegree : Tendsto (fun T : ℝ => (d T : ℝ) * Real.log T / T ^ 2)
      atTop (𝓝 0))
    (hcore : ∀ᶠ T in atTop, (∑ u ∈ s T, squareTerm w (p T) u) ≤ -η)
    (hsum : ∀ᶠ T in atTop, Summable (absoluteSquareTerm w (p T)))
    (hbound : ∀ᶠ T in atTop,
      (∑' u : {u // u ∉ s T}, absoluteSquareTerm w (p T) u) ≤
        tailEnvelope a K d T) : ¬ PolynomialSquareNonneg w := by
  have hlimit : Tendsto (tailEnvelope a K d) atTop (𝓝 0) := by
    exact tendsto_globalCountTailEnvelope_subquadratic a K ha hK d hdegree
  have hsmall : ∀ᶠ T in atTop, tailEnvelope a K d T < η :=
    hlimit.eventually (isOpen_Iio.mem_nhds hη)
  have hbudget : ∀ᶠ T in atTop,
      (∑' u : {u // u ∉ s T}, absoluteSquareTerm w (p T) u) <
        -(∑ u ∈ s T, squareTerm w (p T) u) := by
    filter_upwards [hcore, hbound, hsmall] with T hc hb hsmallT
    linarith
  obtain ⟨T, hsumT, hbudgetT⟩ := (hsum.and hbudget).exists
  exact not_polynomialSquareNonneg_of_absolute_complex_tail_budget
    w (s T) (p T) hsumT hbudgetT

/--
The conditional full infinite converse for a nonreal target pair.  The envelope
constant may depend on the assigned negative value.  Both target memberships
and absolute summability are required only eventually in the real radius.
-/
theorem not_polynomialSquareNonneg_of_nonreal_pair_and_growing_degree_tail
    (w : ℂ → ℂ) (s : ℝ → Finset ℂ) {z : ℂ} (hz : z.im ≠ 0)
    (hzin : ∀ᶠ T in atTop, z ∈ s T)
    (hzcin : ∀ᶠ T in atTop, (starRingEnd ℂ) z ∈ s T)
    (hw : w ((starRingEnd ℂ) z) = (starRingEnd ℂ) (w z)) (hw0 : w z ≠ 0)
    (a : ℝ) (ha : 0 < a) (d : ℝ → ℕ)
    (hdegree : Tendsto (fun T : ℝ => (d T : ℝ) * Real.log T / T ^ 2)
      atTop (𝓝 0))
    (hprovider : ∀ ξ : ℂ, 2 * (w z * ξ ^ 2).re < 0 →
      ∃ K : ℝ, 0 ≤ K ∧
        (∀ᶠ T in atTop,
          Summable (absoluteSquareTerm w (cutoffInterpolant (s T) z ξ))) ∧
        (∀ᶠ T in atTop,
          (∑' u : {u // u ∉ s T},
            absoluteSquareTerm w (cutoffInterpolant (s T) z ξ) u) ≤
              tailEnvelope a K d T)) : ¬ PolynomialSquareNonneg w := by
  obtain ⟨ξ, hξ⟩ := exists_negative_pair_value hw0 hz
  obtain ⟨K, hK, hsum, hbound⟩ := hprovider ξ hξ
  apply not_polynomialSquareNonneg_of_core_and_growing_degree_tail
    w s (fun T => cutoffInterpolant (s T) z ξ)
    (-(2 * (w z * ξ ^ 2).re)) a K d (neg_pos.mpr hξ) ha hK hdegree
    ?_ hsum hbound
  filter_upwards [hzin, hzcin] with T hzT hzcT
  rw [cutoffInterpolant_core w (s T) hz hzT hzcT hw ξ]
  simp

end RiemannResearch.Analysis.GaussianHankelTailBridge
