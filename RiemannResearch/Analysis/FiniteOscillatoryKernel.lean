/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.WeilExplicitFormula.PrimeSideB.PPKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Finite oscillatory kernels and rational frequency separation

Both signed finite-interval endpoints and the exact resonant value are
retained. Mathlib's `integral_exp_mul_complex` proves the nonresonant formula.
The existing proved integer-log spacing lemma in PrimeSideB/PPKernel.lean
gives the uniform rational nonresonant bound 4*n. This is the arithmetic
kernel provider for the sufficient rational Landau contour route; it does
not assert a bound on the complete zeta contour.
-/

open Complex Set Topology Filter Real
open scoped BigOperators

noncomputable section

namespace RiemannResearch.Analysis.ZeroOrdinate

/-- Finite oscillatory exponential kernel with its resonant value retained. -/
def finitePhaseKernel (A B ω : ℝ) : ℂ :=
  if ω = 0 then ((B - A : ℝ) : ℂ) else
    (Complex.exp (((ω : ℂ) * Complex.I) * (B : ℂ)) -
      Complex.exp (((ω : ℂ) * Complex.I) * (A : ℂ))) /
      ((ω : ℂ) * Complex.I)

/-- Exact finite kernel. The nonresonant case is Mathlib's already-used
`integral_exp_mul_complex`, not a new analytic integration argument. -/
theorem integral_phase_eq_finitePhaseKernel (A B ω : ℝ) :
    (∫ t in A..B, Complex.exp (((ω : ℂ) * Complex.I) * (t : ℂ))) =
      finitePhaseKernel A B ω := by
  classical
  by_cases hω : ω = 0
  · simp [finitePhaseKernel, hω]
  · rw [finitePhaseKernel, if_neg hω]
    have hc : ((ω : ℂ) * Complex.I) ≠ 0 := by
      apply mul_ne_zero
      · exact_mod_cast hω
      · exact Complex.I_ne_zero
    exact integral_exp_mul_complex hc

/-- Exact resonant value, kept separate from the nonresonant bound. -/
theorem finitePhaseKernel_zero (A B : ℝ) :
    finitePhaseKernel A B 0 = ((B - A : ℝ) : ℂ) := by
  simp [finitePhaseKernel]

/-- The finite nonresonant exponential integral is bounded by 2/|omega|,
uniformly in both endpoints. -/
theorem norm_finitePhaseKernel_le {ω : ℝ} (hω : ω ≠ 0) (A B : ℝ) :
    ‖finitePhaseKernel A B ω‖ ≤ 2 / |ω| := by
  have hphase : ∀ t : ℝ,
      ‖Complex.exp (((ω : ℂ) * Complex.I) * (t : ℂ))‖ = 1 := by
    intro t
    rw [Complex.norm_exp]
    simp
  have hden : ‖((ω : ℂ) * Complex.I)‖ = |ω| := by
    simp
  rw [finitePhaseKernel, if_neg hω, norm_div, hden]
  calc
    _ ≤ (‖Complex.exp (((ω : ℂ) * Complex.I) * (B : ℂ))‖ +
          ‖Complex.exp (((ω : ℂ) * Complex.I) * (A : ℂ))‖) / |ω| :=
      div_le_div_of_nonneg_right (norm_sub_le _ _) (abs_nonneg ω)
    _ = 2 / |ω| := by rw [hphase, hphase]; norm_num

/-- Rewriting a rational frequency as the difference of two integer logarithms. -/
theorem rationalPhase_frequency_eq {n m k : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hk : 1 ≤ k) :
    Real.log ((n : ℝ) / (m : ℝ)) - Real.log (k : ℝ) =
      Real.log (n : ℝ) - Real.log ((m * k : ℕ) : ℝ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [Real.log_div hn0.ne' hm0.ne', Nat.cast_mul,
    Real.log_mul hm0.ne' hk0.ne']
  ring

/-- Existing integer-log spacing gives separation of every nonresonant
rational Dirichlet-series frequency; no prime-power information is needed. -/
theorem rationalPhase_frequency_separated {n m k : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hk : 1 ≤ k) (hnmk : n ≠ m * k) :
    1 / (2 * (n : ℝ)) ≤
      |Real.log ((n : ℝ) / (m : ℝ)) - Real.log (k : ℝ)| := by
  have hmk : 1 ≤ m * k := by simpa using Nat.mul_le_mul hm hk
  rw [rationalPhase_frequency_eq hn hm hk]
  exact Zeta23.PrimeSide.inv_two_mul_le_abs_log_sub hn hmk hnmk

/-- The sufficient rational nonresonant kernel bound, uniform in k and both
height endpoints. Its 4n loss is harmless for exp(O(sqrt(log T))) ranges. -/
theorem norm_finitePhaseKernel_rational_le {n m k : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hk : 1 ≤ k) (hnmk : n ≠ m * k)
    (A B : ℝ) :
    ‖finitePhaseKernel A B
      (Real.log ((n : ℝ) / (m : ℝ)) - Real.log (k : ℝ))‖ ≤ 4 * (n : ℝ) := by
  let ω : ℝ := Real.log ((n : ℝ) / (m : ℝ)) - Real.log (k : ℝ)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsep : 1 / (2 * (n : ℝ)) ≤ |ω| :=
    rationalPhase_frequency_separated hn hm hk hnmk
  have hω : ω ≠ 0 := by
    intro hzero
    rw [hzero, abs_zero] at hsep
    have hpos : 0 < 1 / (2 * (n : ℝ)) := by positivity
    linarith
  change ‖finitePhaseKernel A B ω‖ ≤ 4 * (n : ℝ)
  calc
    _ ≤ 2 / |ω| := norm_finitePhaseKernel_le hω A B
    _ ≤ 4 * (n : ℝ) := by
      rw [div_le_iff₀ (abs_pos.mpr hω)]
      have hs : 1 ≤ |ω| * (2 * (n : ℝ)) :=
        (div_le_iff₀ (by positivity : 0 < 2 * (n : ℝ))).mp hsep
      nlinarith

/-- The rational resonant term is exactly the interval length, with no
division by its zero frequency. -/
theorem finitePhaseKernel_rational_resonance {n m k : ℕ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hk : 1 ≤ k) (hnmk : n = m * k)
    (A B : ℝ) :
    finitePhaseKernel A B
      (Real.log ((n : ℝ) / (m : ℝ)) - Real.log (k : ℝ)) =
      ((B - A : ℝ) : ℂ) := by
  rw [rationalPhase_frequency_eq hn hm hk, hnmk, sub_self]
  exact finitePhaseKernel_zero A B

end RiemannResearch.Analysis.ZeroOrdinate
