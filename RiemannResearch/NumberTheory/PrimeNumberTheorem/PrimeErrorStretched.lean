/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.NumberTheory.PrimeNumberTheorem.PrimeErrorInverseLogSq
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! The established MediumPNT supplies a uniform stretched-exponential
prime-error provider while reserving the reciprocal-square-log weight
needed by the finite signed head estimate. No arithmetic hypothesis is added. -/

noncomputable section
open Filter Asymptotics
open scoped Topology

namespace RiemannResearch.NumberTheory.PrimeNumberTheorem

/-- Any positive stretched-exponential rate absorbs the square-log weight. -/
private theorem exp_stretched_eventually_le_four_div_logSq (α b : ℝ)
    (hα : 0 < α) (hb : 0 < b) :
    ∀ᶠ y : ℝ in atTop, Real.exp (-b * (Real.log y) ^ α) ≤ 4 / (1 + Real.log y) ^ 2 := by
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2/α) b hb).comp
    ((tendsto_rpow_atTop hα).comp Real.tendsto_log_atTop)
  filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ)),
    (tendsto_order.1 hlim).2 1 (by norm_num)] with y hy hdecay
  change ((Real.log y) ^ α) ^ (2/α) * Real.exp (-b * (Real.log y) ^ α) < 1 at hdecay
  have hlog : 0 < Real.log y := zero_lt_one.trans_le hy
  have hpow : ((Real.log y) ^ α) ^ (2/α) = (Real.log y) ^ 2 := by
    rw [← Real.rpow_mul hlog.le,
      show α*(2/α) = (2 : ℝ) by field_simp [hα.ne'] <;> ring,
      Real.rpow_two]
  rw [hpow] at hdecay
  have hsquare : (1 + Real.log y) ^ 2 ≤ 4 * (Real.log y) ^ 2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hy) (by linarith : 0 ≤ 3*Real.log y+1)]
  have hmul := mul_le_mul_of_nonneg_right hsquare (Real.exp_pos (-b * (Real.log y) ^ α)).le
  apply (le_div_iff₀ (by positivity : 0 < (1 + Real.log y) ^ 2)).mpr
  nlinarith only [hmul, hdecay]

/-- Every smaller positive coefficient in a stretched Chebyshev estimate
survives reserving the square-log weight needed by the finite Möbius sum. -/
theorem R_stretched_squareLog_bound_at_rate (α a c : ℝ) (hα : 0 < α)
    (hc : 0 < c) (hca : c < a)
    (hmedium : (Chebyshev.psi - id) =O[atTop]
      fun x : ℝ => x * Real.exp (-a * (Real.log x) ^ α)) :
    ∃ D > 0, ∀ y : ℝ, 1 ≤ y → |R y| ≤
      D * y * Real.exp (-c * (Real.log y) ^ α) / (1 + Real.log y) ^ 2 := by
  obtain ⟨A, hA, hAbound⟩ := hmedium.exists_pos
  have htail : ∀ᶠ y : ℝ in atTop,
      |R y| ≤ (4 * A) * y *
        Real.exp (-c * (Real.log y) ^ α) /
          (1 + Real.log y) ^ 2 := by
    have hAbound' : ∀ᶠ y : ℝ in atTop,
        ‖Chebyshev.psi y - y‖ ≤
          A * ‖y * Real.exp (-a * (Real.log y) ^ α)‖ := by
      simpa only [Asymptotics.IsBigOWith, Pi.sub_apply, id_eq] using hAbound
    filter_upwards [hAbound',
      exp_stretched_eventually_le_four_div_logSq α (a-c) hα (sub_pos.mpr hca),
      eventually_ge_atTop (1 : ℝ)] with y hbound hdecay hy
    have hy0 : 0 ≤ y := le_trans zero_le_one hy
    have hbound' : |R y| ≤
        A * (y * Real.exp (-a * (Real.log y) ^ α)) := by
      simpa only [R, Psi, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hy0 (Real.exp_pos _).le)] using hbound
    have hsplit :
        Real.exp (-a * (Real.log y) ^ α) =
          Real.exp (-(a-c) * (Real.log y) ^ α) *
          Real.exp (-c * (Real.log y) ^ α) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      |R y| ≤ A * (y * Real.exp (-a * (Real.log y) ^ α)) := hbound'
      _ = (A * y) * (Real.exp (-(a-c) * (Real.log y) ^ α) *
          Real.exp (-c * (Real.log y) ^ α)) := by rw [hsplit]; ring
      _ ≤ (A * y) * ((4 / (1 + Real.log y) ^ 2) *
          Real.exp (-c * (Real.log y) ^ α)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hdecay (Real.exp_pos _).le) (mul_nonneg hA.le hy0)
      _ = (4 * A) * y * Real.exp (-c * (Real.log y) ^ α) /
          (1 + Real.log y) ^ 2 := by ring
  obtain ⟨T, hT⟩ := eventually_atTop.mp htail
  let B : ℝ := max 1 T
  have hB : 1 ≤ B := le_max_left _ _
  obtain ⟨K, hKbound⟩ := R_locally_bounded B (le_trans zero_le_one hB)
  have hK : 0 ≤ K :=
    (abs_nonneg (R 0)).trans
      (hKbound 0 ⟨le_rfl, le_trans zero_le_one hB⟩)
  let D : ℝ := max (4 * A) (K * (1 + Real.log B) ^ 2 *
    Real.exp (c * (Real.log B) ^ α))
  have hD : 0 < D := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨D, hD, ?_⟩
  intro y hy
  have hy0 : 0 ≤ y := le_trans zero_le_one hy
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one hy
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy
  have hden : 0 < (1 + Real.log y) ^ 2 := by positivity
  by_cases hTy : T ≤ y
  · apply (hT y hTy).trans
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hy0)
        (Real.exp_pos _).le) hden.le
  · have hyB : y ≤ B := (lt_of_not_ge hTy).le.trans (le_max_right _ _)
    have hlog : Real.log y ≤ Real.log B := Real.log_le_log hypos hyB
    have hlogsq : (1 + Real.log y) ^ 2 ≤ (1 + Real.log B) ^ 2 := by
      gcongr <;> first | exact hlog | exact hyB | positivity
    have hrpow : (Real.log y) ^ α ≤
        (Real.log B) ^ α :=
      Real.rpow_le_rpow hlogy hlog (by linarith)
    have hexpmono :
        Real.exp (c * (Real.log y) ^ α) ≤
          Real.exp (c * (Real.log B) ^ α) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hrpow hc.le)
    have hweight : (1 + Real.log y) ^ 2 *
          Real.exp (c * (Real.log y) ^ α) ≤
        (1 + Real.log B) ^ 2 *
          Real.exp (c * (Real.log B) ^ α) :=
      mul_le_mul hlogsq hexpmono (Real.exp_pos _).le (sq_nonneg _)
    have hm : |R y| * (1 + Real.log y) ^ 2 *
        Real.exp (c * (Real.log y) ^ α) ≤ D * y := by
      calc
        _ ≤ K * (1 + Real.log y) ^ 2 *
            Real.exp (c * (Real.log y) ^ α) := by
          gcongr
          exact hKbound y ⟨hy0, hyB⟩
        _ = K * ((1 + Real.log y) ^ 2 *
            Real.exp (c * (Real.log y) ^ α)) := by ring
        _ ≤ K * ((1 + Real.log B) ^ 2 *
            Real.exp (c * (Real.log B) ^ α)) :=
          mul_le_mul_of_nonneg_left hweight hK
        _ = K * (1 + Real.log B) ^ 2 *
            Real.exp (c * (Real.log B) ^ α) := by ring
        _ ≤ D := le_max_right _ _
        _ ≤ D * y := le_mul_of_one_le_right hD.le hy
    have hexp :
        Real.exp (c * (Real.log y) ^ α) *
          Real.exp (-c * (Real.log y) ^ α) = 1 := by
      rw [← Real.exp_add]
      convert Real.exp_zero using 1 <;> ring
    apply (le_div_iff₀ hden).2
    have hh := mul_le_mul_of_nonneg_right hm
      (Real.exp_pos (-c * (Real.log y) ^ α)).le
    simpa only [mul_assoc, hexp, mul_one] using hh

/-- Existential-coefficient interface used by the original MediumPNT bootstrap. -/
theorem R_stretched_squareLog_bound_of_medium_rpow
    (α : ℝ) (hα : (1 : ℝ) / 10 ≤ α)
    (hMedium : ∃ c > 0,
      (Chebyshev.psi - id) =O[atTop]
        fun x : ℝ => x * Real.exp (-c * (Real.log x) ^ α)) :
    ∃ c > 0, ∃ D > 0, ∀ y : ℝ, 1 ≤ y →
      |R y| ≤ D * y *
        Real.exp (-c * (Real.log y) ^ α) /
          (1 + Real.log y) ^ 2 := by
  obtain ⟨a, ha, h⟩ := hMedium
  exact ⟨a/2, half_pos ha,
    R_stretched_squareLog_bound_at_rate α a (a/2) (by linarith) (half_pos ha) (by linarith) h⟩

theorem R_stretched_squareLog_bound_of_medium
    (hMedium : ∃ c > 0,
      (Chebyshev.psi - id) =O[atTop]
        fun x : ℝ => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) :
    ∃ c > 0, ∃ D > 0, ∀ y : ℝ, 1 ≤ y →
      |R y| ≤ D * y *
        Real.exp (-c * (Real.log y) ^ ((1 : ℝ) / 10)) /
          (1 + Real.log y) ^ 2 :=
  R_stretched_squareLog_bound_of_medium_rpow (1 / 10) le_rfl hMedium

theorem R_stretched_squareLog_bound :
    ∃ c > 0, ∃ D > 0, ∀ y : ℝ, 1 ≤ y →
      |R y| ≤ D * y *
        Real.exp (-c * (Real.log y) ^ ((1 : ℝ) / 10)) /
          (1 + Real.log y) ^ 2 :=
  R_stretched_squareLog_bound_of_medium Quantitative.MediumPNT

end RiemannResearch.NumberTheory.PrimeNumberTheorem
