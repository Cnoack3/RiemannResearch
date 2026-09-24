import RiemannResearch.NumberTheory.PrimeNumberTheorem.Consequences
import RiemannResearch.NumberTheory.PrimeNumberTheorem.Quantitative.MediumPNT
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Inverse-square-log prime-error bound

This consequence combines the project's compatibility adaptation of PNT+
MediumPNT at commit a5154676af9aa3095150ee410cdda80555aa0642 with Mathlib's
`isLittleO_pow_exp_pos_mul_atTop` and the existing `R_locally_bounded` lemma.
The exponent comparison weakens the established exponential error term to the
global bound needed by the subsequent Mobius summation argument.

The combined proof was checked with Lean. The axiom audit for
`R_inverseLogSq_bound` reported only propext, Classical.choice, and Quot.sound.
-/

open Filter Asymptotics
open scoped Topology

namespace RiemannResearch.NumberTheory.PrimeNumberTheorem

lemma Quantitative.exp_log_tenth_eventually_le_inverseLogSq
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop,
      Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) ≤
        4 / (1 + Real.log x) ^ 2 := by
  have hu : Tendsto
      (fun x : ℝ => (Real.log x) ^ ((1 : ℝ) / 10)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : 0 < (1 : ℝ) / 10)).comp
      Real.tendsto_log_atTop
  have hp : ∀ᶠ t : ℝ in atTop,
      ‖t ^ (20 : ℕ)‖ ≤ 1 * ‖Real.exp (c * t)‖ :=
    (isLittleO_pow_exp_pos_mul_atTop 20 hc).bound (by norm_num)
  filter_upwards [hu.eventually hp,
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))]
      with x hpow hlog
  have hlog0 : 0 ≤ Real.log x := le_trans zero_le_one hlog
  have htwenty :
      ((Real.log x) ^ ((1 : ℝ) / 10)) ^ (20 : ℕ) =
        (Real.log x) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlog0]
    norm_num [Real.rpow_natCast]
  have hpower : (Real.log x) ^ 2 ≤
      Real.exp (c * (Real.log x) ^ ((1 : ℝ) / 10)) := by
    simpa only [htwenty, Real.norm_eq_abs, one_mul,
      abs_of_nonneg (sq_nonneg (Real.log x)),
      abs_of_pos (Real.exp_pos _)] using hpow
  have hpoly : (1 + Real.log x) ^ 2 ≤ 4 * (Real.log x) ^ 2 := by
    nlinarith [sq_nonneg (Real.log x - 1)]
  have hexp :
      Real.exp (c * (Real.log x) ^ ((1 : ℝ) / 10)) *
        Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10)) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1 <;> ring
  have hden : 0 < (1 + Real.log x) ^ 2 := by positivity
  apply (le_div_iff₀ hden).2
  have hscaled := mul_le_mul_of_nonneg_right
    (hpoly.trans (mul_le_mul_of_nonneg_left hpower (by norm_num : (0 : ℝ) ≤ 4)))
    (Real.exp_pos (-c * (Real.log x) ^ ((1 : ℝ) / 10))).le
  nlinarith [hscaled, hexp]

theorem R_inverseLogSq_bound_of_medium
    (hMedium : ∃ c > 0,
      (Chebyshev.psi - id) =O[atTop]
        fun x : ℝ => x * Real.exp (-c * (Real.log x) ^ ((1 : ℝ) / 10))) :
    ∃ C > 0, ∀ y : ℝ, 1 ≤ y →
      |R y| ≤ C * y / (1 + Real.log y) ^ 2 := by
  obtain ⟨c, hc, hmedium⟩ := hMedium
  obtain ⟨A, hA, hAbound⟩ := hmedium.exists_pos
  have htail : ∀ᶠ y : ℝ in atTop,
      |R y| ≤ (4 * A) * y / (1 + Real.log y) ^ 2 := by
    have hAbound' : ∀ᶠ y : ℝ in atTop,
        ‖Chebyshev.psi y - y‖ ≤
          A * ‖y * Real.exp (-c * (Real.log y) ^ ((1 : ℝ) / 10))‖ := by
      simpa only [Asymptotics.IsBigOWith, Pi.sub_apply, id_eq] using hAbound
    filter_upwards [hAbound',
      Quantitative.exp_log_tenth_eventually_le_inverseLogSq hc,
      eventually_ge_atTop (1 : ℝ)] with y hbound hdecay hy
    have hy0 : 0 ≤ y := le_trans zero_le_one hy
    have hbound' : |R y| ≤
        A * (y * Real.exp (-c * (Real.log y) ^ ((1 : ℝ) / 10))) := by
      simpa only [R, Psi, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hy0 (Real.exp_pos _).le)] using hbound
    calc
      |R y| ≤ A * (y * Real.exp (-c * (Real.log y) ^ ((1 : ℝ) / 10))) := hbound'
      _ ≤ A * (y * (4 / (1 + Real.log y) ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hdecay hy0) hA.le
      _ = (4 * A) * y / (1 + Real.log y) ^ 2 := by ring
  obtain ⟨T, hT⟩ := eventually_atTop.mp htail
  let B : ℝ := max 1 T
  have hB : 1 ≤ B := le_max_left _ _
  obtain ⟨K, hKbound⟩ := R_locally_bounded B (le_trans zero_le_one hB)
  have hK : 0 ≤ K :=
    (abs_nonneg (R 0)).trans
      (hKbound 0 ⟨le_rfl, le_trans zero_le_one hB⟩)
  let C : ℝ := max (4 * A) (K * (1 + Real.log B) ^ 2)
  have hC : 0 < C := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro y hy
  have hy0 : 0 ≤ y := le_trans zero_le_one hy
  have hden : 0 < (1 + Real.log y) ^ 2 := by
    have := Real.log_nonneg hy
    positivity
  by_cases hTy : T ≤ y
  · exact (hT y hTy).trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hy0) hden.le)
  · have hyB : y ≤ B := (lt_of_not_ge hTy).le.trans (le_max_right _ _)
    have hlog : Real.log y ≤ Real.log B :=
      Real.log_le_log (lt_of_lt_of_le zero_lt_one hy) hyB
    have hlogsq : (1 + Real.log y) ^ 2 ≤ (1 + Real.log B) ^ 2 := by
      have := Real.log_nonneg hy
      gcongr <;> first | exact hlog | exact hyB | positivity
    apply (le_div_iff₀ hden).2
    calc
      |R y| * (1 + Real.log y) ^ 2 ≤ K * (1 + Real.log y) ^ 2 :=
        mul_le_mul_of_nonneg_right (hKbound y ⟨hy0, hyB⟩) hden.le
      _ ≤ K * (1 + Real.log B) ^ 2 :=
        mul_le_mul_of_nonneg_left hlogsq hK
      _ ≤ C := le_max_right _ _
      _ ≤ C * y := le_mul_of_one_le_right hC.le hy

theorem R_inverseLogSq_bound :
    ∃ C > 0, ∀ y : ℝ, 1 ≤ y →
      |R y| ≤ C * y / (1 + Real.log y) ^ 2 :=
  R_inverseLogSq_bound_of_medium Quantitative.MediumPNT

#print axioms R_inverseLogSq_bound

end RiemannResearch.NumberTheory.PrimeNumberTheorem
