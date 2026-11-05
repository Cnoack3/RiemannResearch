/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QSquarefreeVKDisplacement
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MertensClassicalContour

/-! # Squarefree displacement at the square-root logarithmic Mertens scale -/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QSquarefreeMertensProfileCriterion
open RiemannResearch.NumberTheory.PrimeNumberTheorem
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeDisplacementRigidity

/-- Every displacement growth rate below half the square-root Mertens rate suffices. -/
theorem riemannHypothesis_of_sqrtLog_exponential_displacement
    (a b C D : ℝ) (hb : 0 < b) (hba : 2 * b < a)
    (hM : ∀ᶠ x : ℝ in atTop, |M x| ≤ C * x * Real.exp (-a * Real.sqrt (Real.log x)))
    (hd : ∀ᶠ n : ℕ in atTop, |qSequence displacement n| ≤
      D * Real.exp (b * Real.sqrt (Real.log (n : ℝ)))) : RiemannHypothesis := by
  let φ : ℝ → ℝ := fun x => Real.sqrt (Real.log x)
  have hφ : Tendsto φ atTop atTop := Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have hm : ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ≤ y → φ x ≤ φ y := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx y hxy
    exact Real.sqrt_le_sqrt (Real.log_le_log (zero_lt_one.trans_le hx) hxy)
  have hi (δ : ℝ) (hδ : 0 < δ) : ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ≤ y →
      φ y - φ x ≤ δ * (Real.log y - Real.log x) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), hm,
      (Tendsto.const_mul_atTop hδ hφ).eventually (eventually_ge_atTop 1)] with x hx hmono hlarge y hxy
    have hden : 1 ≤ δ * (φ y + φ x) :=
      hlarge.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.sqrt_nonneg _)) hδ.le)
    have he : (φ y + φ x) * (φ y - φ x) = Real.log y - Real.log x := by
      dsimp only [φ]
      nlinarith only [Real.sq_sqrt (Real.log_nonneg hx), Real.sq_sqrt (Real.log_nonneg (hx.trans hxy))]
    simpa only [one_mul, mul_assoc, he] using
      mul_le_mul_of_nonneg_right hden (sub_nonneg.mpr (hmono y hxy))
  let a' : ℝ := (a + 2 * b) / 2
  apply riemannHypothesis_of_exponential_profile_displacement φ hφ hm hi a' b D
    (by dsimp [a']; linarith) hb (by dsimp [a']; linarith) _ hd
  apply mertens_profile_absorb_constant φ hφ a a' C (by dsimp [a']; linarith)
  filter_upwards [hM] with x hx
  simpa only [φ, mul_assoc, mul_left_comm, mul_comm] using hx

/-- A little-o condition on the logarithm of displacement suffices at this rate. -/
theorem riemannHypothesis_of_sqrtLog_log_displacement_of_M
    (a C : ℝ) (ha : 0 < a)
    (hM : ∀ᶠ x : ℝ in atTop, |M x| ≤ C * x * Real.exp (-a * Real.sqrt (Real.log x)))
    (hd : Tendsto (fun n : ℕ => Real.log (2 + |qSequence displacement n|) /
      Real.sqrt (Real.log (n : ℝ))) atTop (𝓝 0)) : RiemannHypothesis := by
  let b : ℝ := a / 4
  have hb : 0 < b := by dsimp [b]; positivity
  apply riemannHypothesis_of_sqrtLog_exponential_displacement a b C 1 hb
    (by dsimp [b]; linarith) hM
  have hΦ : Tendsto (fun n : ℕ => Real.sqrt (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hd.eventually (gt_mem_nhds hb), hΦ.eventually (eventually_gt_atTop 0)] with n hn hp
  have hlog := Real.exp_le_exp.mpr ((div_lt_iff₀ hp).1 hn).le
  rw [Real.exp_log (by positivity)] at hlog
  linarith

open Asymptotics

/-- The little-o displacement condition consumes the customary big-O version
of the ordinary Mertens estimate directly. -/
theorem riemannHypothesis_of_sqrtLog_log_displacement_of_isBigO
    (hM : ∃ a > 0, M =O[atTop] fun x : ℝ => x * Real.exp (-a * Real.sqrt (Real.log x)))
    (hd : Tendsto (fun n : ℕ => Real.log (2 + |qSequence displacement n|) /
      Real.sqrt (Real.log (n : ℝ))) atTop (𝓝 0)) : RiemannHypothesis := by
  obtain ⟨a, ha, hM⟩ := hM
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hM
  apply riemannHypothesis_of_sqrtLog_log_displacement_of_M a C ha _ hd
  filter_upwards [hC, eventually_ge_atTop (0 : ℝ)] with x hm hx
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hx,
    abs_of_pos (Real.exp_pos _), mul_assoc] using hm

/-- The ordinary Mertens estimate has already been discharged, so growth
of the actual displacement is the sole hypothesis of this implication. -/
theorem riemannHypothesis_of_sqrtLog_log_displacement
    (hd : Tendsto (fun n : ℕ => Real.log (2 + |qSequence displacement n|) /
      Real.sqrt (Real.log (n : ℝ))) atTop (𝓝 0)) : RiemannHypothesis :=
  riemannHypothesis_of_sqrtLog_log_displacement_of_isBigO M_isBigO_exp_neg_sqrt_log hd

/-- A fixed positive growth rate below one quarter of the square root of the
certified strip width is admissible for the actual displacement. -/
theorem riemannHypothesis_of_sqrtLog_displacement_at_rate (b D : ℝ) (hb : 0 < b)
    (hba : 2 * b < Quantitative.MobiusContour.contourEndpoint)
    (hd : ∀ᶠ n : ℕ in atTop, |qSequence displacement n| ≤
      D * Real.exp (b * Real.sqrt (Real.log (n : ℝ)))) : RiemannHypothesis := by
  obtain ⟨a, hga, haq⟩ := exists_between hba
  obtain ⟨B, _, hM⟩ := M_sqrt_log_global_of_lt_contourEndpoint a (by linarith) haq
  apply riemannHypothesis_of_sqrtLog_exponential_displacement a b B D hb hga _ hd
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  exact hM x hx

end RiemannResearch.RH.QSquarefreeMertensProfileCriterion
