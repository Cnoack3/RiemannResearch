/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MertensCubeRoot
import RiemannResearch.Analysis.StretchedLogProductIncrement
import RiemannResearch.RH.QSquarefreeVKDisplacement

/-!
# Displacement at the logarithmic-product Mertens scale

For a Mertens estimate with rate `a`, every fixed displacement growth rate
`b < a/2` is admissible. Only the final implication concerns RH; no
pointwise bound on the actual displacement is proved here.
-/
noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QSquarefreeMertensProfileCriterion
open RiemannResearch.Analysis RiemannResearch.NumberTheory.PrimeNumberTheorem
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeDisplacementRigidity

/-- A stretched Mertens estimate permits fixed displacement growth at every
positive rate below half the Mertens rate. The parameter `β` may equal `1/3`. -/
theorem riemannHypothesis_of_logProduct_exponential_displacement
    (β a b C D : ℝ) (hβ : 0 < β) (hβ2 : 2 * β < 1) (hb : 0 < b) (hab : 2*b < a)
    (hM : ∀ᶠ x : ℝ in atTop, |M x| ≤ C * x *
      Real.exp (-a * logProductPower β (6 + Real.log x)))
    (hd : ∀ᶠ n : ℕ in atTop, |qSequence displacement n| ≤ D *
      Real.exp (b * logProductPower β (6 + Real.log (n : ℝ)))) : RiemannHypothesis := by
  let φ : ℝ → ℝ := fun x => logProductPower β (6 + Real.log x)
  have hφ : Tendsto φ atTop atTop := (tendsto_logProductPower_atTop β hβ).comp
    (tendsto_atTop_add_const_left atTop 6 Real.tendsto_log_atTop)
  have hmono : ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ≤ y → φ x ≤ φ y := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx y hxy
    exact logProductPower_mono β hβ.le (by linarith [Real.log_nonneg hx])
      (by linarith only [Real.log_le_log (zero_lt_one.trans_le hx) hxy])
  have hinc (δ : ℝ) (hδ : 0 < δ) : ∀ᶠ x : ℝ in atTop, ∀ y : ℝ, x ≤ y →
      φ y - φ x ≤ δ * (Real.log y - Real.log x) := by
    filter_upwards [shifted_logProductPower_eventual_log_increment β (1 / δ) hβ.le hβ2
      (by positivity)] with x hx y hxy
    have hh := mul_le_mul_of_nonneg_left (hx y hxy) hδ.le
    have hc : δ * (1 / δ) = 1 := by field_simp [hδ.ne']
    rw [← mul_assoc, hc, one_mul] at hh
    exact hh
  let a' : ℝ := (a + 2*b)/2
  have ha' : 0 < a' := by dsimp [a']; linarith
  have hba' : 2*b < a' := by dsimp [a']; linarith
  have h' : a' < a := by dsimp [a']; linarith
  apply riemannHypothesis_of_exponential_profile_displacement φ hφ hmono hinc a' b D
    ha' hb hba' _ hd
  apply mertens_profile_absorb_constant φ hφ a a' C h'
  filter_upwards [hM] with x hx
  simpa only [φ, mul_assoc, mul_left_comm, mul_comm] using hx

/-- The real arithmetic inequality with its implicit prefactor gives a single
positive displacement coefficient at the cube-root scale. -/
theorem exists_riemannHypothesis_of_cubeRoot_displacement_of_M
    (hM : ∃ a > 0, ∃ C ≥ 0, ∀ x : ℝ, 1 ≤ x →
      |M x| ≤ C * x * Real.exp (-a * logProductPower (1 / 3) (6 + Real.log x))) :
    ∃ b : ℝ, 0 < b ∧ ∀ D : ℝ, (∀ᶠ n : ℕ in atTop, |qSequence displacement n| ≤
      D * Real.exp (b * logProductPower (1 / 3) (6 + Real.log (n : ℝ)))) →
        RiemannHypothesis := by
  obtain ⟨a, ha, C, _, hM⟩ := hM
  refine ⟨a/4, by positivity, fun D hd => ?_⟩
  apply riemannHypothesis_of_logProduct_exponential_displacement (1/3) a (a/4) C D
    (by norm_num) (by norm_num) (by positivity) (by linarith) _ hd
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  exact hM x hx

/-- Subexponential displacement growth relative to the cube-root profile
suffices under the same arithmetic estimate. -/
theorem riemannHypothesis_of_cubeRoot_log_displacement_of_M
    (hM : ∃ a > 0, ∃ C ≥ 0, ∀ x : ℝ, 1 ≤ x →
      |M x| ≤ C * x * Real.exp (-a * logProductPower (1 / 3) (6 + Real.log x)))
    (hd : Tendsto (fun n : ℕ => Real.log (2 + |qSequence displacement n|) /
      logProductPower (1/3) (6 + Real.log (n : ℝ))) atTop (𝓝 0)) : RiemannHypothesis := by
  obtain ⟨b, hb, hcrit⟩ := exists_riemannHypothesis_of_cubeRoot_displacement_of_M hM
  apply hcrit 1
  have hL : Tendsto (fun n : ℕ => 6 + Real.log (n : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop 6 (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hΦ := (tendsto_logProductPower_atTop (1/3) (by norm_num)).comp hL
  filter_upwards [hd.eventually (gt_mem_nhds hb), hΦ.eventually (eventually_gt_atTop (0 : ℝ))]
    with n hn hp
  have hlog := Real.exp_le_exp.mpr ((div_lt_iff₀ hp).1 hn).le
  rw [Real.exp_log (by positivity)] at hlog
  simp only [Function.comp_apply] at hlog
  linarith

/-- A single positive growth coefficient for the actual squarefree displacement
at the cube-root scale suffices for RH. -/
theorem exists_riemannHypothesis_of_cubeRoot_displacement :
    ∃ b : ℝ, 0 < b ∧ ∀ D : ℝ, (∀ᶠ n : ℕ in atTop, |qSequence displacement n| ≤
      D * Real.exp (b * logProductPower (1 / 3) (6 + Real.log (n : ℝ)))) →
        RiemannHypothesis :=
  exists_riemannHypothesis_of_cubeRoot_displacement_of_M M_cubeRoot_logProduct

/-- At the unconditional Mertens exponent, only the little-o assumption on
the actual displacement remains. -/
theorem riemannHypothesis_of_cubeRoot_log_displacement
    (hd : Tendsto (fun n : ℕ => Real.log (2 + |qSequence displacement n|) /
      logProductPower (1/3) (6 + Real.log (n : ℝ))) atTop (𝓝 0)) : RiemannHypothesis :=
  riemannHypothesis_of_cubeRoot_log_displacement_of_M M_cubeRoot_logProduct hd


end RiemannResearch.RH.QSquarefreeMertensProfileCriterion
