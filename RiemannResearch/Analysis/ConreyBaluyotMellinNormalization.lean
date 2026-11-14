/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotMellinShift
import RiemannResearch.Analysis.ConreyBaluyotMellinDecay
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Uniform normalization and coefficient bounds for the actual mollifier

Source: S. A. C. Baluyot, *On the Zeros of Riemann's Zeta-function*
(2017), Lemma 3.1.1, pp. 94--95:
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320 .

The actual secondary coefficient tends to -1. The signed contour expansion
then gives one positive normalization bound on a coupled logarithmic strip,
with constants chosen before sigma and y. The actual coefficients have first
coefficient 1, a uniform bound, and an explicit exponential tail.
This discharges weight normalization, not the zeta-mollifier moment or density.
-/

open Complex MeasureTheory Set Filter
open scoped Topology
noncomputable section
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- The signed secondary residue coefficient tends to minus one at the critical endpoint. -/
theorem tendsto_secondaryResidueCoefficient :
    Tendsto secondaryResidueCoefficient (𝓝[>] (1 / 2 : ℝ)) (𝓝 (-1 : ℂ)) := by
  have hplus : Tendsto (fun σ : ℝ => (2 * σ : ℝ) : ℝ → ℂ)
      (𝓝[>] (1 / 2 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hh : ContinuousAt (fun σ : ℝ => (2 * σ : ℝ) : ℝ → ℂ) (1/2) := by fun_prop
      convert hh.continuousWithinAt.tendsto using 1
      norm_num
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      change (2 * σ : ℝ) ≠ (1 : ℂ)
      intro he
      have hh := congrArg Complex.re he
      simp at hh
      change 1/2 < σ at hσ
      linarith
  have hminus : Tendsto (fun σ : ℝ => (2 : ℂ) - (2 * σ : ℝ))
      (𝓝[>] (1 / 2 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hh : ContinuousAt (fun σ : ℝ => (2 : ℂ) - (2 * σ : ℝ)) (1/2) := by fun_prop
      convert hh.continuousWithinAt.tendsto using 1
      norm_num
    · filter_upwards [self_mem_nhdsWithin] with σ hσ
      change (2 : ℂ) - (2 * σ : ℝ) ≠ 1
      intro he
      have hh := congrArg Complex.re he
      simp at hh
      change 1/2 < σ at hσ
      linarith
  have hp := riemannZeta_residue_one.comp hplus
  have hm := (riemannZeta_residue_one.comp hminus).neg
  have hg : Tendsto (fun σ : ℝ => Gamma ((2 : ℂ) - (2 * σ : ℝ)))
      (𝓝[>] (1/2 : ℝ)) (𝓝 (1 : ℂ)) := by
    have hh := Complex.continuousAt_Gamma_one.tendsto.comp
      (hminus.mono_right nhdsWithin_le_nhds)
    simpa only [Complex.Gamma_one, Function.comp_def] using hh
  have hlim := (hg.mul hm).div hp (by norm_num : (1 : ℂ) ≠ 0)
  have hh : Tendsto
      (fun σ : ℝ => Gamma ((2 : ℂ) - (2 * σ : ℝ)) *
        (-(((2 : ℂ) - (2 * σ : ℝ) - 1) *
          riemannZeta ((2 : ℂ) - (2 * σ : ℝ)))) /
        (((2 * σ : ℝ) - (1 : ℂ)) * riemannZeta (2 * σ : ℝ)))
      (𝓝[>] (1/2 : ℝ)) (𝓝 (-1 : ℂ)) := by
    convert hlim using 1
    · funext σ
      rfl
    · norm_num
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  change 1/2 < σ at hσ
  have hq : (2 * σ : ℝ) - (1 : ℂ) ≠ 0 := by
    intro he
    have hh := congrArg Complex.re he
    simp at hh
    linarith
  dsimp [secondaryResidueCoefficient]
  have he : -((2 : ℂ) - (2 * σ : ℝ) - 1) = (2 * σ : ℝ) - 1 := by ring
  rw [← neg_mul, he]
  field_simp [hq]
/-- A uniform coefficient neighborhood, also contained in the negative-contour strip. -/
theorem exists_secondaryResidueCoefficient_bound :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 4 ∧
      ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 / 2 + η →
        ‖secondaryResidueCoefficient σ‖ ≤ 2 := by
  obtain ⟨δ, hδ, hb⟩ := Metric.tendsto_nhdsWithin_nhds.mp
    tendsto_secondaryResidueCoefficient 1 (by norm_num)
  refine ⟨min (δ / 2) (1 / 4), lt_min (by linarith) (by norm_num),
    min_le_right _ _, ?_⟩
  intro σ hσ hσhi
  have hdist : dist σ (1 / 2) < δ := by
    rw [Real.dist_eq, abs_of_pos (by linarith : 0 < σ - 1 / 2)]
    have hmin := min_le_left (δ / 2) (1 / 4)
    linarith
  have hh := hb hσ hdist
  have hn := norm_le_norm_sub_add (secondaryResidueCoefficient σ) (-1 : ℂ)
  simp only [dist_eq_norm, sub_neg_eq_add] at hh
  norm_num at hn
  linarith

/- The following lemmas continue inside the ConreyBaluyot namespace. -/

/-- The explicit constant in the uniform negative-contour remainder. -/
def negativeRemainderConstant : ℝ := 1024 * Real.Gamma (17 / 4)

theorem negativeRemainderConstant_pos : 0 < negativeRemainderConstant := by
  exact mul_pos (by norm_num) (Real.Gamma_pos_of_pos (by norm_num))

/-- Norm form of the signed expansion, retaining both error contributions. -/
theorem norm_weight_sub_one_le {σ ξ : ℝ}
    (hσ : 1 / 2 < σ) (hσhi : σ ≤ 3 / 4) (hξ : 0 < ξ) :
    ‖weight σ ξ - 1‖ ≤ ‖secondaryResidueCoefficient σ‖ * ξ ^ (1 - 2 * σ) +
      negativeRemainderConstant * ξ ^ (-(3 / 4 : ℝ)) := by
  have hp : ‖(ξ : ℂ) ^ ((1 : ℂ) - (2 * σ : ℝ))‖ = ξ ^ (1 - 2 * σ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hξ]
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
  calc
    _ = ‖secondaryResidueCoefficient σ *
        (ξ : ℂ) ^ ((1 : ℂ) - (2 * σ : ℝ)) + weightOnLine σ ξ (-(3 / 4))‖ := by
      rw [weight_eq_residues_add_negative hσ hσhi hξ]
      congr 1
      ring
    _ ≤ ‖secondaryResidueCoefficient σ *
        (ξ : ℂ) ^ ((1 : ℂ) - (2 * σ : ℝ))‖ + ‖weightOnLine σ ξ (-(3 / 4))‖ :=
      norm_add_le _ _
    _ ≤ _ := by
      rw [norm_mul, hp]
      exact add_le_add le_rfl (norm_weightOnLine_negative_le hσ hσhi hξ)

theorem weight_re_lower_bound {σ ξ : ℝ}
    (hσ : 1 / 2 < σ) (hσhi : σ ≤ 3 / 4) (hξ : 0 < ξ) :
    1 - ‖secondaryResidueCoefficient σ‖ * ξ ^ (1 - 2 * σ) -
      negativeRemainderConstant * ξ ^ (-(3 / 4 : ℝ)) ≤ (weight σ ξ).re := by
  have hb := norm_weight_sub_one_le hσ hσhi hξ
  have hr := Complex.re_le_norm (1 - weight σ ξ)
  rw [norm_sub_rev] at hr
  simp only [Complex.sub_re, Complex.one_re] at hr
  linarith

/-- The coupled logarithmic lower cutoff forces the secondary power below exp(-2). -/
theorem rpow_le_exp_neg_two_of_coupled_strip {σ y : ℝ}
    (hy : 1 < y) (hσ : 1 / 2 + 1 / Real.log y ≤ σ) :
    y ^ (1 - 2 * σ) ≤ Real.exp (-2) := by
  have hl : 0 < Real.log y := Real.log_pos hy
  rw [Real.rpow_def_of_pos (by linarith : 0 < y)]
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_right hσ hl.le
  have he : (1 / Real.log y) * Real.log y = 1 := by field_simp
  nlinarith only [hmul, he]

private theorem twice_exp_neg_two_lt_half : 2 * Real.exp (-2) < 1 / 2 := by
  have h1 : 2 < Real.exp 1 := by
    have hh := Real.add_one_lt_exp (by norm_num : (1 : ℝ) ≠ 0)
    norm_num at hh
    exact hh
  have h2 : 4 < Real.exp 2 := by
    have he : Real.exp (2 : ℝ) = Real.exp 1 * Real.exp 1 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    rw [he]
    nlinarith
  have hi : (Real.exp (2 : ℝ))⁻¹ < 1 / 4 := by
    rw [← one_div]
    exact (div_lt_iff₀ (Real.exp_pos (2 : ℝ))).mpr (by nlinarith)
  rw [Real.exp_neg]
  linarith

/-- Global bound on the selected sigma interval, with an absolute explicit constant. -/
theorem norm_weight_le_global_of_coefficient_bound {σ ξ : ℝ}
    (hσ : 1 / 2 < σ) (hσhi : σ ≤ 3 / 4)
    (hA : ‖secondaryResidueCoefficient σ‖ ≤ 2) (hξ : 0 < ξ) :
    ‖weight σ ξ‖ ≤ max 72 (3 + negativeRemainderConstant) := by
  by_cases hξ1 : ξ ≤ 1
  · have hh := norm_weight_le_exp hσ hξ hξ1
    have he : Real.exp (-1 / (2 * ξ)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity)
    exact (hh.trans (by nlinarith)).trans (le_max_left _ _)
  · have hξ1' : 1 ≤ ξ := le_of_lt (lt_of_not_ge hξ1)
    have hp : ξ ^ (1 - 2 * σ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hξ1' (by linarith)
    have hn : ξ ^ (-(3 / 4 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hξ1' (by norm_num)
    have hAterm : ‖secondaryResidueCoefficient σ‖ * ξ ^ (1 - 2 * σ) ≤ 2 := by
      calc
        _ ≤ 2 * 1 := mul_le_mul hA hp (Real.rpow_nonneg hξ.le _) (by norm_num)
        _ = 2 := by ring
    have hCterm : negativeRemainderConstant * ξ ^ (-(3 / 4 : ℝ)) ≤
        negativeRemainderConstant := by
      simpa using mul_le_mul_of_nonneg_left hn negativeRemainderConstant_pos.le
    have hh := norm_weight_sub_one_le hσ hσhi hξ
    have ht := norm_le_norm_sub_add (weight σ ξ) (1 : ℂ)
    norm_num only [norm_one] at ht
    exact (show ‖weight σ ξ‖ ≤ 3 + negativeRemainderConstant by linarith).trans
      (le_max_right _ _)

/-- Actual uniform positive normalization on a nonempty coupled logarithmic strip. -/
theorem exists_uniform_weight_normalization :
    ∃ ε₀ Y₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 / 4 ∧ 1 < Y₀ ∧
      Real.exp (1 / ε₀) ≤ Y₀ ∧
      (∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 / 2 + ε₀ →
        ∀ ξ : ℝ, 0 < ξ → ‖weight σ ξ‖ ≤ max 72 (3 + negativeRemainderConstant)) ∧
      (∀ y : ℝ, Y₀ ≤ y → ∀ σ : ℝ,
        1 / 2 + 1 / Real.log y ≤ σ → σ ≤ 1 / 2 + ε₀ →
        1 / 4 ≤ (weight σ y).re) := by
  obtain ⟨η, hη, hηhi, hA⟩ := exists_secondaryResidueCoefficient_bound
  let ε₀ := η / 2
  have hε : 0 < ε₀ := by dsimp [ε₀]; linarith
  have hεhi : ε₀ < 1 / 4 := by dsimp [ε₀]; linarith
  have hlim : Tendsto (fun y : ℝ => negativeRemainderConstant * y ^ (-(3 / 4 : ℝ)))
      atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 4)).const_mul
      negativeRemainderConstant
  obtain ⟨Y, hY⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (by norm_num :
    (0 : ℝ) < 1 / 4)))
  refine ⟨ε₀, max 2 (max Y (Real.exp (1 / ε₀))), hε, hεhi,
    lt_of_lt_of_le (by norm_num) (le_max_left _ _),
    (le_max_right _ _).trans (le_max_right _ _), ?_, ?_⟩
  · intro σ hσ hσhi ξ hξ
    apply norm_weight_le_global_of_coefficient_bound hσ (by linarith) (hA σ hσ ?_) hξ
    dsimp [ε₀] at hσhi
    linarith
  · intro y hy σ hσ hσhi
    have hy2 : 2 ≤ y := (le_max_left _ _).trans hy
    have hYy : Y ≤ y := (le_max_left _ _).trans ((le_max_right _ _).trans hy)
    have hy0 : 0 < y := by linarith
    have hl : 0 < Real.log y := Real.log_pos (by linarith)
    have hs : 1 / 2 < σ := by have := one_div_pos.mpr hl; linarith
    have hsHi : σ ≤ 3 / 4 := by linarith
    have hb := weight_re_lower_bound hs hsHi hy0
    have hc := hY y hYy
    have ha : ‖secondaryResidueCoefficient σ‖ ≤ 2 := by
      apply hA σ hs
      dsimp [ε₀] at hσhi
      linarith
    have hp := rpow_le_exp_neg_two_of_coupled_strip (by linarith : 1 < y) hσ
    have hprod : ‖secondaryResidueCoefficient σ‖ * y ^ (1 - 2 * σ) ≤
        2 * Real.exp (-2) :=
      mul_le_mul ha hp (Real.rpow_nonneg hy0.le _) (by norm_num)
    have he := twice_exp_neg_two_lt_half
    linarith
theorem weight_ne_zero_of_re_lower_bound {σ y : ℝ}
    (hW : 1 / 4 ≤ (weight σ y).re) : weight σ y ≠ 0 := by
  intro he
  rw [he] at hW
  norm_num at hW

theorem norm_weight_inv_le_of_re_lower_bound {σ y : ℝ}
    (hW : 1 / 4 ≤ (weight σ y).re) : ‖(weight σ y)⁻¹‖ ≤ 4 := by
  have hn : 1 / 4 ≤ ‖weight σ y‖ := hW.trans (Complex.re_le_norm _)
  rw [norm_inv, ← one_div]
  apply (div_le_iff₀ (by linarith : 0 < ‖weight σ y‖)).mpr
  linarith

private theorem norm_moebius_complex_le_one (n : ℕ) :
    ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> simp [h]

private theorem coefficient_bound_of_numerator {σ y K : ℝ} {n : ℕ}
    (hW : 1 / 4 ≤ (weight σ y).re) (hnum : ‖weight σ (y / n)‖ ≤ K) :
    ‖mollifierCoefficient σ y n‖ ≤ 4 * K := by
  have hK : 0 ≤ K := (norm_nonneg _).trans hnum
  have hinv := norm_weight_inv_le_of_re_lower_bound hW
  unfold mollifierCoefficient
  rw [div_eq_mul_inv, norm_mul, norm_mul]
  calc
    _ ≤ 1 * (K * 4) := mul_le_mul (norm_moebius_complex_le_one n)
      (mul_le_mul hnum hinv (norm_nonneg _) hK)
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    _ = _ := by ring

/-- The actual coefficients are normalized and uniformly bounded, with an exponential tail.
No analytic provider occurs in the hypotheses of this existence theorem. -/
theorem exists_uniform_mollifier_coefficient_bounds :
    ∃ ε₀ Y₀ K : ℝ, 0 < ε₀ ∧ ε₀ < 1 / 4 ∧ 1 < Y₀ ∧
      Real.exp (1 / ε₀) ≤ Y₀ ∧ 0 ≤ K ∧
      ∀ y : ℝ, Y₀ ≤ y → ∀ σ : ℝ,
        1 / 2 + 1 / Real.log y ≤ σ → σ ≤ 1 / 2 + ε₀ →
        weight σ y ≠ 0 ∧ ‖(weight σ y)⁻¹‖ ≤ 4 ∧
        mollifierCoefficient σ y 1 = 1 ∧
        (∀ n : ℕ, 0 < n → ‖mollifierCoefficient σ y n‖ ≤ 4 * K) ∧
        (∀ n : ℕ, y ≤ n → ‖mollifierCoefficient σ y n‖ ≤
          288 * Real.exp (-(n : ℝ) / (2 * y))) := by
  obtain ⟨ε₀, Y₀, hε, hεhi, hY, hexp, hglobal, hnorm⟩ :=
    exists_uniform_weight_normalization
  refine ⟨ε₀, Y₀, max 72 (3 + negativeRemainderConstant),
    hε, hεhi, hY, hexp, le_trans (by norm_num) (le_max_left _ _), ?_⟩
  intro y hy σ hσ hσhi
  have hy1 : 1 < y := hY.trans_le hy
  have hy0 : 0 < y := by linarith
  have hl : 0 < Real.log y := Real.log_pos hy1
  have hs : 1 / 2 < σ := by have := one_div_pos.mpr hl; linarith
  have hW := hnorm y hy σ hσ hσhi
  have hne := weight_ne_zero_of_re_lower_bound hW
  refine ⟨hne, norm_weight_inv_le_of_re_lower_bound hW,
    mollifierCoefficient_one hne, ?_, ?_⟩
  · intro n hn
    apply coefficient_bound_of_numerator hW
    exact hglobal σ hs hσhi (y / n) (div_pos hy0 (by exact_mod_cast hn))
  · intro n hn
    have hh := coefficient_bound_of_numerator hW (norm_weight_ratio_le_exp hs hy0 hn)
    convert hh using 1
    ring

end RiemannResearch.Analysis.ConreyBaluyot
