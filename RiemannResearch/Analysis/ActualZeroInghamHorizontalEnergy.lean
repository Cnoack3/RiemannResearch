/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualInghamLittlewoodDensity
import RiemannResearch.Analysis.ActualSelbergIngham
import RiemannResearch.Analysis.ActualZeroCountNormalization
import RiemannResearch.Analysis.ActualZeroLoglogRate
import RiemannResearch.Analysis.ActualZeroTailLayerCake
import RiemannResearch.Analysis.ActualZeroTailReflection
import RiemannResearch.Analysis.FiniteStrictTailSecondMoment
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Leading upper bound for actual horizontal zero energy

Chourasiya and Simonič, *An explicit form of Ingham's zero density estimate*,
Theorem 1, https://arxiv.org/abs/2507.15184, give the logarithmic profile used
in `exists_ingham_littlewood_density_all_heights`. Its checked actual-zero
version has logarithmic exponent at most three. At distance
`(3/2) * log(log T) / log T` the two surplus logarithms are absorbed. The
excess beyond this strip has squared sum `O(T / log T)`. Inside the strip
we retain the actual multiplicity count and its Riemann–von Mangoldt
leading coefficient.
-/

noncomputable section

open Filter Set Zeta23
open scoped Topology BigOperators

namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- A two-sided exponential envelope extracted from the sharper Ingham
profile. The constant is uniform in the displacement threshold. -/
theorem exists_strictTail_ingham_exponential :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, max 2 (Real.exp 1) ≤ T →
      ∀ t : ℝ, 0 ≤ t →
        strictTail T t ≤ C * T * (Real.log T) ^ 3 *
          Real.exp (-((4 / 3 * Real.log T) * t)) := by
  obtain ⟨D, hD, hd⟩ := exists_ingham_littlewood_density_all_heights
  refine ⟨2 * D, by positivity, ?_⟩
  intro T hT t ht
  have hT₂ := (le_max_left (2 : ℝ) (Real.exp 1)).trans hT
  have hT₀ : 0 < T := by linarith
  have hL : 1 ≤ Real.log T := by
    simpa only [Real.log_exp] using
      Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hT)
  by_cases ht₂ : t ≤ 1 / 2
  · let σ : ℝ := 1 / 2 + t
    let q : ℝ := 3 * (1 - σ) / (2 - σ)
    have hσ : σ ∈ Icc (1 / 2 : ℝ) 1 := ⟨by dsimp [σ]; linarith, by dsimp [σ]; linarith⟩
    have hq : q ≤ 1 - 4 / 3 * t := by
      have he := ingham_exponent_add_gap_le (a := (4 / 3 : ℝ)) (η := t)
        le_rfl ht (show σ ∈ Icc (1 / 2 + t) 1 from ⟨le_rfl, hσ.2⟩)
      change q + (4 / 3 - 4 / 3) * t ≤ 1 - 4 / 3 * (σ - 1 / 2) at he
      dsimp [σ] at he
      linarith
    have hTq : T ^ q ≤ T * Real.exp (-((4 / 3 * Real.log T) * t)) := by
      calc
        _ ≤ T ^ (1 - 4 / 3 * t) := Real.rpow_le_rpow_of_exponent_le (by linarith) hq
        _ = _ := by
          rw [Real.rpow_def_of_pos hT₀, show Real.log T * (1 - 4 / 3 * t) =
            Real.log T + -((4 / 3 * Real.log T) * t) by ring, Real.exp_add, Real.exp_log hT₀]
    have hLq : (Real.log T) ^ (2 + q) ≤ (Real.log T) ^ (3 : ℕ) := by
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le hL
      norm_num
      linarith only [hq, ht]
    have hraw := hd T hT₂ σ hσ
    change rightInclusiveCount T σ ≤
      D * min (T * Real.log T) (T ^ q * (Real.log T) ^ (2 + q)) at hraw
    calc
      _ ≤ 2 * rightInclusiveCount T σ := strictTail_le_twice_inclusive T t ht
      _ ≤ 2 * (D * (T ^ q * (Real.log T) ^ (2 + q))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact hraw.trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hD.le)
      _ ≤ 2 * (D * ((T * Real.exp (-((4 / 3 * Real.log T) * t))) *
          (Real.log T) ^ (3 : ℕ))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul hTq hLq (Real.rpow_nonneg (by linarith) _) (by positivity)) hD.le)
          (by norm_num)
      _ = _ := by ring
  · have hz : strictTail T t = 0 := by
      rw [strictTail_eq_realSum, realSum]
      apply Finset.sum_eq_zero
      intro ρ hρ
      have hρ' := displacement_lt_half hρ
      rw [if_neg (by linarith : ¬ t < |ρ.re - 1 / 2|), mul_zero]
    rw [hz]
    positivity

private theorem sq_le_shifted_sq (x b η : ℝ) (hx : 0 ≤ x) (hη : 0 < η) :
    x ^ 2 ≤ (1 + η) * b ^ 2 + (1 + η⁻¹) * (max 0 (x - b)) ^ 2 := by
  let z := max 0 (x - b)
  have hxb : x ≤ b + z := by dsimp [z]; linarith [le_max_right 0 (x - b)]
  have hprod : 2 * b * z - η * b ^ 2 ≤ z ^ 2 / η := by
    apply (le_div_iff₀ hη).2
    nlinarith only [sq_nonneg (η * b - z)]
  have hsq := pow_le_pow_left₀ hx hxb 2
  change x ^ 2 ≤ (1 + η) * b ^ 2 + (1 + η⁻¹) * z ^ 2
  simp only [add_mul, one_mul, inv_mul_eq_div]
  nlinarith only [hsq, hprod]

/-- The constant for the total count is kept separate from the far-tail
constant. The second term vanishes after the displayed normalization. -/
theorem exists_horizontalEnergy_ingham_upper :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → ∀ᶠ T : ℝ in atTop,
      horizontalEnergy T / (T * horizontalLogRate T) ≤
        ((1 + η) * (9 / 4)) * ((Ncount 0 T : ℝ) / (T * Real.log T)) +
        ((1 + η⁻¹) * (9 * C / 8)) / (Real.log (Real.log T)) ^ 2 := by
  obtain ⟨C, hC, htail⟩ := exists_strictTail_ingham_exponential
  refine ⟨C, hC, ?_⟩
  intro η hη
  filter_upwards [eventually_ge_atTop (max 2 (Real.exp 1)),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_gt_atTop 0] with T hT hℓ
  let L := Real.log T
  let ℓ := Real.log L
  let b := 3 / 2 * ℓ / L
  let a := 4 / 3 * L
  have hT₀ : 0 < T := by linarith [le_max_left (2 : ℝ) (Real.exp 1)]
  have hL : 0 < L := Real.log_pos (by linarith [le_max_left (2 : ℝ) (Real.exp 1)])
  change 0 < ℓ at hℓ
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  let x := copyDisplacement T
  let z := fun c : Copies T => max 0 (x c - b)
  have hzmem (c : Copies T) : z c ∈ Icc (0 : ℝ) (1 / 2) := by
    refine ⟨le_max_left _ _, max_le (by norm_num) ?_⟩
    have hx := displacement_lt_half c.1.2
    dsimp [x, copyDisplacement]
    linarith
  have htranslate (t : ℝ) (ht : 0 ≤ t) :
      FiniteStrictTail.tail Finset.univ z t = strictTail T (b + t) := by
    change FiniteStrictTail.tail Finset.univ z t = FiniteStrictTail.tail Finset.univ x (b + t)
    simp only [FiniteStrictTail.tail]
    apply Finset.sum_congr rfl
    intro c _
    have he : t < z c ↔ b + t < x c := by
      simp only [z, lt_max_iff, not_lt_of_ge ht, false_or]
      rw [lt_sub_iff_add_lt, add_comm t b]
    exact if_congr he rfl rfl
  have hab : a * b = 2 * ℓ := by
    dsimp [a, b]
    field_simp [hL.ne']
    <;> ring
  have hexp : Real.exp (2 * ℓ) = L ^ 2 := by
    rw [show (2 : ℝ) * ℓ = (2 : ℕ) * ℓ by norm_num, Real.exp_nat_mul, Real.exp_log hL]
  have hzsum : (∑ c : Copies T, (z c) ^ 2) ≤ 2 * (C * T * L) / a ^ 2 := by
    apply FiniteStrictTail.secondMoment_le_exponential_tail _ _ _ _ _
      (by norm_num) (by positivity) ha (fun c _ => hzmem c)
    intro t ht
    rw [htranslate t ht.1]
    calc
      _ ≤ C * T * L ^ 3 * Real.exp (-(a * (b + t))) := htail T hT (b + t) (add_nonneg hb ht.1)
      _ = C * T * L * Real.exp (-a * t) := by
        rw [show -(a * (b + t)) = -(a * b) + -a * t by ring,
          Real.exp_add, hab, Real.exp_neg, hexp]
        field_simp [hL.ne']
        <;> ring
  have he : horizontalEnergy T = ∑ c : Copies T, (x c) ^ 2 := by
    rw [horizontalEnergy, realSum_eq_copies]
    simp only [x, copyDisplacement, sq_abs]
  have hsum : horizontalEnergy T ≤
      (1 + η) * b ^ 2 * (Ncount 0 T : ℝ) + (1 + η⁻¹) * (2 * (C * T * L) / a ^ 2) := by
    calc
      _ ≤ ∑ c : Copies T, ((1 + η) * b ^ 2 + (1 + η⁻¹) * (z c) ^ 2) := by
        rw [he]
        exact Finset.sum_le_sum (fun c _ => sq_le_shifted_sq (x c) b η (abs_nonneg _) hη)
      _ = (1 + η) * b ^ 2 * (Ncount 0 T : ℝ) + (1 + η⁻¹) * (∑ c : Copies T, (z c) ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          card_copies, nsmul_eq_mul]
        ring
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hzsum (by positivity))
  calc
    _ ≤ _ := div_le_div_of_nonneg_right hsum (by unfold horizontalLogRate; positivity)
    _ = _ := by
      change ((1 + η) * b ^ 2 * (Ncount 0 T : ℝ) +
        (1 + η⁻¹) * (2 * (C * T * L) / a ^ 2)) / (T * (ℓ ^ 2 / L)) = _
      dsimp only [a, b]
      change _ = ((1 + η) * (9 / 4)) * ((Ncount 0 T : ℝ) / (T * L)) +
        ((1 + η⁻¹) * (9 * C / 8)) / ℓ ^ 2
      field_simp [hT₀.ne', hL.ne', hℓ.ne', hη.ne']
      <;> ring

/-- An unconditional leading upper bound for the multiplicity-weighted
horizontal energy, with the coefficient from the actual zero count. -/
theorem eventually_horizontalEnergy_ratio_le_ingham {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop,
      horizontalEnergy T / (T * horizontalLogRate T) ≤ 9 / (8 * Real.pi) + ε := by
  obtain ⟨C, _, hE⟩ := exists_horizontalEnergy_ingham_upper
  let B : ℝ := 9 / (8 * Real.pi)
  have hB : 0 < B := by dsimp [B]; positivity
  let η := ε / (2 * B)
  have hη : 0 < η := by dsimp [η]; positivity
  have hc : Tendsto (fun T : ℝ => (Ncount 0 T : ℝ) / (T * Real.log T))
      atTop (𝓝 (1 / (2 * Real.pi))) := by
    have hn := tendsto_count_div_mainTerm.const_mul (1 / (2 * Real.pi))
    simp only [mul_one] at hn
    apply hn.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    have hpos : 0 < T := by linarith
    have hlog := Real.log_pos hT
    field_simp [hpos.ne', hlog.ne', Real.pi_ne_zero]
    <;> ring
  have ht := ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).const_div_atTop (1 : ℝ)).pow 2
  simp only [zero_pow (by norm_num : 2 ≠ 0)] at ht
  have htail : Tendsto (fun T : ℝ =>
      ((1 + η⁻¹) * (9 * C / 8)) / (Real.log (Real.log T)) ^ 2) atTop (𝓝 0) := by
    convert ht.const_mul ((1 + η⁻¹) * (9 * C / 8)) using 1
    · funext T
      simp only [Function.comp_def, div_pow, one_pow, mul_one_div]
    · simp
  have hlim := (hc.const_mul ((1 + η) * (9 / 4))).add htail
  simp only [add_zero] at hlim
  have hupper : ((1 + η) * (9 / 4)) * (1 / (2 * Real.pi)) < B + ε := by
    have he : (9 / 4 : ℝ) * (1 / (2 * Real.pi)) = B := by dsimp [B]; ring
    rw [mul_assoc, he, add_mul, one_mul]
    have heq : η * B = ε / 2 := by dsimp [η]; field_simp
    linarith
  filter_upwards [hE η hη, hlim.eventually_lt_const hupper] with T he ht
  exact he.trans ht.le

end RiemannResearch.Analysis.ActualZeroOrdinate
