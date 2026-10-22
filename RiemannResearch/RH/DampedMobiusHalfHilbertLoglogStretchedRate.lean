/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ArithmeticFloorLoglogStretchedEnvelope
import RiemannResearch.RH.DampedMobiusLoglogStretchedProviders
import RiemannResearch.RH.DampedMobiusProfileNorm
import RiemannResearch.Analysis.LogSquareTail

/-!
# The optimized complete endpoint Hilbert rate

See `RH/MertensStretchedContinuation20260927.md` for the provider audit,
finite optimization, and scope of the result.
-/

noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis

/-- The optimized logarithmic physical kernel is summable. -/
theorem summable_halfProfileKernel_logProductPower
    (a β : ℝ) (ha : 0 < a) (hβ : 0 < β) :
    Summable (halfProfileKernel a (fun n => logProductPower β (6 + Real.log (n : ℝ)))) := by
  obtain ⟨B, hB, hb⟩ := stretchedExp_le_inverse_square a β ha hβ
  have hmajor (n : ℕ) :
      halfProfileKernel a (fun n => logProductPower β (6 + Real.log (n : ℝ))) n ≤
        B * (1 / ((n : ℝ) * (6 + Real.log (n : ℝ)) ^ (2 : ℝ))) := by
    by_cases hn : n = 0
    · subst n
      simp [halfProfileKernel]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      have hL : 6 ≤ 6 + Real.log (n : ℝ) := by linarith [Real.log_nonneg hn1]
      have hlower := logProductPower_lower β hβ.le hL
      have hexp : Real.exp (-a * logProductPower β (6 + Real.log (n : ℝ))) ≤
          Real.exp (-a * (6 + Real.log (n : ℝ)) ^ β) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hlower ha.le]
      calc
        _ ≤ (1 / (n : ℝ)) * Real.exp (-a * (6 + Real.log (n : ℝ)) ^ β) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
        _ ≤ (1 / (n : ℝ)) * (B / (6 + Real.log (n : ℝ)) ^ 2) :=
          mul_le_mul_of_nonneg_left (hb _ (by linarith)) (by positivity)
        _ = _ := by
          simp only [Real.rpow_two, one_div, div_eq_mul_inv, mul_inv_rev]
          ring
  exact Summable.of_nonneg_of_le (halfProfileKernel_nonneg _ _) hmajor
    (summable_shifted_log_square.mul_left B)

/-- Exact density-tail squaring controls the entire finite physical head. -/
theorem dampedMobius_half_head_error_profile_bound
    (φ : ℕ → ℝ) {d D : ℝ} (hD : 0 ≤ D)
    (hT : ∀ M : ℕ, 0 < M →
      |(1 / riemannZeta (1 + ((1 / 2 : ℝ) : ℂ))).re -
        positiveArithmeticPrefix (fun m => dampedMobiusWeight (1 / 2) m / (m : ℝ)) M| ≤
        D * (M : ℝ) ^ (-1 / 2 : ℝ) * Real.exp (-d * φ M))
    (H M : ℕ) (hHM : H ≤ M) (hM : 1 ≤ M) :
    (∑ n ∈ Finset.range H, positiveWeight n *
      (hilbertSequence (arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M) n -
        (dampedMobiusPrefix (1 / 2) n - (n : ℝ) *
          (1 / riemannZeta (1 + ((1 / 2 : ℝ) : ℂ))).re)) ^ 2) ≤
      D ^ 2 * Real.exp (-2 * d * φ M) := by
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hsq := (sq_le_sq₀ (abs_nonneg _) (by positivity :
    0 ≤ D * (M : ℝ) ^ (-1 / 2 : ℝ) * Real.exp (-d * φ M))).mpr (hT M (by omega))
  rw [sq_abs] at hsq
  simp only [positiveArithmeticPrefix] at hsq
  simp only [dampedMobiusPrefix]
  rw [arithmeticFloorPartial_head_error _ _ H M hHM]
  calc
    _ ≤ (D * (M : ℝ) ^ (-1 / 2 : ℝ) * Real.exp (-d * φ M)) ^ 2 * (M : ℝ) :=
      mul_le_mul hsq ((paretoHead_linear_mass_le H).trans (by exact_mod_cast hHM))
        (Finset.sum_nonneg (fun n _ => mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _)))
        (sq_nonneg _)
    _ = _ := by
      have hm : ((M : ℝ) ^ (-1 / 2 : ℝ)) ^ 2 = (M : ℝ)⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hMp.le]
        norm_num [Real.rpow_neg]
      have he : (Real.exp (-d * φ M)) ^ 2 = Real.exp (-2 * d * φ M) := by
        rw [sq, ← Real.exp_add]
        congr 1
        ring
      rw [mul_pow, mul_pow, hm, he]
      field_simp

/-- The full-PNT bootstrap propagates its optimized stretched-log power
through the finite head and the complete infinite physical tail. -/
theorem dampedMobius_half_cutoffs_eventual_loglog_stretched_rate :
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ M : ℕ in atTop,
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M -
        dampedMobiusHalfRangeLimit (1 / 2) le_rfl‖ ≤
        C * Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (M : ℝ))) := by
  obtain ⟨d, hd, hd8, B, D, hB, hD, hp, ht⟩ := dampedMobius_half_loglog_stretched_providers
  let φ : ℕ → ℝ := fun n => logProductPower (1 / 11) (6 + Real.log (n : ℝ))
  have hmono : ∀ m n : ℕ, 1 ≤ m → m ≤ n → φ m ≤ φ n := by
    intro m n hm hmn
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    exact logProductPower_mono (1 / 11) (by norm_num)
      (by linarith [Real.log_nonneg hm1])
      (by linarith [Real.log_le_log hm0 (show (m : ℝ) ≤ n by exact_mod_cast hmn)])
  have hphi0 (n : ℕ) (hn : 1 ≤ n) : 0 ≤ φ n := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hL : 1 ≤ 6 + Real.log (n : ℝ) := by linarith [Real.log_nonneg hn1]
    dsimp [φ, logProductPower]
    exact Real.rpow_nonneg (mul_nonneg (by linarith) (Real.log_nonneg hL)) _
  have ht' (t : ℕ) (ht0 : 0 < t) :
      |(1 / riemannZeta (1 + ((1 / 2 : ℝ) : ℂ))).re -
        positiveArithmeticPrefix (fun k => dampedMobiusWeight (1 / 2) k / (k : ℝ)) t| ≤
        D / Real.sqrt (t : ℝ) * loglogStretchedProfile (1 / 11) d (t : ℝ) := by
    have h := ht t ht0
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
      Real.rpow_neg (Nat.cast_nonneg t), ← Real.sqrt_eq_rpow] at h
    simpa only [div_eq_mul_inv] using h
  let K : ℝ := 2 + 6 * B + 4 * D
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ M : ℕ,
      |hilbertSequence (arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M) n| ≤
        K * Real.sqrt (n : ℝ) * Real.exp (-(d / 8) * φ n) := by
    filter_upwards [hlog.eventually (eventually_ge_atTop (10 : ℝ)),
      eventually_ge_atTop (1 : ℕ)] with n hn hn1
    intro M
    have h := arithmeticFloorHilbertPartial_uniform_loglog_stretched_bound
      (dampedMobiusWeight (1 / 2)) (dampedMobiusWeight_zero _) _ (W := 1)
      (by norm_num) hB hD (by norm_num : (0 : ℝ) < 1 / 11)
      (by norm_num : (1 / 11 : ℝ) ≤ 1 / 2) hd hd8 dampedMobius_half_weight_bound hp ht'
      M n (by omega) hn
    simpa only [K, φ, mul_one] using h
  have hhead : ∀ᶠ M : ℕ in atTop,
      (∑ n ∈ Finset.range M, positiveWeight n *
        (hilbertSequence
          (arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M -
            dampedMobiusHalfRangeLimit (1 / 2) le_rfl) n) ^ 2) ≤
        D ^ 2 * Real.exp (-(d / 8) * φ M) := by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
    have htφ (t : ℕ) (ht0 : 0 < t) :
        |(1 / riemannZeta (1 + ((1 / 2 : ℝ) : ℂ))).re -
          positiveArithmeticPrefix (fun m => dampedMobiusWeight (1 / 2) m / (m : ℝ)) t| ≤
          D * (t : ℝ) ^ (-1 / 2 : ℝ) * Real.exp (-d * φ t) := by
      simpa only [φ, logProductPower, loglogStretchedProfile, stretchedLoglogCore] using ht t ht0
    have h := dampedMobius_half_head_error_profile_bound φ hD htφ M M le_rfl hM
    have he : Real.exp (-2 * d * φ M) ≤ Real.exp (-(d / 8) * φ M) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hd.le (hphi0 M hM)]
    have h' := h.trans (mul_le_mul_of_nonneg_left he (sq_nonneg D))
    simpa only [hilbertSequence_sub, Pi.sub_apply,
      (dampedMobiusHalfRangeLimit_spec (1 / 2) le_rfl).1] using h'
  obtain ⟨C, hC, hc⟩ :=
    dampedMobius_half_cutoffs_eventual_profile_rate_of_coordinate_and_head
      φ (by positivity : 0 < d / 8) hK (sq_nonneg D) hmono
      (summable_halfProfileKernel_logProductPower (d / 8) (1 / 11) (by positivity) (by norm_num))
      hbound hhead
  refine ⟨d / 16, by positivity, C, hC, ?_⟩
  have he : (d / 8) / 2 = d / 16 := by ring
  simpa only [he, φ] using hc

/-- All cutoffs share a single positive optimized stretched-log rate.
The finite exceptional set changes only the multiplicative constant. -/
theorem dampedMobius_half_cutoffs_loglog_stretched_rate_unshifted :
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ,
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M -
        dampedMobiusHalfRangeLimit (1 / 2) le_rfl‖ ≤
        C * Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (M : ℝ))) := by
  obtain ⟨a, ha, C, hC, hc⟩ := dampedMobius_half_cutoffs_eventual_loglog_stretched_rate
  obtain ⟨D, hD, hd⟩ := exists_global_majorant_of_eventual_positive_profile
    (fun M => ‖arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M -
      dampedMobiusHalfRangeLimit (1 / 2) le_rfl‖)
    (fun M => Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (M : ℝ))))
    (fun _ => norm_nonneg _) (fun _ => Real.exp_pos _) hc
  exact ⟨a, ha, D, hD, hd⟩


private theorem logProductPower_nat_succ_le_two (β : ℝ)
    (hβ : 0 ≤ β) (hβ2 : 2 * β ≤ 1) (M : ℕ) :
    logProductPower β (6 + Real.log ((M + 1 : ℕ) : ℝ)) ≤
      2 * logProductPower β (6 + Real.log (M : ℝ)) := by
  by_cases hM0 : M = 0
  · subst M
    simp only [Nat.zero_add, Nat.cast_one, Nat.cast_zero, Real.log_zero, Real.log_one, add_zero]
    have hp : 0 ≤ logProductPower β 6 := by unfold logProductPower; positivity
    linarith
  have hm0 : (0 : ℝ) < M := by exact_mod_cast (Nat.pos_of_ne_zero hM0)
  have hm1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hlog0 : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg hm1
  let L : ℝ := 6 + Real.log (M : ℝ)
  let T : ℝ := 6 + Real.log ((M + 1 : ℕ) : ℝ)
  have hL6 : 6 ≤ L := by dsimp [L]; linarith
  have hL0 : 0 < L := by linarith
  have hLT : L ≤ T := by
    dsimp [L, T]
    linarith [Real.log_le_log hm0 (show (M : ℝ) ≤ ((M + 1 : ℕ) : ℝ) by push_cast; linarith)]
  have hT0 : 0 < T := hL0.trans_le hLT
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlog : Real.log ((M + 1 : ℕ) : ℝ) ≤ 1 + Real.log (M : ℝ) := by
    calc
      _ ≤ Real.log (2 * (M : ℝ)) := Real.log_le_log (by positivity) (by push_cast; linarith)
      _ = Real.log 2 + Real.log (M : ℝ) := Real.log_mul (by norm_num) hm0.ne'
      _ ≤ _ := by linarith
  have hTle : T ≤ 2 * L := by dsimp [T, L]; linarith
  have hp0 : 0 ≤ logProductPower β L := by
    unfold logProductPower
    exact Real.rpow_nonneg (mul_nonneg hL0.le (Real.log_nonneg (by linarith))) _
  have hr := (div_le_div_iff₀ hT0 hL0).mp (logProductPower_div_antitone β hβ hβ2 hL6 hLT)
  have hmul := mul_le_mul_of_nonneg_left hTle hp0
  change logProductPower β T ≤ 2 * logProductPower β L
  nlinarith

/-- Successor-normalized endpoint rate for the increasing Abel transfer. -/
theorem dampedMobius_half_cutoffs_loglog_stretched_rate :
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ,
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M -
        dampedMobiusHalfRangeLimit (1 / 2) le_rfl‖ ≤
        C * Real.exp (-a * logProductPower (1 / 11) (6 + Real.log ((M + 1 : ℕ) : ℝ))) := by
  obtain ⟨a, ha, C, hC, hc⟩ := dampedMobius_half_cutoffs_loglog_stretched_rate_unshifted
  refine ⟨a / 2, by positivity, C, hC, fun M => (hc M).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.exp_le_exp.mpr
  have hp := logProductPower_nat_succ_le_two (1 / 11) (by norm_num) (by norm_num) M
  nlinarith [mul_le_mul_of_nonneg_left hp ha.le]

end RiemannResearch.RH.Pareto
