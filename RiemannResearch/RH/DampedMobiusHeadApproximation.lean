/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.DampedMobiusSignedHeadClosure
import RiemannResearch.Analysis.PSeriesTail

/-!
# Quantitative approximation after signed finite-head cancellation

The existing exact head-error identity sums the distant-conductor tail
before squaring. Only that scalar tail is bounded by absolute values here.
The resulting estimate holds for every positive damping, without RH.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto

theorem dampedMobius_density_term_abs_le (ε : ℝ) (m : ℕ) :
    |dampedMobiusWeight ε (m+1) / ((m+1 : ℕ) : ℝ)| ≤
      ((m+1 : ℕ) : ℝ) ^ (-ε-1) := by
  have hm : (0 : ℝ) < ((m+1 : ℕ) : ℝ) := by positivity
  have hmu : |(ArithmeticFunction.moebius (m+1) : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := m+1))
  rw [abs_div, abs_of_pos hm, dampedMobiusWeight, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg hm.le _)]
  calc
    _ ≤ (1 * ((m+1 : ℕ) : ℝ) ^ (-ε)) / ((m+1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hmu (Real.rpow_nonneg hm.le _)) hm.le
    _ = _ := by
      rw [one_mul]
      simpa only [Real.rpow_one] using (Real.rpow_sub hm (-ε) 1).symm

/-- Explicit scalar density error; no Hilbert summability premise occurs. -/
theorem dampedMobius_density_tail_le {ε : ℝ} (hε : 0 < ε)
    {M : ℕ} (hM : 1 ≤ M) :
    |(1 / riemannZeta (1 + (ε : ℂ))).re -
      ∑ m ∈ Finset.range M, dampedMobiusWeight ε (m+1) / ((m+1 : ℕ) : ℝ)| ≤
      (M : ℝ) ^ (-ε) / ε := by
  let a : ℕ → ℝ := fun m => dampedMobiusWeight ε (m+1) / ((m+1 : ℕ) : ℝ)
  have hs : HasSum a (1 / riemannZeta (1 + (ε : ℂ))).re := dampedMobius_density_hasSum hε
  have hp : Summable (fun m : ℕ => ((m+1 : ℕ) : ℝ) ^ (-ε-1)) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_rpow.mpr (by linarith))
  have ha : Summable (fun m => |a m|) :=
    hp.of_nonneg_of_le (fun _ => abs_nonneg _) (dampedMobius_density_term_abs_le ε)
  have ht := ((hasSum_nat_add_iff' M).mpr hs).tsum_eq
  change |(1 / riemannZeta (1 + (ε : ℂ))).re - ∑ m ∈ Finset.range M, a m| ≤ _
  rw [← ht]
  calc
    |∑' j, a (j+M)| ≤ ∑' j, |a (j+M)| := by
      have hn : Summable (fun j => ‖a (j+M)‖) := by
        simpa only [Real.norm_eq_abs] using (summable_nat_add_iff M).mpr ha
      simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hn
    _ ≤ ∑' j : ℕ, ((j+M+1 : ℕ) : ℝ) ^ (-ε-1) :=
      ((summable_nat_add_iff M).mpr ha).tsum_le_tsum
        (fun j => dampedMobius_density_term_abs_le ε (j+M))
        ((summable_nat_add_iff M).mpr hp)
    _ ≤ _ := by
      have h := Real.tsum_nat_rpow_tail_le (p := ε+1) (by linarith) hM
      simpa only [show -(ε+1) = -ε-1 by ring,
        show 1-(ε+1) = -ε by ring, show ε+1-1 = ε by ring] using h

theorem paretoHead_linear_mass_le (H : ℕ) :
    (∑ n ∈ Finset.range H, positiveWeight n * (n : ℝ)^2) ≤ H := by
  calc
    _ ≤ ∑ _n ∈ Finset.range H, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hn0 : n = 0
      · simp [hn0]
      · have hp : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
        unfold positiveWeight
        rw [one_div, inv_mul_eq_div]
        apply (div_le_one (by positivity : (0 : ℝ) < (n : ℝ)*((n : ℝ)+1))).mpr
        nlinarith
    _ = _ := by simp

/-- Quantitative error on an entire head after exact signed-tail collapse. -/
theorem dampedMobius_head_error_le {ε : ℝ} (hε : 0 < ε)
    (H M : ℕ) (hHM : H ≤ M) (hM : 1 ≤ M) :
    (∑ n ∈ Finset.range H, positiveWeight n *
      (hilbertSequence (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M) n -
        (dampedMobiusPrefix ε n -
          (n : ℝ) * (1 / riemannZeta (1 + (ε : ℂ))).re))^2) ≤
      (H : ℝ) * (M : ℝ)^(-2*ε) / ε^2 := by
  simp only [dampedMobiusPrefix]
  rw [arithmeticFloorPartial_head_error _ _ H M hHM]
  have ht := dampedMobius_density_tail_le hε hM
  have hsq := sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ (M : ℝ)^(-ε)/ε) |>.mpr ht
  rw [sq_abs] at hsq
  have hMp : (0 : ℝ) < M := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hM)
  calc
    _ ≤ ((M : ℝ)^(-ε)/ε)^2 * (H : ℝ) :=
      mul_le_mul hsq (paretoHead_linear_mass_le H)
        (Finset.sum_nonneg (fun n _ => mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _)))
        (sq_nonneg _)
    _ = _ := by
      have hp2 : ((M : ℝ)^(-ε))^2 = (M : ℝ)^(-2*ε) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hMp.le]
        congr 1
        norm_num
        ring
      rw [div_pow, hp2]
      ring

end RiemannResearch.RH.Pareto
