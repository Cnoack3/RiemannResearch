/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.FiniteWeightedEnergyComparison
import RiemannResearch.RH.DampedMobiusHeadApproximation
import RiemannResearch.RH.DampedMobiusExactSignedHeadLimits
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Joint signed-head convergence, including the half-damping endpoint

At every epsilon >= 1 / 2 the actual signed off-diagonal tends to energy
minus the actual diagonal when both cutoffs diverge and the physical head
is eventually no larger than the residue cutoff. The endpoint uses a
signed density-tail logarithmic saving from the existing PNT provider.
Equal cutoffs are allowed. No off-diagonal bound is assumed.

Source for the underlying unconditional membership statement: J.-F.
Burnol, "On an analytic estimate in the theory of the Riemann zeta function
and a theorem of Baez-Duarte", Section 4, Lemma 4.1,
https://arxiv.org/abs/math/0202166. The simultaneous-limit argument uses
the repository's exact head-error identity, weighted Cauchy--Schwarz and
dominated convergence. No novelty claim is made. Subhalf finite energy
and absolute off-diagonal summability are not asserted.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto

/-- A proved vanishing moving-head error supplies the exact signed limit.
Actual centered finite energy remains an explicit premise. -/
theorem dampedMobius_offDiagonal_joint_tendsto_of_head_error
    {ε : ℝ} (hε : 0 < ε) (H M : ℕ → ℕ)
    (hH : Tendsto H atTop atTop) (hM : Tendsto M atTop atTop)
    (henergy : Summable (fun n : ℕ => positiveWeight n *
      (dampedMobiusPrefix ε n - (n : ℝ) *
        (1 / riemannZeta (1 + (ε : ℂ))).re) ^ 2))
    (herr : Tendsto (fun j => ∑ n ∈ Finset.range (H j), positiveWeight n *
      (hilbertSequence (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) (M j)) n -
        (dampedMobiusPrefix ε n - (n : ℝ) *
          (1 / riemannZeta (1 + (ε : ℂ))).re)) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun j => dampedMobiusHeadOffDiagonal ε (H j) (M j)) atTop
      (𝓝 ((∑' n : ℕ, positiveWeight n *
        (dampedMobiusPrefix ε n - (n : ℝ) *
          (1 / riemannZeta (1 + (ε : ℂ))).re) ^ 2) - dampedMobiusExactDiagonal ε)) := by
  let g := fun n => dampedMobiusPrefix ε n - (n : ℝ) *
    (1 / riemannZeta (1 + (ε : ℂ))).re
  have hd := RiemannResearch.Analysis.sum_weighted_sq_sub_tendsto_zero
    (fun j => Finset.range (H j)) positiveWeight
    (fun j => hilbertSequence (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) (M j)))
    g positiveWeight_nonneg (∑' n, positiveWeight n * (g n) ^ 2)
    (fun j => Summable.sum_le_tsum _ (fun n _ => mul_nonneg (positiveWeight_nonneg n)
      (sq_nonneg _)) henergy) herr
  have he := hd.add (henergy.hasSum.tendsto_sum_nat.comp hH)
  simp only [g, Function.comp_apply, sub_add_cancel, zero_add] at he
  have ht := he.sub (dampedMobius_headDiagonal_joint_tendsto hε H M hH hM)
  convert ht using 1
  funext j
  have hi := dampedMobius_partial_head_eq_signed ε (H j) (M j)
  simp only [paretoHeadPairing, mul_assoc, ← pow_two] at hi
  linarith

open RiemannResearch.Analysis
open RiemannResearch.NumberTheory.PrimeNumberTheorem

/-- PNT supplies a signed density-tail saving at the half-damping endpoint. -/
theorem dampedMobius_half_density_tail_log_bound :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ M : ℕ, 1 ≤ M →
      |(1 / riemannZeta (1 + ((1 / 2 : ℝ) : ℂ))).re -
        ∑ m ∈ Finset.range M,
          dampedMobiusWeight (1 / 2) (m + 1) / ((m + 1 : ℕ) : ℝ)| ≤
        D * (M : ℝ) ^ (-1 / 2 : ℝ) *
          (6 + Real.log (M : ℝ)) ^ (-3 / 2 : ℝ) := by
  let c := fun n : ℕ => (ArithmeticFunction.moebius n : ℝ)
  have hc : c 0 = 0 := by simp [c]
  have hterm (n : ℕ) : c n * (n : ℝ) ^ (-3 / 2 : ℝ) =
      dampedMobiusWeight (1 / 2) n / (n : ℝ) := by
    rw [dampedMobiusWeight_div]
    norm_num only [show (1 + (1 / 2 : ℝ)) = 3 / 2 by norm_num]
    rw [Real.rpow_neg (Nat.cast_nonneg n)]
    simp only [c, div_eq_mul_inv]
  have hs : HasSum (fun n => c n * (n : ℝ) ^ (-3 / 2 : ℝ))
      (1 / riemannZeta (1 + ((1 / 2 : ℝ) : ℂ))).re := by
    simp_rw [hterm]
    have h := (hasSum_nat_add_iff
      (f := fun n => dampedMobiusWeight (1 / 2) n / (n : ℝ)) 1).mp
      (dampedMobius_density_hasSum (by norm_num : (0 : ℝ) < 1 / 2))
    simpa only [Finset.sum_range_one, dampedMobiusWeight_zero, Nat.cast_zero,
      zero_div, add_zero] using h
  have hp (M : ℕ) : threeHalfWeightedPrefix c (M : ℝ) =
      ∑ m ∈ Finset.range M, dampedMobiusWeight (1 / 2) (m + 1) / ((m + 1 : ℕ) : ℝ) := by
    unfold threeHalfWeightedPrefix
    rw [Nat.floor_natCast]
    have hi : Finset.Icc 0 M = Finset.range (M + 1) := by ext n; simp
    rw [hi, Finset.sum_range_succ']
    simp only [hc, zero_mul, add_zero, hterm]
  obtain ⟨B, hB, hM⟩ := M_shiftedLog_threeHalves_bound
  have hMu : ∀ x : ℝ, 1 ≤ x → |arithmeticSummatory c x| ≤
      B * x * shiftedLogProfile x := by
    have hid (x : ℝ) : arithmeticSummatory c x = M x := by
      unfold arithmeticSummatory M
      apply Finset.sum_congr
      · ext n
        simp
      · intro n hn
        rfl
    simpa only [hid, shiftedLogProfile] using hM
  refine ⟨5 * B, by positivity, ?_⟩
  intro M hM
  have h := threeHalfWeightedPrefix_tail_bound c hc hB hMu hs.summable hM
  simpa only [hs.tsum_eq, hp, shiftedLogProfile] using h

/-- The entire signed head error vanishes logarithmically even when the
two cutoffs are equal. All arithmetic hypotheses have been discharged. -/
theorem dampedMobius_half_head_error_log_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ H M : ℕ, H ≤ M → 1 ≤ M →
      (∑ n ∈ Finset.range H, positiveWeight n *
        (hilbertSequence (arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) M) n -
          (dampedMobiusPrefix (1 / 2) n - (n : ℝ) *
            (1 / riemannZeta (1 + ((1 / 2 : ℝ) : ℂ))).re)) ^ 2) ≤
        K * (6 + Real.log (M : ℝ)) ^ (-3 : ℝ) := by
  obtain ⟨D, hD, htail⟩ := dampedMobius_half_density_tail_log_bound
  refine ⟨D ^ 2, sq_nonneg _, ?_⟩
  intro H M hHM hM
  have hMp : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hLp : 0 < 6 + Real.log (M : ℝ) :=
    shiftedLog_pos (by exact_mod_cast hM)
  have hsq := (sq_le_sq₀ (abs_nonneg _) (by positivity :
    0 ≤ D * (M : ℝ) ^ (-1 / 2 : ℝ) * (6 + Real.log (M : ℝ)) ^ (-3 / 2 : ℝ))).mpr
    (htail M hM)
  rw [sq_abs] at hsq
  simp only [dampedMobiusPrefix]
  rw [arithmeticFloorPartial_head_error _ _ H M hHM]
  calc
    _ ≤ (D * (M : ℝ) ^ (-1 / 2 : ℝ) *
        (6 + Real.log (M : ℝ)) ^ (-3 / 2 : ℝ)) ^ 2 * (M : ℝ) :=
      mul_le_mul hsq ((paretoHead_linear_mass_le H).trans (by exact_mod_cast hHM))
        (Finset.sum_nonneg (fun n _ => mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _)))
        (sq_nonneg _)
    _ = _ := by
      have hm : ((M : ℝ) ^ (-1 / 2 : ℝ)) ^ 2 = (M : ℝ)⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hMp.le]
        norm_num [Real.rpow_neg]
      have hl : ((6 + Real.log (M : ℝ)) ^ (-3 / 2 : ℝ)) ^ 2 =
          (6 + Real.log (M : ℝ)) ^ (-3 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hLp.le]
        norm_num
      rw [mul_pow, mul_pow, hm, hl]
      field_simp

/-- Along every pair of cutoffs with H <= M eventually and M tending to
infinity, the half-damped signed approximation error tends to zero. -/
theorem dampedMobius_half_head_error_tendsto
    (H M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (hHM : ∀ᶠ j in atTop, H j ≤ M j) :
    Tendsto (fun j => ∑ n ∈ Finset.range (H j), positiveWeight n *
      (hilbertSequence (arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) (M j)) n -
        (dampedMobiusPrefix (1 / 2) n - (n : ℝ) *
          (1 / riemannZeta (1 + ((1 / 2 : ℝ) : ℂ))).re)) ^ 2) atTop (𝓝 0) := by
  obtain ⟨K, hK, hb⟩ := dampedMobius_half_head_error_log_bound
  have hlog : Tendsto (fun j => Real.log (M j : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hM)
  have hL : Tendsto (fun j => 6 + Real.log (M j : ℝ)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [hlog.eventually (eventually_ge_atTop (b-6))] with j hj
    linarith
  have ht := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3)).comp hL).const_mul K
  apply squeeze_zero' _ _ (by simpa only [mul_zero] using ht)
  · exact Eventually.of_forall (fun j => Finset.sum_nonneg
      (fun n _ => mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _)))
  · filter_upwards [hHM, hM.eventually (eventually_ge_atTop 1)] with j hj hj1
    exact hb (H j) (M j) hj hj1

/-- Unconditional joint signed limit at the critical half-damping endpoint.
Both cutoffs grow together; no off-diagonal bound is assumed. -/
theorem dampedMobius_half_offDiagonal_joint_tendsto
    (H M : ℕ → ℕ) (hH : Tendsto H atTop atTop) (hM : Tendsto M atTop atTop)
    (hHM : ∀ᶠ j in atTop, H j ≤ M j) :
    Tendsto (fun j => dampedMobiusHeadOffDiagonal (1 / 2) (H j) (M j)) atTop
      (𝓝 ((∑' n : ℕ, positiveWeight n *
        (dampedMobiusPrefix (1 / 2) n - (n : ℝ) *
          (1 / riemannZeta (1 + ((1 / 2 : ℝ) : ℂ))).re) ^ 2) -
          dampedMobiusExactDiagonal (1 / 2))) :=
  dampedMobius_offDiagonal_joint_tendsto_of_head_error (by norm_num)
    H M hH hM (centered_dampedMobius_square_summable_of_half_le le_rfl)
    (dampedMobius_half_head_error_tendsto H M hM hHM)


/-- In the strict range the elementary density tail already makes the
moving-head error vanish whenever H <= M eventually. -/
theorem dampedMobius_head_error_tendsto_of_half_lt
    {ε : ℝ} (hε : (1 / 2 : ℝ) < ε) (H M : ℕ → ℕ)
    (hM : Tendsto M atTop atTop) (hHM : ∀ᶠ j in atTop, H j ≤ M j) :
    Tendsto (fun j => ∑ n ∈ Finset.range (H j), positiveWeight n *
      (hilbertSequence (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) (M j)) n -
        (dampedMobiusPrefix ε n - (n : ℝ) *
          (1 / riemannZeta (1 + (ε : ℂ))).re)) ^ 2) atTop (𝓝 0) := by
  have hpos : 0 < ε := by linarith
  have ht := ((tendsto_rpow_neg_atTop (by linarith : 0 < 2 * ε-1)).comp
    (tendsto_natCast_atTop_atTop.comp hM)).div_const (ε ^ 2)
  apply squeeze_zero' _ _ (by simpa only [zero_div] using ht)
  · exact Eventually.of_forall (fun j => Finset.sum_nonneg
      (fun n _ => mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _)))
  · filter_upwards [hHM, hM.eventually (eventually_ge_atTop 1)] with j hj hj1
    have hMp : (0 : ℝ) < M j := by exact_mod_cast (show 0 < M j by omega)
    calc
      _ ≤ (H j : ℝ) * (M j : ℝ) ^ (-2 * ε) / ε ^ 2 :=
        dampedMobius_head_error_le hpos _ _ hj hj1
      _ ≤ (M j : ℝ) * (M j : ℝ) ^ (-2 * ε) / ε ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hj)
          (Real.rpow_nonneg hMp.le _)
      _ = _ := by
        congr 1
        calc
          _ = (M j : ℝ) ^ (1 : ℝ) * (M j : ℝ) ^ (-2 * ε) := by rw [Real.rpow_one]
          _ = (M j : ℝ) ^ (1 + -2 * ε) := (Real.rpow_add hMp _ _).symm
          _ = _ := by congr 1; ring

/-- The exact joint signed limit throughout the unconditional range,
including equal cutoffs at epsilon = 1 / 2. -/
theorem dampedMobius_offDiagonal_joint_tendsto_of_half_le
    {ε : ℝ} (hε : (1 / 2 : ℝ) ≤ ε) (H M : ℕ → ℕ)
    (hH : Tendsto H atTop atTop) (hM : Tendsto M atTop atTop)
    (hHM : ∀ᶠ j in atTop, H j ≤ M j) :
    Tendsto (fun j => dampedMobiusHeadOffDiagonal ε (H j) (M j)) atTop
      (𝓝 ((∑' n : ℕ, positiveWeight n *
        (dampedMobiusPrefix ε n - (n : ℝ) *
          (1 / riemannZeta (1 + (ε : ℂ))).re) ^ 2) - dampedMobiusExactDiagonal ε)) := by
  rcases eq_or_lt_of_le hε with heq | hlt
  · subst ε
    exact dampedMobius_half_offDiagonal_joint_tendsto H M hH hM hHM
  · exact dampedMobius_offDiagonal_joint_tendsto_of_head_error
      (by linarith) H M hH hM (centered_dampedMobius_square_summable_of_half_le hε)
      (dampedMobius_head_error_tendsto_of_half_lt hlt H M hM hHM)

/-- A concrete unconditional signed upper bound on the equal-cutoff path
throughout the full half-damping range. -/
theorem dampedMobius_equal_cutoff_signed_bound_of_half_le
    {ε : ℝ} (hε : (1 / 2 : ℝ) ≤ ε) :
    ∃ B : ℝ, ∀ H : ℕ, dampedMobiusHeadOffDiagonal ε H H ≤ B := by
  have h := dampedMobius_offDiagonal_joint_tendsto_of_half_le hε
    id id tendsto_id tendsto_id (Eventually.of_forall (fun _ => le_rfl))
  rw [← Nat.cofinite_eq_atTop] at h
  obtain ⟨B, hB⟩ := h.bddAbove_range_of_cofinite
  exact ⟨B, fun H => hB (Set.mem_range_self H)⟩

end RiemannResearch.RH.Pareto
