/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFloorDilationEnergy
import RiemannResearch.RH.QDilationMoments
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Two sharp bounds for inverse-square floor dilation

Source: user-requested improvement of the Full-Conductor RH Reproducibility
Supplement, 6 November 2026. Direct comparison of its complete block weights
gives the optimal lower energy constant. Physical unit spikes approach the
upper constant, proving that the previously proved upper bound is the exact
operator norm, although no nonzero vector attains it when m > 1.
These are unconditional operator facts and do not imply legal approximation.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QFloorDilation
open ZetaTwoHilbert ZetaTwoProbability

/-- Exact minimum squared singular ratio, attained at physical site one. -/
def floorDilationLowerConstant (m : ℕ) : ℝ :=
  ∑ r ∈ Finset.range m, 1 / (((m + r : ℕ) : ℝ) ^ 2)

theorem qBlockWeight_ge_lowerConstant (m k : ℕ) (hm : 0 < m) (hk : 0 < k) :
    floorDilationLowerConstant m * positiveQWeight k ≤ qBlockWeight m k := by
  unfold floorDilationLowerConstant qBlockWeight
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro r hr
  have hmk : (0 : ℝ) < (m * k + r : ℕ) := by
    exact_mod_cast (lt_of_lt_of_le (Nat.mul_pos hm hk) (Nat.le_add_right _ _))
  have hcmp : (m * k + r : ℕ) ≤ (m + r) * k := by
    nlinarith
  have hw : positiveQWeight ((m + r) * k) ≤ positiveQWeight (m * k + r) := by
    have hZ := zetaTwo_pos
    have hc : ((m * k + r : ℕ) : ℝ) ≤ (((m + r) * k : ℕ) : ℝ) :=
      Nat.cast_le.mpr hcmp
    unfold positiveQWeight
    gcongr
  rw [positiveQWeight_mul] at hw
  simpa only [one_div_mul_eq_div] using hw

theorem floorDilationLowerConstant_pos (m : ℕ) (hm : 0 < m) :
    0 < floorDilationLowerConstant m := by
  unfold floorDilationLowerConstant
  apply Finset.sum_pos'
  · intro r hr
    positivity
  · refine ⟨0, Finset.mem_range.mpr hm, ?_⟩
    have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
    simp only [Nat.add_zero]
    positivity

/-- Full infinite lower energy bound; every physical block is retained. -/
theorem floorDilation_norm_sq_ge (m : ℕ) (hm : 0 < m) (f : QHilbert) :
    floorDilationLowerConstant m * ‖f‖ ^ 2 ≤ ‖floorDilation m hm f‖ ^ 2 := by
  rw [qNorm_weighted_sq, floorDilation_norm_sq_eq_blocks, ← tsum_mul_left]
  apply Summable.tsum_le_tsum _
    ((qSequence_square_summable f).mul_left (floorDilationLowerConstant m))
    (qBlockEnergy_summable m hm f)
  intro k
  by_cases hk : k = 0
  · simp [hk]
  · simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right
        (qBlockWeight_ge_lowerConstant m k hm (Nat.pos_of_ne_zero hk)) (sq_nonneg _)

/-- Lower complete-block estimate useful for the exact upper norm. -/
theorem qBlockWeight_ge_next (m k : ℕ) (hm : 0 < m) (hk : 0 < k) :
    positiveQWeight (k + 1) / (m : ℝ) ≤ qBlockWeight m k := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hm)
  calc
    positiveQWeight (k + 1) / (m : ℝ) =
        (m : ℝ) * positiveQWeight (m * (k + 1)) := by
      rw [positiveQWeight_mul]
      field_simp [hmR]
    _ = ∑ r ∈ Finset.range m, positiveQWeight (m * (k + 1)) := by simp
    _ ≤ qBlockWeight m k := by
      apply Finset.sum_le_sum
      intro r hr
      have hmk : (0 : ℝ) < (m * k + r : ℕ) := by
        exact_mod_cast (lt_of_lt_of_le (Nat.mul_pos hm hk) (Nat.le_add_right _ _))
      have hc : ((m * k + r : ℕ) : ℝ) ≤ ((m * (k + 1) : ℕ) : ℝ) := by
        exact_mod_cast (show m * k + r ≤ m * (k + 1) by
          have := Finset.mem_range.mp hr
          nlinarith)
      have hZ := zetaTwo_pos
      unfold positiveQWeight
      gcongr

/-- A unit spike's exact energy is its complete block-to-site mass ratio. -/
theorem floorDilation_single_norm_sq (m : ℕ) (hm : 0 < m) (k : ℕ) :
    ‖floorDilation m hm (lp.single 2 k (1 : ℝ))‖ ^ 2 =
      qBlockWeight m (k + 1) / positiveQWeight (k + 1) := by
  have hseq (j : ℕ) :
      qSequence (lp.single 2 k (1 : ℝ)) j =
        if j = k + 1 then 1 / Real.sqrt (qWeight k) else 0 := by
    cases j with
    | zero => simp
    | succ j =>
        by_cases hj : j = k
        · subst j
          simp [qSequence, lp.single_apply]
        · have hj' : j + 1 ≠ k + 1 := by omega
          simp [qSequence, lp.single_apply, hj]
  rw [floorDilation_norm_sq_eq_blocks]
  simp_rw [hseq]
  simp only [ite_pow, one_div_pow, zero_pow (by decide : 2 ≠ 0),
    mul_ite, mul_zero, tsum_ite_eq, Real.sq_sqrt (qWeight_pos k).le]
  simp only [qWeight, mul_one_div]

theorem floorDilationLowerConstant_eq_ratio (m : ℕ) :
    floorDilationLowerConstant m =
      qBlockWeight m 1 / positiveQWeight 1 := by
  unfold floorDilationLowerConstant qBlockWeight
  simp only [Nat.mul_one]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro r hr
  unfold positiveQWeight
  have hZ := ne_of_gt zetaTwo_pos
  by_cases hmr : m + r = 0
  · simp [hmr]
  · have hmrR : (((m + r : ℕ) : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hmr
    field_simp [hZ, hmrR]
    <;> norm_num

/-- Characterization of every possible global lower energy constant. -/
theorem floorDilation_lower_bound_iff (m : ℕ) (hm : 0 < m) (c : ℝ) :
    (∀ f : QHilbert, c * ‖f‖ ^ 2 ≤ ‖floorDilation m hm f‖ ^ 2) ↔
      c ≤ floorDilationLowerConstant m := by
  constructor
  · intro h
    have hh := h (lp.single 2 0 (1 : ℝ))
    rw [lp.norm_single (by norm_num : (0 : ENNReal) < 2),
      norm_one, one_pow, mul_one, floorDilation_single_norm_sq,
      ← floorDilationLowerConstant_eq_ratio] at hh
    exact hh
  · intro hc f
    exact (mul_le_mul_of_nonneg_right hc (sq_nonneg _)).trans
      (floorDilation_norm_sq_ge m hm f)

theorem floorDilation_injective (m : ℕ) (hm : 0 < m) :
    Function.Injective (floorDilation m hm) := by
  intro f g h
  have hz : floorDilation m hm (f - g) = 0 := by
    rw [map_sub, h, sub_self]
  have hb := floorDilation_norm_sq_ge m hm (f - g)
  rw [hz, norm_zero, zero_pow (by decide : 2 ≠ 0)] at hb
  have he : ‖f - g‖ ^ 2 = 0 := by
    have hc := floorDilationLowerConstant_pos m hm
    nlinarith [sq_nonneg ‖f - g‖]
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp he))

/-- Every physical unit spike bounds the squared operator norm from below. -/
theorem qBlockRatio_le_floorDilation_opNorm_sq (m : ℕ) (hm : 0 < m) (k : ℕ) :
    qBlockWeight m (k + 1) / positiveQWeight (k + 1) ≤
      ‖floorDilation m hm‖ ^ 2 := by
  have h := (floorDilation m hm).le_opNorm (lp.single 2 k (1 : ℝ))
  rw [lp.norm_single (by norm_num : (0 : ENNReal) < 2), norm_one, mul_one] at h
  have hs := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr h
  rwa [floorDilation_single_norm_sq] at hs

/-- The upper block ratio approaches 1/m along physical spikes. -/
theorem floorDilation_opNorm_sq_ge_sharp (m : ℕ) (hm : 0 < m) :
    1 / (m : ℝ) ≤ ‖floorDilation m hm‖ ^ 2 := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hm)
  have hbound (k : ℕ) :
      (((k : ℝ) + 1) / ((k : ℝ) + 2)) ^ 2 / (m : ℝ) ≤
        ‖floorDilation m hm‖ ^ 2 := by
    have hp : 0 < positiveQWeight (k + 1) := by
      have hZ := zetaTwo_pos
      unfold positiveQWeight
      positivity
    calc
      _ = (positiveQWeight ((k + 1) + 1) / (m : ℝ)) /
          positiveQWeight (k + 1) := by
        unfold positiveQWeight
        push_cast
        have h1 : (k : ℝ) + 1 ≠ 0 := by positivity
        have h2 : (k : ℝ) + 1 + 1 ≠ 0 := by positivity
        field_simp [hmR, ne_of_gt zetaTwo_pos, h1, h2]
        <;> ring
      _ ≤ qBlockWeight m (k + 1) / positiveQWeight (k + 1) :=
        div_le_div_of_nonneg_right
          (qBlockWeight_ge_next m (k + 1) hm (Nat.succ_pos k)) hp.le
      _ ≤ _ := qBlockRatio_le_floorDilation_opNorm_sq m hm k
  have hden : Tendsto (fun k : ℕ => (k : ℝ) + 2) atTop atTop := by
    apply tendsto_atTop_mono (fun k => ?_) (tendsto_natCast_atTop_atTop (R := ℝ))
    linarith
  have hz : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 2)) atTop (𝓝 0) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).div_atTop hden
  have hrat : Tendsto
      (fun k : ℕ => (((k : ℝ) + 1) / ((k : ℝ) + 2)) ^ 2 / (m : ℝ))
      atTop (𝓝 (1 / (m : ℝ))) := by
    have ht := (((tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hz).pow 2).div_const (m : ℝ)
    convert ht using 1
    · funext k
      have hk : (k : ℝ) + 2 ≠ 0 := by positivity
      field_simp [hk]
      <;> ring
    · simp
  exact le_of_tendsto hrat (Eventually.of_forall hbound)

/-- Exact operator norm. Strict loss at each nonzero vector is nonattainment,
not a smaller uniform norm. -/
theorem floorDilation_opNorm_eq_sharp (m : ℕ) (hm : 0 < m) :
    ‖floorDilation m hm‖ = Real.sqrt (1 / (m : ℝ)) := by
  have hupper := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr
    (floorDilation_opNorm_le_sharp m hm)
  have hsq := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 / (m : ℝ))
  rw [hsq] at hupper
  have hlower := floorDilation_opNorm_sq_ge_sharp m hm
  nlinarith [norm_nonneg (floorDilation m hm), Real.sqrt_nonneg (1 / (m : ℝ))]

end RiemannResearch.RH.QFloorDilation
