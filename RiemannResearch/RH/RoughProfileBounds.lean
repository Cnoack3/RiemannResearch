import RiemannResearch.RH.RoughComponentHead
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Unconditional profile bounds for the diagonal rough-component energy

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md,
Section 8. The exact floor defect is retained before passing to the limit.
-/

namespace RiemannResearch.RH.Pareto

open scoped BigOperators Topology
open Filter OneBoundaryRepair

noncomputable section

private theorem floorBlock_eq_linear_defect (q k : ℕ) (hq : 0 < q) :
    floorBlock q k = (k : ℝ) / q - residue q k / q := by
  have h := floorBlock_mul q k
  have hqR : (q : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith

/-- Exact four-residue defect, before any estimate. -/
theorem roughHeadProfile_defect_exact (q k : ℕ) (hq : 0 < q) :
    roughHeadProfile q k - (k : ℝ) / (3 * (q : ℝ)) =
      -residue q k / q + residue (2 * q) k / ((2 * q : ℕ) : ℝ) +
        residue (3 * q) k / ((3 * q : ℕ) : ℝ) -
          residue (6 * q) k / ((6 * q : ℕ) : ℝ) := by
  unfold roughHeadProfile
  rw [floorBlock_eq_linear_defect q k hq,
    floorBlock_eq_linear_defect (2 * q) k (by omega),
    floorBlock_eq_linear_defect (3 * q) k (by omega),
    floorBlock_eq_linear_defect (6 * q) k (by omega)]
  push_cast
  ring

private theorem residue_ratio_bounds (q k : ℕ) (hq : 0 < q) :
    0 ≤ residue q k / (q : ℝ) ∧ residue q k / (q : ℝ) ≤ 1 := by
  have hqR : 0 < (q : ℝ) := by positivity
  have hres : residue q k ≤ (q : ℝ) := by
    change ((k % q : ℕ) : ℝ) ≤ (q : ℝ)
    exact_mod_cast (Nat.mod_lt k hq).le
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hqR.le
  · exact (div_le_one hqR).mpr hres

theorem roughHeadProfile_defect_bound (q k : ℕ) (hq : 0 < q) :
    |roughHeadProfile q k - (k : ℝ) / (3 * (q : ℝ))| ≤ 2 := by
  rw [roughHeadProfile_defect_exact q k hq]
  have h1 := residue_ratio_bounds q k hq
  have h2 := residue_ratio_bounds (2 * q) k (by omega)
  have h3 := residue_ratio_bounds (3 * q) k (by omega)
  have h6 := residue_ratio_bounds (6 * q) k (by omega)
  rw [neg_div]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem floorBlock_nonneg (q k : ℕ) : 0 ≤ floorBlock q k := Nat.cast_nonneg _

private theorem floorBlock_scaled_le (q a k : ℕ) (ha : 1 ≤ a) :
    (q : ℝ) * floorBlock (a * q) k ≤ (k : ℝ) := by
  have he := floorBlock_mul (a * q) k
  have hf := floorBlock_nonneg (a * q) k
  have hres : 0 ≤ residue (a * q) k := Nat.cast_nonneg _
  have hqa : (q : ℝ) ≤ ((a * q : ℕ) : ℝ) := by exact_mod_cast (by nlinarith : q ≤ a * q)
  nlinarith [mul_nonneg (sub_nonneg.mpr hqa) hf]

/-- A uniform summable majorant is available without evaluating an Euler product. -/
theorem roughHeadProfile_scaled_abs (q k : ℕ) :
    (q : ℝ) * |roughHeadProfile q k| ≤ 2 * (k : ℝ) := by
  have h1 := floorBlock_scaled_le q 1 k (by omega)
  have h2 := floorBlock_scaled_le q 2 k (by omega)
  have h3 := floorBlock_scaled_le q 3 k (by omega)
  have h6 := floorBlock_scaled_le q 6 k (by omega)
  simp only [one_mul] at h1
  have hp1 := mul_nonneg (Nat.cast_nonneg q) (floorBlock_nonneg q k)
  have hp2 := mul_nonneg (Nat.cast_nonneg q) (floorBlock_nonneg (2 * q) k)
  have hp3 := mul_nonneg (Nat.cast_nonneg q) (floorBlock_nonneg (3 * q) k)
  have hp6 := mul_nonneg (Nat.cast_nonneg q) (floorBlock_nonneg (6 * q) k)
  rw [← abs_of_nonneg (show (0:ℝ) ≤ q from Nat.cast_nonneg q), ← abs_mul]
  apply abs_le.mpr
  unfold roughHeadProfile
  constructor <;> nlinarith

theorem roughHeadProfile_weighted_square_bound (q k : ℕ) (hq : 0 < q) :
    0 ≤ positiveWeight k * (roughHeadProfile q k) ^ 2 ∧
      positiveWeight k * (roughHeadProfile q k) ^ 2 ≤ 4 / (q : ℝ) ^ 2 := by
  constructor
  · exact mul_nonneg (positiveWeight_nonneg k) (sq_nonneg _)
  have hqR : 0 < (q : ℝ) := by positivity
  have hb := roughHeadProfile_scaled_abs q k
  have hleft : 0 ≤ (q : ℝ) * |roughHeadProfile q k| := by positivity
  have hsq := mul_self_le_mul_self hleft hb
  have hs : (q : ℝ) ^ 2 * (roughHeadProfile q k) ^ 2 ≤ 4 * (k : ℝ) ^ 2 := by
    have hsq' : ((q : ℝ) * |roughHeadProfile q k|) ^ 2 ≤ (2 * (k : ℝ)) ^ 2 := by
      simpa only [pow_two] using hsq
    rw [mul_pow, sq_abs] at hsq'
    nlinarith
  have hw : positiveWeight k * (k : ℝ) ^ 2 ≤ 1 := by
    by_cases hk : k = 0
    · simp [hk, positiveWeight]
    · have hkR : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
      unfold positiveWeight
      rw [one_div_mul_eq_div]
      apply (div_le_one (by positivity : 0 < (k : ℝ) * ((k : ℝ) + 1))).mpr
      nlinarith
  apply (le_div_iff₀ (sq_pos_of_pos hqR)).mpr
  have hm := mul_le_mul_of_nonneg_left hs (positiveWeight_nonneg k)
  nlinarith

theorem roughHeadProfile_ratio_tendsto (q : ℕ) (hq : 0 < q) :
    Tendsto (fun n : ℕ => roughHeadProfile q (n + 1) / ((n : ℝ) + 1)) atTop
      (𝓝 (1 / (3 * (q : ℝ)))) := by
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    Filter.tendsto_atTop_mono (fun n : ℕ => show (n:ℝ) ≤ (n:ℝ)+1 by linarith)
      tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    hden.const_div_atTop 2
  have hb (n : ℕ) : ‖roughHeadProfile q (n + 1) / ((n : ℝ) + 1) -
      1 / (3 * (q : ℝ))‖ ≤ 2 / ((n : ℝ) + 1) := by
    have hd : 0 < (n : ℝ) + 1 := by positivity
    have hqR : (q : ℝ) ≠ 0 := by positivity
    have he : roughHeadProfile q (n + 1) / ((n : ℝ) + 1) -
        1 / (3 * (q : ℝ)) =
        (roughHeadProfile q (n + 1) - ((n : ℝ) + 1) / (3 * (q : ℝ))) /
          ((n : ℝ) + 1) := by
      field_simp <;> ring
    rw [Real.norm_eq_abs, he, abs_div, abs_of_pos hd]
    exact (div_le_div_iff_of_pos_right hd).mpr (by
      simpa only [Nat.cast_add, Nat.cast_one] using roughHeadProfile_defect_bound q (n + 1) hq)
  have hz := squeeze_zero_norm' (Eventually.of_forall hb) hsmall
  simpa only [sub_add_cancel, zero_add] using hz.add_const (1 / (3 * (q : ℝ)))

theorem roughHeadProfile_weighted_square_tendsto (q : ℕ) (hq : 0 < q) :
    Tendsto (fun n : ℕ => positiveWeight (n + 1) * (roughHeadProfile q (n + 1)) ^ 2)
      atTop (𝓝 (1 / (9 * (q : ℝ) ^ 2))) := by
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    Filter.tendsto_atTop_mono (fun n : ℕ => show (n:ℝ) ≤ (n:ℝ)+2 by linarith)
      tendsto_natCast_atTop_atTop
  have hi := hden.const_div_atTop (1 : ℝ)
  have hone : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 (1:ℝ)) := tendsto_const_nhds
  have ht := ((roughHeadProfile_ratio_tendsto q hq).pow 2).mul
    (hone.sub hi)
  have he (n : ℕ) : positiveWeight (n + 1) * (roughHeadProfile q (n + 1)) ^ 2 =
      (roughHeadProfile q (n + 1) / ((n : ℝ) + 1)) ^ 2 *
        (1 - 1 / ((n : ℝ) + 2)) := by
    unfold positiveWeight
    push_cast
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp <;> ring
  convert ht using 1
  · funext n
    exact he n
  · congr 1
    have hqR : (q : ℝ) ≠ 0 := by positivity
    field_simp <;> ring

/-- The diagonal head energy of one rough profile, divided by the head length. -/
def roughComponentAverage (q N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N,
    positiveWeight (k + 1) * (roughHeadProfile q (k + 1)) ^ 2

theorem roughComponentAverage_tendsto (q : ℕ) (hq : 0 < q) :
    Tendsto (roughComponentAverage q) atTop (𝓝 (1 / (9 * (q : ℝ) ^ 2))) :=
  (roughHeadProfile_weighted_square_tendsto q hq).cesaro

theorem roughComponentAverage_bounds (q N : ℕ) (hq : 0 < q) :
    0 ≤ roughComponentAverage q N ∧ roughComponentAverage q N ≤ 4 / (q : ℝ) ^ 2 := by
  have hsum : 0 ≤ ∑ k ∈ Finset.range N,
      positiveWeight (k + 1) * (roughHeadProfile q (k + 1)) ^ 2 := by
    exact Finset.sum_nonneg (fun k hk => (roughHeadProfile_weighted_square_bound q (k + 1) hq).1)
  constructor
  · exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N)) hsum
  · by_cases hN : N = 0
    · simp only [roughComponentAverage, hN, Nat.cast_zero, inv_zero, zero_mul]
      positivity
    have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN
    have hl : (∑ k ∈ Finset.range N,
        positiveWeight (k + 1) * (roughHeadProfile q (k + 1)) ^ 2) ≤
        ∑ k ∈ Finset.range N, 4 / (q : ℝ) ^ 2 := by
      exact Finset.sum_le_sum (fun k hk => (roughHeadProfile_weighted_square_bound q (k + 1) hq).2)
    have hm := mul_le_mul_of_nonneg_left hl (inv_nonneg.mpr (Nat.cast_nonneg N))
    simpa [roughComponentAverage, Finset.sum_const, nsmul_eq_mul, hNR, ← mul_assoc] using hm

end
end RiemannResearch.RH.Pareto
