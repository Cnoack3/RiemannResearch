/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.MontgomeryPrimeDiagonalAbel
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! The exact integral of the squared von Mangoldt prefix against the two Montgomery weights.
Uses the two branches of `primeDiagonal_eq_edge_kernel` and the finite Abel formula in mathlib. -/

open MeasureTheory Set Filter
open scoped BigOperators ArithmeticFunction Topology
noncomputable section
namespace RiemannResearch.Analysis.MontgomeryHorizontalBessel

private theorem mangoldt_sq_le_four_mul (n : ℕ) : (Λ n) ^ 2 ≤ 4 * (n : ℝ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn' : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hs := Real.sqrt_pos.mpr hn'
  have he := Real.log_pow (Real.sqrt n) 2
  rw [Real.sq_sqrt hn'.le] at he
  norm_num at he
  have hlog := Real.log_le_sub_one_of_pos hs
  have hu : Λ n ≤ 2 * Real.sqrt n := by
    linarith [ArithmeticFunction.vonMangoldt_le_log (n := n)]
  have hv := mul_self_le_mul_self ArithmeticFunction.vonMangoldt_nonneg hu
  nlinarith [Real.sq_sqrt hn'.le]

theorem mangoldtSquarePrefix_integrableOn_Ioc (x : ℝ) :
    IntegrableOn (fun t : ℝ => ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, (Λ n) ^ 2) (Ioc 1 x) := by
  have hc : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc 1 x) :=
    continuousOn_const.integrableOn_Icc
  simpa using (integrableOn_mul_sum_Icc (fun n : ℕ => (Λ n) ^ 2) zero_le_one hc).mono_set
    Ioc_subset_Icc_self

private theorem prefix_le_quadratic {t : ℝ} (ht : 1 ≤ t) :
    ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, (Λ n) ^ 2 ≤ 8 * t ^ 2 := by
  have ht0 := zero_le_one.trans ht
  calc
    _ ≤ ∑ _n ∈ Finset.Icc 0 ⌊t⌋₊, 4 * t := Finset.sum_le_sum fun n hn =>
      (mangoldt_sq_le_four_mul n).trans (by
        have h := (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2 : (n : ℝ) ≤ ⌊t⌋₊).trans
          (Nat.floor_le ht0)
        linarith)
    _ ≤ 8 * t ^ 2 := by
      simp only [Finset.sum_const, Nat.card_Icc, Nat.sub_zero, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one]
      nlinarith [mul_le_mul_of_nonneg_right (Nat.floor_le ht0) ht0,
        mul_le_mul_of_nonneg_right ht ht0]

theorem mangoldtSquarePrefix_div_four_integrableOn_Ioi {x : ℝ} (hx : 1 ≤ x) :
    IntegrableOn (fun t : ℝ => (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, (Λ n) ^ 2) / t ^ 4) (Ioi x) := by
  have hm : Measurable (fun t : ℝ => (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, (Λ n) ^ 2)) :=
    (measurable_of_countable (f := fun k : ℕ => ∑ n ∈ Finset.Icc 0 k, (Λ n) ^ 2)).comp
      Nat.measurable_floor
  have hmaj : IntegrableOn (fun t : ℝ => 8 * (t ^ 2)⁻¹) (Ioi x) := by
    have h := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
      (zero_lt_one.trans_le hx)).const_mul 8
    have h2 (t : ℝ) : t ^ (-2 : ℝ) = (t ^ 2)⁻¹ := by simp
    simpa only [IntegrableOn, h2] using h
  refine hmaj.mono' (hm.div (measurable_id.pow_const 4)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht' := hx.trans (le_of_lt ht)
  have htp := zero_lt_one.trans_le ht'
  rw [Real.norm_of_nonneg (div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (by positivity))]
  apply (div_le_iff₀ (show 0 < t ^ 4 by positivity)).2
  calc
    _ ≤ 8 * t ^ 2 := prefix_le_quadratic ht'
    _ = _ := by field_simp [htp.ne'] <;> ring

private def slice (x : ℝ) (n : ℕ) : ℝ → ℝ :=
  (Ioi x ∩ Ici (n : ℝ)).indicator (fun t : ℝ => (Λ n) ^ 2 / t ^ 4)

private theorem slice_set (x : ℝ) (n : ℕ) :
    (Ioi x ∩ Ici (n : ℝ) : Set ℝ) =ᵐ[volume] Ioi (max x n) := by
  rw [← Ioi_inter_Ioi]
  exact (EventuallyEq.refl _ _).inter Ioi_ae_eq_Ici.symm

private theorem slice_int {x : ℝ} (hx : 1 ≤ x) (n : ℕ) : Integrable (slice x n) := by
  apply (integrable_indicator_iff (measurableSet_Ioi.inter measurableSet_Ici)).2
  apply IntegrableOn.congr_set_ae _ (slice_set x n)
  have h := (integrableOn_Ioi_rpow_of_lt (by norm_num : (-4 : ℝ) < -1)
    ((zero_lt_one.trans_le hx).trans_le (le_max_left x (n : ℝ)))).const_mul ((Λ n) ^ 2)
  have h4 (t : ℝ) : t ^ (-4 : ℝ) = (t ^ 4)⁻¹ := by simp
  simpa only [IntegrableOn, div_eq_mul_inv, h4] using h

private theorem slice_eval {x : ℝ} (hx : 1 ≤ x) (n : ℕ) :
    (∫ t, slice x n t) = (Λ n) ^ 2 / (3 * (max x (n : ℝ)) ^ 3) := by
  have hp : 0 < max x (n : ℝ) := (zero_lt_one.trans_le hx).trans_le (le_max_left _ _)
  rw [slice, integral_indicator (measurableSet_Ioi.inter measurableSet_Ici),
    Measure.restrict_congr_set (slice_set x n)]
  have he := integral_Ioi_rpow_of_lt (by norm_num : (-4 : ℝ) < -1) hp
  rw [show (-4:ℝ) + 1 = -3 by norm_num] at he
  have h4 (t : ℝ) : t ^ (-4 : ℝ) = (t ^ 4)⁻¹ := by simp
  have h3 (t : ℝ) : t ^ (-3 : ℝ) = (t ^ 3)⁻¹ := by simp
  simp only [h4, h3] at he
  simp only [div_eq_mul_inv, integral_const_mul]
  rw [he]
  ring

/-- Absolute summability of the maximum-kernel coefficients at a real cutoff. -/
theorem mangoldtSquare_maxKernel_summable {x : ℝ} (hx : 1 ≤ x) :
    Summable (fun n : ℕ => (Λ n) ^ 2 / (3 * (max x (n : ℝ)) ^ 3)) := by
  have h := ((Real.summable_nat_pow_inv (p := 2)).2 (by norm_num)).mul_left 4
  apply Summable.of_nonneg_of_le (fun n => by
    have := (zero_lt_one.trans_le hx).trans_le (le_max_left x (n : ℝ))
    positivity) _ h
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn' : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hm : (n : ℝ) ≤ max x (n : ℝ) := le_max_right _ _
  have hp := hn'.trans_le hm
  calc
    _ ≤ 4 * n / (3 * (n:ℝ) ^ 3) := div_le_div₀ (by positivity) (mangoldt_sq_le_four_mul n)
      (by positivity) (by gcongr)
    _ ≤ _ := by field_simp [hn'.ne']; nlinarith [sq_pos_of_pos hn']

private theorem slice_sum {x : ℝ} (hx : 1 ≤ x) (t : ℝ) :
    (∑' n, slice x n t) =
      (Ioi x).indicator (fun t : ℝ => (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, (Λ n) ^ 2) / t ^ 4) t := by
  by_cases ht : x < t
  · have ht0 : 0 ≤ t := (zero_le_one.trans hx).trans ht.le
    rw [Set.indicator_of_mem (show t ∈ Ioi x from ht), Finset.sum_div]
    rw [tsum_eq_sum (s := Finset.Icc 0 ⌊t⌋₊)]
    · apply Finset.sum_congr rfl
      intro n hn
      have hmem : t ∈ (Ioi x ∩ Ici (n : ℝ)) :=
        ⟨ht, (Nat.le_floor_iff ht0).mp (Finset.mem_Icc.mp hn).2⟩
      exact Set.indicator_of_mem hmem _
    · intro n hn
      apply Set.indicator_of_notMem
      exact fun h => hn (Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor h.2⟩)
  · simp [slice, Set.indicator, ht]

/-- The improper integral as an absolutely summable series of exact kernel slices. -/
theorem prefix_tail_eq_tsum {x : ℝ} (hx : 1 ≤ x) :
    (∫ t in Ioi x, (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, (Λ n) ^ 2) / t ^ 4) =
      ∑' n : ℕ, (Λ n) ^ 2 / (3 * (max x (n : ℝ)) ^ 3) := by
  have hnn (n : ℕ) (t : ℝ) : 0 ≤ slice x n t := by
    apply Set.indicator_nonneg
    intro y _
    positivity
  have hsum := mangoldtSquare_maxKernel_summable hx
  have hnorm : Summable (fun n => ∫ t, ‖slice x n t‖) := by
    simpa only [Real.norm_of_nonneg (hnn _ _), slice_eval hx] using hsum
  have h := integral_tsum_of_summable_integral_norm (slice_int hx) hnorm
  simpa only [slice_eval hx, slice_sum hx, integral_indicator measurableSet_Ioi] using h.symm

/-- The two Abel boundary terms at the moving cutoff cancel, including at integers.
The improper integral is absolutely convergent by the preceding quadratic majorant. -/
theorem primeDiagonal_eq_prefix_integrals {x : ℝ} (hx : 1 ≤ x) :
    primeDiagonal x = -(∫ t in Ioc 1 x, ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, (Λ n) ^ 2) / x ^ 2 +
      3 * x ^ 2 * (∫ t in Ioi x, (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, (Λ n) ^ 2) / t ^ 4) := by
  have hp := zero_lt_one.trans_le hx
  let adj (n : ℕ) : ℝ := if (n : ℝ) ≤ x then ((n : ℝ) - x) * (Λ n) ^ 2 / x ^ 2 else 0
  have hzero (n : ℕ) (hn : n ∉ Finset.Icc 0 ⌊x⌋₊) : adj n = 0 :=
    if_neg fun h => hn (Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor h⟩)
  have hhead : (∑' n, adj n) =
      -(∫ t in Ioc 1 x, ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, (Λ n) ^ 2) / x ^ 2 := by
    rw [tsum_eq_sum hzero]
    have ha := sum_mul_eq_sub_integral_mul₀ (fun n : ℕ => (Λ n) ^ 2) (by simp) x
      (f := id) (fun _ _ => differentiableAt_id) (by simp)
    simp only [id_eq, deriv_id, one_mul] at ha
    calc
      _ = ((∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (n : ℝ) * (Λ n) ^ 2) -
            x * (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (Λ n) ^ 2)) / x ^ 2 := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro n hn
        simp only [adj, if_pos ((Nat.le_floor_iff hp.le).mp (Finset.mem_Icc.mp hn).2)]
        ring
      _ = _ := by rw [ha]; ring
  rw [primeDiagonal_eq_edge_kernel hp, prefix_tail_eq_tsum hx, ← hhead, ← tsum_mul_left,
    ← ((summable_of_ne_finset_zero hzero).tsum_add ((mangoldtSquare_maxKernel_summable hx).mul_left (3 * x ^ 2)))]
  apply tsum_congr
  intro n
  by_cases hn : (n : ℝ) ≤ x
  · simp only [adj, if_pos hn, max_eq_left hn]
    field_simp [hp.ne']
    ring
  · have hn' := hp.trans (lt_of_not_ge hn)
    simp only [adj, if_neg hn, max_eq_right (le_of_lt (lt_of_not_ge hn)), zero_add]
    field_simp [hn'.ne']

end RiemannResearch.Analysis.MontgomeryHorizontalBessel
