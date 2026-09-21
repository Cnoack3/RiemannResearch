import RiemannResearch.RH.ParetoShapeMellinEnergy
import RiemannResearch.RH.MellinModeTailCauchy
import RiemannResearch.RH.CompactMixtureResidueSummation
import RiemannResearch.Analysis.WeightedComplexPairing

/-!
# Coefficient-uniform tail capacity bounds for Pareto shapes below one

Source: user-provided `RH_Pareto_Capacity_Exact_Bounds_and_Critical_Shape_2026-09-21.md`.
The legal functions below are actual finite complex combinations of every
residue generator in the indicated dictionary. The whole infinite tail is
retained. Summability and arithmetic annihilation are proved, not assumed.
The existence of a critical-line zero is not supplied by this module.

-/

noncomputable section
set_option autoImplicit false
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.ShapeCapacity
open RiemannResearch.Analysis.Cesaro
open RiemannResearch.RH.Pareto.SpectralObstruction
open RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity

/-- Actual finite legal combination; array index `k` is physical site `k+1`. -/
def shapeLegalCombination (n : ℕ) (c : Fin n → ℂ) (k : ℕ) : ℂ :=
  ∑ i : Fin n, c i * normalizedResidueCoordinate (i.val + 2) k

theorem shapeLegalCombination_head (n : ℕ) (c : Fin n → ℂ) :
    shapeLegalCombination n c 0 = complexReciprocalSource n c := by
  unfold shapeLegalCombination complexReciprocalSource
  apply Finset.sum_congr rfl
  intro i hi
  simp [normalizedResidueCoordinate, reciprocalSource,
    Nat.mod_eq_of_lt (show 1 < i.val + 2 by omega)]

theorem shapeLegalCombination_norm_le (n : ℕ) (c : Fin n → ℂ) (k : ℕ) :
    ‖shapeLegalCombination n c k‖ ≤ ∑ i : Fin n, ‖c i‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _)
    (normalizedResidueCoordinate_norm_le (i.val + 2) k (by omega))

theorem shapeCellWeight_summable (α a : ℝ) (hα : 0 < α) (ha : 0 < a) :
    Summable (fun k : ℕ => shapeCellWeight α ((k : ℝ) + a)) := by
  have he (k : ℕ) : shapeCellWeight α ((k : ℝ) + a) =
      α * powerCellMass ((α + 1) / 2) a k := by
    rw [powerCellMass_eq _ a (by linarith) ha k]
    rw [show 1 - 2 * ((α + 1) / 2) = -α by ring,
      show 2 * ((α + 1) / 2) - 1 = α by ring]
    unfold shapeCellWeight
    field_simp [hα.ne']
  simp_rw [he]
  exact (powerCellMass_summable ((α + 1) / 2) a (by linarith) ha).mul_left α

/-- The full infinite shape-alpha tail, with all signed mixed terms retained. -/
def shapeLegalTailEnergy (α : ℝ) (n : ℕ) (c : Fin n → ℂ) : ℝ :=
  ∑' k : ℕ, shapeCellWeight α ((k : ℝ) + 2) *
    ‖shapeLegalCombination n c (k + 1)‖ ^ 2

theorem shapeLegalTailEnergy_summable (α : ℝ) (hα : 0 < α)
    (n : ℕ) (c : Fin n → ℂ) :
    Summable (fun k : ℕ => shapeCellWeight α ((k : ℝ) + 2) *
      ‖shapeLegalCombination n c (k + 1)‖ ^ 2) := by
  let C : ℝ := ∑ i : Fin n, ‖c i‖
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (shapeCellWeight_pos α _ hα (by positivity)).le (sq_nonneg _))
    (fun k => ?_)
    ((shapeCellWeight_summable α 2 hα (by norm_num)).mul_right (C ^ 2))
  apply mul_le_mul_of_nonneg_left _
    (shapeCellWeight_pos α _ hα (by positivity)).le
  have hbound := shapeLegalCombination_norm_le n c (k + 1)
  have hnorm := norm_nonneg (shapeLegalCombination n c (k + 1))
  change ‖shapeLegalCombination n c (k + 1)‖ ^ 2 ≤
    (∑ i : Fin n, ‖c i‖) ^ 2
  nlinarith

theorem shapeLegalTailEnergy_nonneg (α : ℝ) (hα : 0 < α)
    (n : ℕ) (c : Fin n → ℂ) : 0 ≤ shapeLegalTailEnergy α n c :=
  tsum_nonneg (fun k => mul_nonneg
    (shapeCellWeight_pos α _ hα (by positivity)).le (sq_nonneg _))

/-- Shape does not alter the exact Mellin annihilation identity. -/
theorem zero_shapeLegal_tail_hasSum
    (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0)
    (n : ℕ) (c : Fin n → ℂ) :
    HasSum (fun k => mellinFirst s (k + 2) * shapeLegalCombination n c (k + 1))
      (-(1 - (2 : ℂ) ^ (-s)) * complexReciprocalSource n c) := by
  have hfull : HasSum
      (fun k => mellinFirst s (k + 1) * shapeLegalCombination n c k) 0 := by
    have hsum : HasSum
        (fun k => ∑ i : Fin n, c i *
          ((paretoWeight k : ℂ) * mellinMode s k *
            normalizedResidueCoordinate (i.val + 2) k))
        (∑ i : Fin n, c i * 0) := by
      apply hasSum_sum
      intro i hi
      have hiSum : HasSum (fun k =>
          (paretoWeight k : ℂ) * mellinMode s k *
            normalizedResidueCoordinate (i.val + 2) k) 0 := by
        simpa only [hz, mul_zero] using
          mellinMode_residue_hasSum s hs hs1 (i.val + 2) (by omega)
      exact hiSum.mul_left (c i)
    have he (k : ℕ) : mellinFirst s (k + 1) * shapeLegalCombination n c k =
        ∑ i : Fin n, c i *
          ((paretoWeight k : ℂ) * mellinMode s k *
            normalizedResidueCoordinate (i.val + 2) k) := by
      rw [shapeLegalCombination, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [weighted_mellinMode_eq]
      ring
    simpa only [he, mul_zero, Finset.sum_const_zero] using hsum
  have ht := (hasSum_nat_add_iff' 1).mpr hfull
  have hhead : mellinFirst s 1 * shapeLegalCombination n c 0 =
      (1 - (2 : ℂ) ^ (-s)) * complexReciprocalSource n c := by
    rw [shapeLegalCombination_head]
    norm_num [mellinFirst]
  simpa only [Finset.sum_range_one, hhead, zero_sub, neg_mul,
    show ∀ k : ℕ, k + 1 + 1 = k + 2 by omega] using ht

theorem mellinFirst_shapeCellEnergy (α : ℝ) (s : ℂ) (k : ℕ) :
    ‖mellinFirst s (k + 2)‖ ^ 2 / shapeCellWeight α ((k : ℝ) + 2) =
      shapeMellinCellEnergy α s ((k : ℝ) + 2) := by
  simp only [mellinFirst, shapeMellinCellEnergy, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one,
    Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_ofNat,
    Complex.ofReal_one]

/-- The actual coefficient-uniform Cauchy inequality, valid for every finite
dictionary and its complete shape-alpha tail. -/
theorem zero_shapeLegal_tail_cauchy
    (α : ℝ) (s : ℂ) (hα : 0 < α) (hs : α < 2 * s.re)
    (hs1 : s ≠ 1) (hz : riemannZeta s = 0) (n : ℕ) (c : Fin n → ℂ) :
    ‖1 - (2 : ℂ) ^ (-s)‖ ^ 2 * ‖complexReciprocalSource n c‖ ^ 2 ≤
      (‖s‖ ^ 2 * (2 : ℝ) ^ (α - 2 * s.re) / (α * (2 * s.re - α))) *
        shapeLegalTailEnergy α n c := by
  have hb : Summable (fun k : ℕ =>
      ‖mellinFirst s (k + 2)‖ ^ 2 / shapeCellWeight α ((k : ℝ) + 2)) := by
    simpa only [mellinFirst_shapeCellEnergy] using
      shapeMellinEnergy_summable α s 2 hα hs (by norm_num)
  have hcs := RiemannResearch.Analysis.WeightedPairing.pairing_norm_sq_le
    (fun k => shapeCellWeight α ((k : ℝ) + 2))
    (fun k => shapeCellWeight_pos α _ hα (by positivity))
    (fun k => mellinFirst s (k + 2))
    (fun k => shapeLegalCombination n c (k + 1)) hb
    (shapeLegalTailEnergy_summable α hα n c)
  rw [(zero_shapeLegal_tail_hasSum s (by linarith) hs1 hz n c).tsum_eq,
    norm_mul, norm_neg, mul_pow] at hcs
  simp_rw [mellinFirst_shapeCellEnergy] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_right
    (shapeMellinEnergy_le α s 2 hα hs (by norm_num))
    (shapeLegalTailEnergy_nonneg α hα n c))

private theorem shape_mellin_head_ne_zero (s : ℂ) (hs : 0 < s.re) :
    1 - (2 : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have he : (2 : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have hn : ‖(2 : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (-s.re) := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos
      (show (0 : ℝ) < 2 by norm_num) (-s)
  have hl : (2 : ℝ) ^ (-s.re) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  rw [he, norm_one] at hn
  linarith

/-- Explicit capacity bound for each actual finite coefficient vector. -/
theorem zero_shapeLegal_capacity_bound
    (α : ℝ) (s : ℂ) (hα : 0 < α) (hs : α < 2 * s.re)
    (hs1 : s ≠ 1) (hz : riemannZeta s = 0) (n : ℕ) (c : Fin n → ℂ) :
    ‖complexReciprocalSource n c‖ ^ 2 ≤
      (‖s‖ ^ 2 * (2 : ℝ) ^ (α - 2 * s.re) /
        (α * (2 * s.re - α) * ‖1 - (2 : ℂ) ^ (-s)‖ ^ 2)) *
        shapeLegalTailEnergy α n c := by
  have hA : 0 < ‖1 - (2 : ℂ) ^ (-s)‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (shape_mellin_head_ne_zero s (by linarith))) 2
  have h := zero_shapeLegal_tail_cauchy α s hα hs hs1 hz n c
  calc
    _ ≤ ((‖s‖ ^ 2 * (2 : ℝ) ^ (α - 2 * s.re) /
        (α * (2 * s.re - α))) * shapeLegalTailEnergy α n c) /
        ‖1 - (2 : ℂ) ^ (-s)‖ ^ 2 :=
      (le_div_iff₀ hA).2 (by simpa only [mul_comm] using h)
    _ = _ := by
      field_simp [hA.ne', hα.ne', (sub_pos.mpr hs).ne']

/-- Every known critical-line zero gives this uniform bound for all shapes
strictly below one. The zero-existence theorem remains an explicit input. -/
theorem critical_shapeLegal_capacity_bound
    (α t : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hz : riemannZeta (MellinFrequency.criticalPoint t) = 0)
    (n : ℕ) (c : Fin n → ℂ) :
    ‖complexReciprocalSource n c‖ ^ 2 ≤
      (‖MellinFrequency.criticalPoint t‖ ^ 2 * (2 : ℝ) ^ (α - 1) /
        (α * (1 - α) *
          ‖1 - (2 : ℂ) ^ (-MellinFrequency.criticalPoint t)‖ ^ 2)) *
        shapeLegalTailEnergy α n c := by
  have hs : α < 2 * (MellinFrequency.criticalPoint t).re := by
    rw [MellinFrequency.criticalPoint_re]
    linarith
  have hs1 : MellinFrequency.criticalPoint t ≠ 1 := by
    intro he
    have hr := congrArg Complex.re he
    rw [MellinFrequency.criticalPoint_re] at hr
    norm_num at hr
  simpa only [MellinFrequency.criticalPoint_re,
    show 2 * (1 / 2 : ℝ) = 1 by norm_num] using
    zero_shapeLegal_capacity_bound α (MellinFrequency.criticalPoint t)
      hα hs hs1 hz n c

/-- Full-tail capacity of the finite dictionary, as an actual supremum over
all complex coefficient choices. The zero vector has quotient zero. -/
def shapeFiniteCapacity (α : ℝ) (n : ℕ) : ℝ :=
  sSup (Set.range (fun c : Fin n → ℂ =>
    ‖complexReciprocalSource n c‖ ^ 2 / shapeLegalTailEnergy α n c))

theorem zero_shapeFiniteCapacity_le
    (α : ℝ) (s : ℂ) (hα : 0 < α) (hs : α < 2 * s.re)
    (hs1 : s ≠ 1) (hz : riemannZeta s = 0) (n : ℕ) :
    shapeFiniteCapacity α n ≤
      ‖s‖ ^ 2 * (2 : ℝ) ^ (α - 2 * s.re) /
        (α * (2 * s.re - α) * ‖1 - (2 : ℂ) ^ (-s)‖ ^ 2) := by
  unfold shapeFiniteCapacity
  apply csSup_le (Set.range_nonempty _)
  rintro r ⟨c, rfl⟩
  change ‖complexReciprocalSource n c‖ ^ 2 / shapeLegalTailEnergy α n c ≤ _
  by_cases he : shapeLegalTailEnergy α n c = 0
  · rw [he, div_zero]
    apply div_nonneg
    · exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by norm_num) _)
    · exact mul_nonneg (mul_nonneg hα.le (sub_pos.mpr hs).le) (sq_nonneg _)
  · have hE : 0 < shapeLegalTailEnergy α n c :=
      lt_of_le_of_ne (shapeLegalTailEnergy_nonneg α hα n c) (Ne.symm he)
    exact (div_le_iff₀ hE).2
      (zero_shapeLegal_capacity_bound α s hα hs hs1 hz n c)

/-- An actual critical-line zero bounds all finite-dictionary capacities by
one explicit finite real number for each shape below one. -/
theorem critical_shapeFiniteCapacities_bddAbove
    (α t : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hz : riemannZeta (MellinFrequency.criticalPoint t) = 0) :
    BddAbove (Set.range (shapeFiniteCapacity α)) := by
  have hs : α < 2 * (MellinFrequency.criticalPoint t).re := by
    rw [MellinFrequency.criticalPoint_re]
    linarith
  have hs1 : MellinFrequency.criticalPoint t ≠ 1 := by
    intro he
    have hr := congrArg Complex.re he
    rw [MellinFrequency.criticalPoint_re] at hr
    norm_num at hr
  refine ⟨‖MellinFrequency.criticalPoint t‖ ^ 2 *
    (2 : ℝ) ^ (α - 2 * (MellinFrequency.criticalPoint t).re) /
      (α * (2 * (MellinFrequency.criticalPoint t).re - α) *
        ‖1 - (2 : ℂ) ^ (-MellinFrequency.criticalPoint t)‖ ^ 2), ?_⟩
  rintro r ⟨n, rfl⟩
  exact zero_shapeFiniteCapacity_le α (MellinFrequency.criticalPoint t)
    hα hs hs1 hz n

end RiemannResearch.RH.Pareto.ShapeCapacity
