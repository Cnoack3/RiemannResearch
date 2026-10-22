/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.FiniteDyadicCellKernel
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.Topology.UniformSpace.HeineCantor
/-!
# Constructive mean-zero dyadic L2 density

The literal Ioc cells of the existing dyadic model carry their actual integral
averages. Their finite Haar reconstruction preserves the original unnormalized
Haar matrix. Cellwise least squares and continuous compact-support density prove
convergence in squared-integral distance; the zero-radius case is handled before
any cancellation of a cell width.

Source: user-provided RH_Proof_First_Continuation_2026-09-04.md, Section 5,
supports the dyadic-average construction and the density statement. The
continuous-density proof strategy uses Mathlib's
`MemLp.exists_hasCompactSupport_integral_rpow_sub_le`.

This is an unconditional analytic density result. Arithmetic positivity,
agreement with the completed Weil distribution, and RH remain separate
obligations.
-/

open scoped BigOperators
open MeasureTheory Set Filter
open RiemannResearch.Analysis
namespace RiemannResearch.RH.PrimeGapCurvature
noncomputable section

/-- Every cell has positive width when the support radius is positive. -/
theorem dyadicCellWidth_pos {R : ℝ} (hR : 0 < R) (m : ℕ) :
    0 < dyadicCellWidth R m := by
  unfold dyadicCellWidth
  positivity

private theorem exists_grid_cell (a w : ℝ) (n : ℕ) {x : ℝ}
    (hx : x ∈ Ioc a (a + w * n)) :
    ∃ j : Fin n, x ∈ Ioc (a + w * j.val) (a + w * j.val + w) := by
  induction n with
  | zero => simp at hx
  | succ n ih =>
    by_cases hx' : x ≤ a + w * n
    · obtain ⟨j, hj⟩ := ih ⟨hx.1, hx'⟩
      exact ⟨j.castSucc, hj⟩
    · refine ⟨Fin.last n, ?_⟩
      have hxn := hx.2
      push_cast at hxn
      exact ⟨lt_of_not_ge hx', by simpa [mul_add, add_assoc] using hxn⟩

theorem exists_mem_dyadicCell (R : ℝ) (m : ℕ) {x : ℝ}
    (hx : x ∈ Ioc (-R) R) :
    ∃ j : Fin (2 ^ m),
      x ∈ Ioc (dyadicCellLeft R m j) (dyadicCellRight R m j) := by
  apply exists_grid_cell (-R) (dyadicCellWidth R m)
  constructor
  · exact hx.1
  · have hh := dyadicCellWidth_mul_count R m
    have hc : ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ m := by norm_cast
    rw [hc, hh]
    linarith [hx.2]

theorem dyadicCell_disjoint {R : ℝ} (hR : 0 ≤ R) (m : ℕ)
    {i j : Fin (2 ^ m)} (hij : i ≠ j) :
    Disjoint (Ioc (dyadicCellLeft R m i) (dyadicCellRight R m i))
      (Ioc (dyadicCellLeft R m j) (dyadicCellRight R m j)) := by
  have aux : ∀ i j : Fin (2 ^ m), i < j →
      dyadicCellRight R m i ≤ dyadicCellLeft R m j := by
    intro i j hij
    have hn : (i.val : ℝ) + 1 ≤ j.val := by
      exact_mod_cast (Nat.succ_le_of_lt hij)
    have h := mul_le_mul_of_nonneg_left hn (dyadicCellWidth_nonneg hR m)
    dsimp [dyadicCellLeft, dyadicCellRight]
    nlinarith
  rcases lt_or_gt_of_ne hij with hij | hij
  · exact Ioc_disjoint_Ioc_of_le (aux i j hij)
  · exact (Ioc_disjoint_Ioc_of_le (aux j i hij)).symm

/-- Recover literal Haar coefficients from any zero-sum cell vector. -/
theorem finiteDyadicHaarMatrix_surjective_meanZero (m : ℕ)
    (s : Fin (2 ^ m) → ℝ) (hs : ∑ j, s j = 0) :
    ∃ c : FiniteDyadicHaarIndex m → ℝ, (finiteDyadicHaarMatrix m).mulVec c = s := by
  classical
  let v : meanZeroSlopeSubmodule (2 ^ m - 1) :=
    ⟨fun j => s (Fin.cast (dyadicDimension_eq m) j), by
      change (∑ j : Fin (2 ^ m - 1 + 1), s (Fin.cast (dyadicDimension_eq m) j)) = 0
      exact ((Fin.castOrderIso (dyadicDimension_eq m)).toEquiv.sum_comp s).trans hs⟩
  refine ⟨fun i => ((finiteDyadicHaarBasis m).repr v) i, ?_⟩
  funext j
  let j' : Fin (2 ^ m - 1 + 1) := Fin.cast (dyadicDimension_eq m).symm j
  have h := congrArg (fun z : meanZeroSlopeSubmodule (2 ^ m - 1) => z.val j')
    ((finiteDyadicHaarBasis m).sum_repr v)
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul, finiteDyadicHaarBasis_apply] at h
  change (∑ i, ((finiteDyadicHaarBasis m).repr v) i *
    finiteDyadicHaarAtom m i.1.val i.2 j) = s j at h
  simpa only [Matrix.mulVec, dotProduct, finiteDyadicHaarMatrix, mul_comm] using h

/-- The actual integral average on one literal Ioc cell. -/
def dyadicCellAverage (R : ℝ) (m : ℕ) (u : ℝ → ℝ) (j : Fin (2 ^ m)) : ℝ :=
  (dyadicCellWidth R m)⁻¹ *
    ∫ x in Ioc (dyadicCellLeft R m j) (dyadicCellRight R m j), u x

/-- The finite step whose values are the actual dyadic cell averages. -/
def dyadicAverageStep (R : ℝ) (m : ℕ) (u : ℝ → ℝ) : ℝ → ℝ :=
  finiteCellStep (dyadicCellLeft R m) (dyadicCellRight R m) (dyadicCellAverage R m u)

/-- Adjacent Ioc-cell integrals telescope to the support-window integral. -/
theorem sum_integral_dyadicCell {R : ℝ} (hR : 0 ≤ R) (m : ℕ)
    {u : ℝ → ℝ} (hu : Integrable u) :
    (∑ j : Fin (2 ^ m),
      ∫ x in Ioc (dyadicCellLeft R m j) (dyadicCellRight R m j), u x) =
      ∫ x in Ioc (-R) R, u x := by
  simp_rw [← intervalIntegral.integral_of_le (dyadicCell_ordered hR m _)]
  let a : ℕ → ℝ := fun n => -R + dyadicCellWidth R m * n
  have hr (j : Fin (2 ^ m)) : dyadicCellRight R m j = a (j.val + 1) := by
    dsimp [dyadicCellRight, dyadicCellLeft, a]
    push_cast
    ring
  simp_rw [hr]
  change (∑ j : Fin (2 ^ m), ∫ x in a j.val..a (j.val + 1), u x) = _
  rw [Fin.sum_univ_eq_sum_range (fun n => ∫ x in a n..a (n + 1), u x)]
  rw [intervalIntegral.sum_integral_adjacent_intervals (fun k hk => hu.intervalIntegrable)]
  have ha0 : a 0 = -R := by simp [a]
  have han : a (2 ^ m) = R := by
    simp [a, Nat.cast_pow, dyadicCellWidth_mul_count]
    ring
  rw [ha0, han, intervalIntegral.integral_of_le (by linarith)]

/-- The left endpoint is null, so Ioc integration retains a closed-window-supported test. -/
theorem integral_dyadicWindow_eq {R : ℝ} {u : ℝ → ℝ}
    (hu : ∀ x, x ∉ Icc (-R) R → u x = 0) :
    (∫ x in Ioc (-R) R, u x) = ∫ x, u x := by
  rw [← integral_Icc_eq_integral_Ioc, ← integral_indicator measurableSet_Icc]
  congr 1
  funext x
  by_cases hx : x ∈ Icc (-R) R
  · simp [hx]
  · simp [hx, hu x hx]

/-- Actual cell averages have exact zero sum for mean-zero supported tests. -/
theorem dyadicCellAverage_sum_zero {R : ℝ} (hR : 0 ≤ R) (m : ℕ)
    {u : ℝ → ℝ} (hu : Integrable u)
    (hsupp : ∀ x, x ∉ Icc (-R) R → u x = 0) (hmean : (∫ x, u x) = 0) :
    ∑ j, dyadicCellAverage R m u j = 0 := by
  unfold dyadicCellAverage
  rw [← Finset.mul_sum, sum_integral_dyadicCell hR m hu,
    integral_dyadicWindow_eq hsupp, hmean, mul_zero]

/-- Reconstruct the actual averaging step in the existing Haar coordinates. -/
theorem dyadicAverageStep_exists_Haar {R : ℝ} (hR : 0 ≤ R) (m : ℕ)
    {u : ℝ → ℝ} (hu : Integrable u)
    (hsupp : ∀ x, x ∉ Icc (-R) R → u x = 0) (hmean : (∫ x, u x) = 0) :
    ∃ c : FiniteDyadicHaarIndex m → ℝ, dyadicHaarStep R m c = dyadicAverageStep R m u := by
  obtain ⟨c, hc⟩ := finiteDyadicHaarMatrix_surjective_meanZero m
    (dyadicCellAverage R m u) (dyadicCellAverage_sum_zero hR m hu hsupp hmean)
  exact ⟨c, by simp [dyadicHaarStep, dyadicAverageStep, hc]⟩

theorem dyadicAverageStep_eq_on_cell {R : ℝ} (hR : 0 ≤ R) (m : ℕ)
    (u : ℝ → ℝ) (j : Fin (2 ^ m)) {x : ℝ}
    (hx : x ∈ Ioc (dyadicCellLeft R m j) (dyadicCellRight R m j)) :
    dyadicAverageStep R m u x = dyadicCellAverage R m u j := by
  classical
  unfold dyadicAverageStep finiteCellStep
  rw [Finset.sum_eq_single j]
  · simp [hx]
  · intro i hi hij
    apply indicator_of_notMem
    intro hxi
    exact Set.disjoint_left.mp (dyadicCell_disjoint hR m hij) hxi hx
  · simp

theorem dyadicAverageStep_eq_zero_of_not_mem {R : ℝ} (hR : 0 ≤ R)
    (m : ℕ) (u : ℝ → ℝ) {x : ℝ} (hx : x ∉ Icc (-R) R) :
    dyadicAverageStep R m u x = 0 := by
  classical
  unfold dyadicAverageStep finiteCellStep
  apply Finset.sum_eq_zero
  intro j hj
  apply indicator_of_notMem
  intro hcell
  have hb := dyadicCell_endpoints_bounds hR m j
  exact hx ⟨hb.1.trans hcell.1.le, hcell.2.trans hb.2⟩

theorem memLp_dyadicAverageStep (R : ℝ) (m : ℕ) (u : ℝ → ℝ) :
    MemLp (dyadicAverageStep R m u) 2 := by
  apply (memLp_two_iff_integrable_sq
    (measurable_finiteCellStep _ _ _).aestronglyMeasurable).2
  exact integrable_finiteCellStep_sq _ _ _

theorem dyadicCell_volume_real {R : ℝ} (hR : 0 ≤ R) (m : ℕ)
    (j : Fin (2 ^ m)) :
    volume.real (Ioc (dyadicCellLeft R m j) (dyadicCellRight R m j)) =
      dyadicCellWidth R m := by
  rw [Real.volume_real_Ioc, dyadicCellRight, add_sub_cancel_left,
    max_eq_left (dyadicCellWidth_nonneg hR m)]

theorem integral_sq_sub_const_dyadicCell {R : ℝ} (hR : 0 ≤ R) (m : ℕ)
    {u : ℝ → ℝ} (hu : Integrable u) (hu2 : Integrable (fun x => u x ^ 2))
    (j : Fin (2 ^ m)) (b : ℝ) :
    (∫ x in Ioc (dyadicCellLeft R m j) (dyadicCellRight R m j), (u x - b) ^ 2) =
      (∫ x in Ioc (dyadicCellLeft R m j) (dyadicCellRight R m j), u x ^ 2) -
      2 * b * (∫ x in Ioc (dyadicCellLeft R m j) (dyadicCellRight R m j), u x) +
      dyadicCellWidth R m * b ^ 2 := by
  have hi1 := hu2.restrict (s := Ioc (dyadicCellLeft R m j) (dyadicCellRight R m j))
  have hi2 := (hu.restrict (s := Ioc (dyadicCellLeft R m j)
    (dyadicCellRight R m j))).const_mul (2 * b)
  have hi3 : Integrable (fun _ : ℝ => b ^ 2)
      (volume.restrict (Ioc (dyadicCellLeft R m j) (dyadicCellRight R m j))) :=
    integrable_const _
  simp_rw [show ∀ x, (u x - b) ^ 2 = u x ^ 2 - (2 * b) * u x + b ^ 2 by
    intro x; ring]
  rw [integral_add (f := fun x => u x ^ 2 - (2 * b) * u x)
      (g := fun _ => b ^ 2) (hi1.sub hi2) hi3,
    integral_sub (f := fun x => u x ^ 2) (g := fun x => (2 * b) * u x) hi1 hi2,
    integral_const_mul, integral_const, measureReal_restrict_apply_univ,
    dyadicCell_volume_real hR m j, smul_eq_mul]

/-- A cell average minimizes squared error among all constant cell values. -/
theorem dyadicCellAverage_minimizes_sq {R : ℝ} (hR : 0 < R) (m : ℕ)
    {u : ℝ → ℝ} (hu : Integrable u) (hu2 : Integrable (fun x => u x ^ 2))
    (j : Fin (2 ^ m)) (b : ℝ) :
    (∫ x in Ioc (dyadicCellLeft R m j) (dyadicCellRight R m j),
      (dyadicCellAverage R m u j - u x) ^ 2) ≤
    ∫ x in Ioc (dyadicCellLeft R m j) (dyadicCellRight R m j), (b - u x) ^ 2 := by
  rw [show (fun x => (dyadicCellAverage R m u j - u x) ^ 2) =
      (fun x => (u x - dyadicCellAverage R m u j) ^ 2) by funext x; ring,
    show (fun x => (b - u x) ^ 2) = (fun x => (u x - b) ^ 2) by funext x; ring]
  rw [integral_sq_sub_const_dyadicCell hR.le m hu hu2,
    integral_sq_sub_const_dyadicCell hR.le m hu hu2]
  have ha : dyadicCellWidth R m * dyadicCellAverage R m u j =
      ∫ x in Ioc (dyadicCellLeft R m j) (dyadicCellRight R m j), u x := by
    unfold dyadicCellAverage
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt (dyadicCellWidth_pos hR m)), one_mul]
  have hn := mul_nonneg (dyadicCellWidth_pos hR m).le
    (sq_nonneg (b - dyadicCellAverage R m u j))
  rw [← ha]
  nlinarith only [hn]

/-- The averaging step is at least as accurate as every step on the same grid. -/
theorem dyadicAverageStep_sq_error_le {R : ℝ} (hR : 0 < R) (m : ℕ)
    {u : ℝ → ℝ} (hu : Integrable u) (hu2 : Integrable (fun x => u x ^ 2))
    (hsupp : ∀ x, x ∉ Icc (-R) R → u x = 0) (b : Fin (2 ^ m) → ℝ) :
    (∫ x, (dyadicAverageStep R m u x - u x) ^ 2) ≤
      ∑ j : Fin (2 ^ m),
        ∫ x in Ioc (dyadicCellLeft R m j) (dyadicCellRight R m j), (b j - u x) ^ 2 := by
  have huLp : MemLp u 2 := (memLp_two_iff_integrable_sq hu.aestronglyMeasurable).2 hu2
  have herr : Integrable (fun x => (dyadicAverageStep R m u x - u x) ^ 2) :=
    ((memLp_dyadicAverageStep R m u).sub huLp).integrable_sq
  have he := sum_integral_dyadicCell hR.le m herr
  rw [integral_dyadicWindow_eq (by
    intro x hx
    simp [dyadicAverageStep_eq_zero_of_not_mem hR.le m u hx, hsupp x hx])] at he
  rw [← he]
  apply Finset.sum_le_sum
  intro j hj
  rw [setIntegral_congr_fun measurableSet_Ioc (fun x hx => by
    rw [dyadicAverageStep_eq_on_cell hR.le m u j hx])]
  exact dyadicCellAverage_minimizes_sq hR m hu hu2 j (b j)



/-- Compare averaging error with a global L2 error and the test's cell oscillation. -/
theorem dyadicAverageStep_sq_error_le_of_oscillation {R : ℝ} (hR : 0 < R) (m : ℕ)
    {u : ℝ → ℝ} (hu : Integrable u) (hu2 : Integrable (fun x => u x ^ 2))
    (hsupp : ∀ x, x ∉ Icc (-R) R → u x = 0)
    {g : ℝ → ℝ} (hg : MemLp g 2) {η δ : ℝ}
    (hosc : ∀ {x y : ℝ}, dist x y < δ → dist (g x) (g y) ≤ η)
    (hm : dyadicCellWidth R m < δ) :
    (∫ x, (dyadicAverageStep R m u x - u x) ^ 2) ≤
      2 * (∫ x, (u x - g x) ^ 2) + 4 * R * η ^ 2 := by
  have huLp : MemLp u 2 := (memLp_two_iff_integrable_sq hu.aestronglyMeasurable).2 hu2
  have herr : Integrable (fun x => (u x - g x) ^ 2) := (huLp.sub hg).integrable_sq
  have hj (j : Fin (2 ^ m)) :
      (∫ x in Ioc (dyadicCellLeft R m j) (dyadicCellRight R m j),
        (g (dyadicCellLeft R m j) - u x) ^ 2) ≤
      2 * (∫ x in Ioc (dyadicCellLeft R m j) (dyadicCellRight R m j), (u x - g x) ^ 2) +
        dyadicCellWidth R m * (2 * η ^ 2) := by
    let S := Ioc (dyadicCellLeft R m j) (dyadicCellRight R m j)
    have hi1 : Integrable (fun x => (g (dyadicCellLeft R m j) - u x) ^ 2)
        (volume.restrict S) :=
      ((memLp_const (g (dyadicCellLeft R m j))).sub (huLp.restrict S)).integrable_sq
    have hi2 : Integrable (fun x => 2 * (u x - g x) ^ 2) (volume.restrict S) :=
      (herr.restrict).const_mul 2
    have hi3 : Integrable (fun _ : ℝ => 2 * η ^ 2) (volume.restrict S) := integrable_const _
    have hb :
        (∫ x in S, (g (dyadicCellLeft R m j) - u x) ^ 2) ≤
          ∫ x in S, (2 * (u x - g x) ^ 2 + 2 * η ^ 2) := by
      apply integral_mono_ae hi1 (hi2.add hi3)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hd : dist x (dyadicCellLeft R m j) < δ := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.1.le)]
        have hright := hx.2
        dsimp [dyadicCellRight] at hright
        linarith
      have ho := hosc hd
      rw [Real.dist_eq] at ho
      have hs : (g x - g (dyadicCellLeft R m j)) ^ 2 ≤ η ^ 2 := by
        have hh := mul_self_le_mul_self (abs_nonneg (g x - g (dyadicCellLeft R m j))) ho
        simpa only [← sq, sq_abs] using hh
      change (g (dyadicCellLeft R m j) - u x) ^ 2 ≤ 2 * (u x - g x) ^ 2 + 2 * η ^ 2
      nlinarith only [hs, sq_nonneg ((u x - g x) - (g x - g (dyadicCellLeft R m j)))]
    rw [integral_add hi2 hi3, integral_const_mul, integral_const,
      measureReal_restrict_apply_univ] at hb
    simpa only [S, dyadicCell_volume_real hR.le m j, smul_eq_mul] using hb
  calc
    _ ≤ ∑ j : Fin (2 ^ m),
        ∫ x in Ioc (dyadicCellLeft R m j) (dyadicCellRight R m j),
          (g (dyadicCellLeft R m j) - u x) ^ 2 :=
      dyadicAverageStep_sq_error_le hR m hu hu2 hsupp (fun j => g (dyadicCellLeft R m j))
    _ ≤ ∑ j : Fin (2 ^ m),
        (2 * (∫ x in Ioc (dyadicCellLeft R m j) (dyadicCellRight R m j),
          (u x - g x) ^ 2) + dyadicCellWidth R m * (2 * η ^ 2)) :=
      Finset.sum_le_sum (fun j _ => hj j)
    _ = 2 * (∫ x in Ioc (-R) R, (u x - g x) ^ 2) + 4 * R * η ^ 2 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, sum_integral_dyadicCell hR.le m herr]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_pow, Nat.cast_ofNat]
      have hw := dyadicCellWidth_mul_count R m
      nlinarith only [hw]
    _ ≤ _ := by
      have hb := setIntegral_le_integral (s := Ioc (-R) R) herr
        (Eventually.of_forall (fun x => sq_nonneg (u x - g x)))
      linarith

theorem tendsto_dyadicCellWidth (R : ℝ) :
    Tendsto (dyadicCellWidth R) atTop (nhds 0) := by
  exact tendsto_const_nhds.div_atTop
    (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num))


/-- The genuine Ioc-cell averages converge in squared-integral distance. -/
theorem tendsto_dyadicAverageStep_sq_error {R : ℝ} (hR : 0 ≤ R)
    {u : ℝ → ℝ} (hu : Integrable u) (hu2 : Integrable (fun x => u x ^ 2))
    (hsupp : ∀ x, x ∉ Icc (-R) R → u x = 0) :
    Tendsto (fun m => ∫ x, (dyadicAverageStep R m u x - u x) ^ 2) atTop (nhds 0) := by
  rcases eq_or_lt_of_le hR with hR0 | hRpos
  · have hR' : R = 0 := hR0.symm
    subst R
    have he : (∫ x, u x ^ 2) = 0 := by
      have hh := integral_dyadicWindow_eq (R := 0)
        (u := fun x => u x ^ 2) (by intro x hx; simp [hsupp x hx])
      simpa using hh.symm
    have hz (m : ℕ) : dyadicAverageStep 0 m u = 0 := by
      funext x
      simp [dyadicAverageStep, finiteCellStep, dyadicCellLeft, dyadicCellRight,
        dyadicCellWidth]
    simpa only [hz, Pi.zero_apply, zero_sub, neg_sq, he] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  · rw [Metric.tendsto_atTop]
    intro ε hε
    have huLp : MemLp u 2 := (memLp_two_iff_integrable_sq hu.aestronglyMeasurable).2 hu2
    obtain ⟨g, hgc, he, hgc', hgLp⟩ :=
      MemLp.exists_hasCompactSupport_integral_rpow_sub_le
        (p := (2 : ℝ)) (by norm_num) (by simpa using huLp) (show 0 < ε / 4 by positivity)
    have he' : (∫ x, (u x - g x) ^ 2) ≤ ε / 4 := by
      simpa [Real.rpow_two, Real.norm_eq_abs] using he
    have hgLp' : MemLp g 2 := by simpa using hgLp
    let η : ℝ := min 1 (ε / (8 * R + 1))
    have hden : 0 < 8 * R + 1 := by linarith
    have hη : 0 < η := lt_min zero_lt_one (div_pos hε hden)
    have hη1 : η ≤ 1 := min_le_left _ _
    have hηε : η * (8 * R + 1) ≤ ε :=
      (le_div_iff₀ hden).mp (min_le_right _ _)
    have hηsq : η ^ 2 ≤ η := by nlinarith
    obtain ⟨δ, hδ, hosc⟩ := Metric.uniformContinuous_iff.mp
      (hgc.uniformContinuous_of_continuous hgc') η hη
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (tendsto_dyadicCellWidth R) δ hδ
    refine ⟨N, ?_⟩
    intro m hm
    have hwidth : dyadicCellWidth R m < δ := by
      have hh := hN m hm
      simpa [Real.dist_eq, abs_of_nonneg (dyadicCellWidth_nonneg hRpos.le m)] using hh
    have hb := dyadicAverageStep_sq_error_le_of_oscillation hRpos m hu hu2 hsupp
      hgLp' (fun hxy => (hosc hxy).le) hwidth
    have hn : 0 ≤ ∫ x, (dyadicAverageStep R m u x - u x) ^ 2 :=
      integral_nonneg (fun x => sq_nonneg _)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hn]
    have hterm : 4 * R * η ^ 2 ≤ 4 * R * η :=
      mul_le_mul_of_nonneg_left hηsq (by positivity)
    nlinarith

/-- Constructive mean-zero dyadic Haar density on every fixed support window.
The coefficients reconstruct the actual Ioc-cell averages at every level. -/
theorem exists_dyadicHaarStep_tendsto_sq_error {R : ℝ} (hR : 0 ≤ R)
    {u : ℝ → ℝ} (hu : Integrable u) (hu2 : Integrable (fun x => u x ^ 2))
    (hsupp : ∀ x, x ∉ Icc (-R) R → u x = 0) (hmean : (∫ x, u x) = 0) :
    ∃ c : (m : ℕ) → FiniteDyadicHaarIndex m → ℝ,
      (∀ m, dyadicHaarStep R m (c m) = dyadicAverageStep R m u) ∧
      Tendsto (fun m => ∫ x, (dyadicHaarStep R m (c m) x - u x) ^ 2) atTop (nhds 0) := by
  rcases eq_or_lt_of_le hR with hR0 | hRpos
  · have hR' : R = 0 := hR0.symm
    subst R
    have hc (m : ℕ) : dyadicHaarStep 0 m (fun _ => 0) = dyadicAverageStep 0 m u := by
      funext x
      simp [dyadicHaarStep, dyadicAverageStep, finiteCellStep,
        dyadicCellLeft, dyadicCellRight, dyadicCellWidth]
    refine ⟨fun _ _ => 0, hc, ?_⟩
    simpa only [hc] using tendsto_dyadicAverageStep_sq_error (le_refl 0) hu hu2 hsupp
  · choose c hc using fun m => dyadicAverageStep_exists_Haar hRpos.le m hu hsupp hmean
    refine ⟨c, hc, ?_⟩
    simpa only [hc] using tendsto_dyadicAverageStep_sq_error hRpos.le hu hu2 hsupp

end
end RiemannResearch.RH.PrimeGapCurvature
