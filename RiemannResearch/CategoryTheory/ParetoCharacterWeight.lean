import RiemannResearch.CategoryTheory.ParetoCharacterScreenedEnergy
import Mathlib.Algebra.Ring.GeomSum

/-! # Uniform Dirichlet-power approximation to the Pareto mixed minimum

Expanding the physical weight about the middle of the interval for 1/n gives a
finite polynomial in 1/n. The relative quadratic-form error is uniform over
all vectors, so it persists under minimization over the mixed closure.
-/

noncomputable section
open scoped BigOperators Topology
open Filter
namespace RiemannResearch.CategoryTheory.ParetoCharacterWeight
open RiemannResearch.RH.Pareto RiemannResearch.RH.Pareto.PrimePowerSchur
open CoefficientStabilization

def ratio (n : ℕ) : ℝ := (1 - 2 / (n : ℝ)) / 3

def dirichletWeight (k n : ℕ) : ℝ :=
  2 / (3 * (n : ℝ)^2) * ∑ j ∈ Finset.range (2*k), ratio n ^ j

theorem weight_identity (k n : ℕ) :
    dirichletWeight k n = (1 - (ratio n ^ 2)^k) * positiveWeight n := by
  have h : (1-ratio n)*positiveWeight n = 2 / (3*(n : ℝ)^2) := by
    cases n with
    | zero => norm_num [ratio, positiveWeight]
    | succ n =>
      have hp : (0 : ℝ) < n.succ := by positivity
      unfold ratio positiveWeight
      field_simp
      <;> ring
  rw [dirichletWeight, ← h, ← pow_mul]
  linear_combination -positiveWeight n * geom_sum_mul (ratio n) (2*k)

theorem ratio_sq_bound (n : ℕ) : (ratio n)^2 ≤ (1/9 : ℝ) := by
  have ha : |ratio n| ≤ (1/3 : ℝ) := by
    cases n with
    | zero => norm_num [ratio]
    | succ n =>
      have hp : 0 < (n.succ : ℝ) := by positivity
      have h1 : (1 : ℝ) ≤ n.succ := by exact_mod_cast Nat.le_add_left 1 n
      have hd := (div_le_iff₀ hp).mpr (show (2 : ℝ) ≤ 2 * n.succ by linarith)
      have hp' : 0 ≤ 2 / (n.succ : ℝ) := by positivity
      rw [ratio, abs_le]
      constructor <;> linarith
  calc
    _ = |ratio n|^2 := (sq_abs _).symm
    _ ≤ ((1:ℝ)/3)^2 := pow_le_pow_left₀ (abs_nonneg _) ha _
    _ = _ := by norm_num

theorem weight_bounds (k n : ℕ) :
    (1-(1/9 : ℝ)^k)*positiveWeight n ≤ dirichletWeight k n ∧
      dirichletWeight k n ≤ positiveWeight n := by
  rw [weight_identity]
  constructor
  · exact mul_le_mul_of_nonneg_right
      (sub_le_sub_left (pow_le_pow_left₀ (sq_nonneg _) (ratio_sq_bound n) k) 1)
      (positiveWeight_nonneg n)
  · have hv : 0 ≤ (ratio n ^ 2)^k := pow_nonneg (sq_nonneg _) _
    nlinarith [mul_nonneg hv (positiveWeight_nonneg n)]

private theorem scale_nonneg (k : ℕ) : 0 ≤ 1-(1/9 : ℝ)^k := by
  exact sub_nonneg.mpr (pow_le_one₀ (by norm_num) (by norm_num))

private theorem weight_nonneg (k n : ℕ) : 0 ≤ dirichletWeight k n :=
  (mul_nonneg (scale_nonneg _) (positiveWeight_nonneg _)).trans (weight_bounds k n).1

def energy (k : ℕ) (x : ThresholdHilbert) : ℝ :=
  ∑' n : ℕ, dirichletWeight k n * (hilbertSequence x n)^2

theorem energy_bounds (k : ℕ) (x : ThresholdHilbert) :
    (1-(1/9 : ℝ)^k)*‖x‖^2 ≤ energy k x ∧ energy k x ≤ ‖x‖^2 := by
  have hs := hilbertSequence_square_summable x
  have hw : Summable (fun n => dirichletWeight k n * (hilbertSequence x n)^2) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (weight_nonneg k n) (sq_nonneg _))
      (fun n => mul_le_mul_of_nonneg_right (weight_bounds k n).2 (sq_nonneg _)) hs
  rw [hilbert_norm_weighted_sq, energy, ← tsum_mul_left]
  constructor
  · apply Summable.tsum_le_tsum _ (hs.mul_left _) hw
    intro n
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (weight_bounds k n).1 (sq_nonneg _)
  · exact hw.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_right (weight_bounds k n).2
      (sq_nonneg _)) hs

abbrev parityInput : ThresholdHilbert := (Real.log 2)⁻¹ • ramanujanPacketHilbert 2
private abbrev fit : mixedClosure := mixedClosure.orthogonalProjectionOnto parityInput

private theorem fit_sub : parityInput - (fit : ThresholdHilbert) = normalizedScreenedTwo := by
  have h := CenteredMeanSnake.normalizedScreenedTwo_eq_projected_packet
  rw [Submodule.starProjection_orthogonal_val, smul_sub] at h
  change parityInput - mixedClosure.starProjection parityInput = _
  simpa only [parityInput, map_smul] using h.symm

theorem trial_split (m : mixedClosure) :
    ‖parityInput - (m : ThresholdHilbert)‖^2 =
      inner ℝ normalizedScreenedTwo normalizedScreenedTwo + ‖fit - m‖^2 := by
  have hu : normalizedScreenedTwo ∈ mixedClosureᗮ :=
    (Submodule.starProjection_apply_eq_zero_iff _).mp mixed_starProjection_screenedTwo
  have ho : inner ℝ normalizedScreenedTwo ((fit-m : mixedClosure) : ThresholdHilbert) = 0 :=
    (real_inner_comm _ _).trans (hu _ (fit-m).property)
  have hv : parityInput - (m : ThresholdHilbert) = normalizedScreenedTwo +
      ((fit-m : mixedClosure) : ThresholdHilbert) := by rw [← fit_sub]; change _ = _ + (_ - _); abel
  rw [hv, norm_add_sq_real, ho, real_inner_self_eq_norm_sq]
  simp

/-- Infimum over the entire physical mixed closure in the polynomial weight. -/
def mixedMinimum (k : ℕ) : ℝ :=
  ⨅ m : mixedClosure, energy k (parityInput - (m : ThresholdHilbert))

/-- Uniform relative error after exact minimization. -/
theorem mixedMinimum_bounds (k : ℕ) :
    (1-(1/9 : ℝ)^k) * inner ℝ normalizedScreenedTwo normalizedScreenedTwo ≤ mixedMinimum k ∧
      mixedMinimum k ≤ inner ℝ normalizedScreenedTwo normalizedScreenedTwo := by
  constructor
  · apply le_ciInf
    intro m
    calc
      _ ≤ (1-(1/9 : ℝ)^k)*‖parityInput - (m : ThresholdHilbert)‖^2 := by
        rw [trial_split]
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg _)) (scale_nonneg _)
      _ ≤ _ := (energy_bounds _ _).1
  · have hb : BddBelow (Set.range (fun m : mixedClosure => energy k (parityInput - m))) := by
      refine ⟨0, Set.forall_mem_range.mpr (fun m => ?_)⟩
      exact (mul_nonneg (scale_nonneg k) (sq_nonneg _)).trans (energy_bounds _ _).1
    calc
      mixedMinimum k ≤ energy k (parityInput - (fit : ThresholdHilbert)) := ciInf_le hb fit
      _ ≤ _ := by rw [fit_sub, real_inner_self_eq_norm_sq]; exact (energy_bounds _ _).2

/-- A finite mixed trial with a certified polynomial cost gives an upper bound
on the true screened scalar. -/
theorem upper_of_dirichlet_trial (k : ℕ) (hk : 0 < k) (m : mixedClosure) :
    inner ℝ normalizedScreenedTwo normalizedScreenedTwo ≤
      energy k (parityInput - (m : ThresholdHilbert)) / (1-(1/9 : ℝ)^k) := by
  have hp : 0 < 1-(1/9 : ℝ)^k :=
    sub_pos.mpr (pow_lt_one₀ (by norm_num) (by norm_num) hk.ne')
  apply (le_div_iff₀ hp).mpr
  rw [mul_comm]
  apply le_trans _ (energy_bounds k (parityInput - (m : ThresholdHilbert))).1
  rw [trial_split]
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg _)) hp.le

/-- A fully explicit error for the limit of the polynomial-metric minima. -/
theorem mixedMinimum_error (k : ℕ) :
    0 ≤ inner ℝ normalizedScreenedTwo normalizedScreenedTwo - mixedMinimum k ∧
      inner ℝ normalizedScreenedTwo normalizedScreenedTwo - mixedMinimum k ≤
        (1000/961 : ℝ) * (1/9 : ℝ)^k := by
  obtain ⟨hl,hh⟩ := mixedMinimum_bounds k
  have hknown : inner ℝ normalizedScreenedTwo normalizedScreenedTwo ≤ (1000/961 : ℝ) := by
    rw [real_inner_self_eq_norm_sq]
    exact normalizedScreenedTwo_norm_sq_lt_period5040.le
  have hp : 0 ≤ (1/9 : ℝ)^k := by positivity
  exact ⟨sub_nonneg.mpr hh, by nlinarith [mul_le_mul_of_nonneg_right hknown hp]⟩

end RiemannResearch.CategoryTheory.ParetoCharacterWeight
