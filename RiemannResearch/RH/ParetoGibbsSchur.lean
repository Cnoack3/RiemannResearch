import RiemannResearch.RH.ParetoGeometricMixture
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.GCongr

/-!
# An exact Gamma Schur weight for the constant-complement Gibbs matrix

The matrix is the elementary specialization 2B(1,2,2) of Kalvoda–Šťovíček,
arXiv:1506.01064, equation (3). The row evaluation below is proved directly
by telescoping, including its boundary at infinity, rather than assumed from
the paper's spectral theorem.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
open Filter
noncomputable section

def gibbsComplementKernel (n m : ℕ) : ℝ :=
  ((n : ℝ) + 1) * ((m : ℝ) + 1) * geometricKernel n m

def gibbsSchurWeight (m : ℕ) : ℝ :=
  Real.Gamma ((m : ℝ) + 3/2) / Real.Gamma ((m : ℝ) + 2)

/-- The row after removing its outer factor n+1. -/
def gibbsSchurTerm (n m : ℕ) : ℝ :=
  2 * ((m : ℝ) + 1) * gibbsSchurWeight m /
    (((n : ℝ) + m + 1) * ((n : ℝ) + m + 2) * ((n : ℝ) + m + 3))

/-- The exact boundary occurring in creative telescoping of adjacent rows. -/
def gibbsSchurBoundary (n m : ℕ) : ℝ :=
  ((m : ℝ) + 1) * gibbsSchurWeight m * m /
    (((n : ℝ) + m + 1) * ((n : ℝ) + m + 2) * ((n : ℝ) + m + 3))

theorem gibbsComplementKernel_symm (n m : ℕ) :
    gibbsComplementKernel n m = gibbsComplementKernel m n := by
  unfold gibbsComplementKernel
  rw [geometricKernel_symm]
  ring

theorem gibbsComplementKernel_pos (n m : ℕ) : 0 < gibbsComplementKernel n m := by
  unfold gibbsComplementKernel
  exact mul_pos (by positivity) (geometricKernel_pos n m)

theorem gibbsSchurWeight_pos (m : ℕ) : 0 < gibbsSchurWeight m := by
  unfold gibbsSchurWeight
  positivity

theorem gibbsSchurWeight_succ (m : ℕ) :
    gibbsSchurWeight (m+1) =
      (((m : ℝ) + 3/2) / ((m : ℝ) + 2)) * gibbsSchurWeight m := by
  unfold gibbsSchurWeight
  push_cast
  rw [show (m : ℝ) + 1 + 3/2 = ((m : ℝ) + 3/2) + 1 by ring,
    show (m : ℝ) + 1 + 2 = ((m : ℝ) + 2) + 1 by ring,
    Real.Gamma_add_one (by positivity : (m : ℝ) + 3/2 ≠ 0),
    Real.Gamma_add_one (by positivity : (m : ℝ) + 2 ≠ 0)]
  have hg : Real.Gamma ((m : ℝ)+2) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos (by positivity))
  have hm : (m : ℝ)+2 ≠ 0 := by positivity
  field_simp
  <;> ring

theorem gibbsSchurWeight_le_initial (m : ℕ) : gibbsSchurWeight m ≤ gibbsSchurWeight 0 := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
      rw [gibbsSchurWeight_succ]
      calc
        _ ≤ 1 * gibbsSchurWeight m := by
          apply mul_le_mul_of_nonneg_right _ (gibbsSchurWeight_pos m).le
          apply (div_le_one (by positivity : (0 : ℝ) < m + 2)).2
          norm_num
        _ ≤ _ := by simpa only [one_mul] using ih

private theorem schur_denominator_bound (n m : ℕ) :
    (((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3)) ≤
      (((n : ℝ) + m + 1) * ((n : ℝ) + m + 2) * ((n : ℝ) + m + 3)) := by
  gcongr <;> nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]

theorem gibbsSchurTerm_nonneg (n m : ℕ) : 0 ≤ gibbsSchurTerm n m := by
  unfold gibbsSchurTerm
  have h := gibbsSchurWeight_pos m
  positivity

theorem gibbsSchurTerm_bound (n m : ℕ) :
    gibbsSchurTerm n m ≤ 2 * gibbsSchurWeight 0 * paretoWeight (m+1) := by
  unfold gibbsSchurTerm
  calc
    _ ≤ 2 * ((m : ℝ) + 1) * gibbsSchurWeight 0 /
        (((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3)) := by
      apply div_le_div₀
      · exact mul_nonneg (by positivity) (gibbsSchurWeight_pos 0).le
      · exact mul_le_mul_of_nonneg_left (gibbsSchurWeight_le_initial m) (by positivity)
      · positivity
      · exact schur_denominator_bound n m
    _ = _ := by
      unfold paretoWeight
      push_cast
      field_simp
      <;> ring

theorem gibbsSchurTerm_summable (n : ℕ) : Summable (gibbsSchurTerm n) := by
  have hw : Summable (fun m => paretoWeight (m+1)) :=
    (summable_nat_add_iff 1).mpr paretoWeight_hasSum.summable
  exact Summable.of_nonneg_of_le (gibbsSchurTerm_nonneg n)
    (gibbsSchurTerm_bound n) (hw.mul_left (2 * gibbsSchurWeight 0))

private theorem reciprocal_real_shift_tendsto (a : ℝ) :
    Tendsto (fun m : ℕ => 1 / ((m : ℝ) + a)) atTop (nhds 0) := by
  simpa only [Function.comp_def, one_div] using tendsto_inv_atTop_zero.comp
    (tendsto_atTop_add_const_right atTop a
      (tendsto_natCast_atTop_atTop : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop))

private theorem gibbsSchur_initial_boundary_tendsto :
    Tendsto (fun m : ℕ => gibbsSchurWeight m / ((m : ℝ) + 2)) atTop (nhds 0) := by
  apply squeeze_zero (fun m => div_nonneg (gibbsSchurWeight_pos m).le (by positivity))
    (fun m => div_le_div_of_nonneg_right (gibbsSchurWeight_le_initial m) (by positivity))
  simpa only [mul_one_div, mul_zero] using
    tendsto_const_nhds.mul (reciprocal_real_shift_tendsto 2)

theorem gibbsSchurTerm_initial_telescope (m : ℕ) :
    gibbsSchurTerm 0 m = (4/3 : ℝ) *
      (gibbsSchurWeight m / ((m : ℝ) + 2) -
        gibbsSchurWeight (m+1) / ((m : ℝ) + 3)) := by
  rw [gibbsSchurWeight_succ]
  unfold gibbsSchurTerm
  norm_num
  field_simp
  <;> ring

theorem gibbsSchurTerm_initial_hasSum :
    HasSum (gibbsSchurTerm 0) ((2/3 : ℝ) * gibbsSchurWeight 0) := by
  apply (gibbsSchurTerm_summable 0).hasSum_iff_tendsto_nat.mpr
  have hp (N : ℕ) : (∑ m ∈ Finset.range N, gibbsSchurTerm 0 m) =
      (4/3 : ℝ) * (gibbsSchurWeight 0 / 2 - gibbsSchurWeight N / ((N : ℝ)+2)) := by
    simp_rw [gibbsSchurTerm_initial_telescope, ← Finset.mul_sum]
    have h := Finset.sum_range_sub'
      (fun m : ℕ => gibbsSchurWeight m / ((m : ℝ)+2)) N
    push_cast at h
    simp only [add_assoc, show (1 : ℝ)+2=3 by norm_num, zero_add] at h
    rw [h]
  simp_rw [hp]
  convert (tendsto_const_nhds.sub gibbsSchur_initial_boundary_tendsto).const_mul (4/3 : ℝ) using 1
  · ring

theorem gibbsSchurBoundary_nonneg (n m : ℕ) : 0 ≤ gibbsSchurBoundary n m := by
  unfold gibbsSchurBoundary
  have h := gibbsSchurWeight_pos m
  positivity

theorem gibbsSchurBoundary_bound (n m : ℕ) :
    gibbsSchurBoundary n m ≤ gibbsSchurWeight 0 / ((m : ℝ) + 1) := by
  unfold gibbsSchurBoundary
  have h0 := gibbsSchurWeight_pos 0
  calc
    _ ≤ ((m : ℝ) + 1) * gibbsSchurWeight 0 * m /
        (((m : ℝ) + 1) * ((m : ℝ) + 2) * ((m : ℝ) + 3)) := by
      apply div_le_div₀
      · positivity
      · gcongr; exact gibbsSchurWeight_le_initial m
      · positivity
      · exact schur_denominator_bound n m
    _ ≤ _ := by
      have hp : 0 < gibbsSchurWeight 0 := gibbsSchurWeight_pos 0
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      apply (div_le_div_iff₀ (by positivity) (by positivity)).2
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ (m : ℝ) + 1 by positivity) hp.le]

theorem gibbsSchurBoundary_tendsto (n : ℕ) :
    Tendsto (gibbsSchurBoundary n) atTop (nhds 0) := by
  apply squeeze_zero (gibbsSchurBoundary_nonneg n) (gibbsSchurBoundary_bound n)
  simpa only [mul_one_div, mul_zero] using
    tendsto_const_nhds.mul (reciprocal_real_shift_tendsto 1)

/-- The entire inter-row defect is an exact boundary difference. -/
theorem gibbsSchurTerm_recurrence (n m : ℕ) :
    ((n : ℝ) + 5/2) * gibbsSchurTerm (n+1) m -
        ((n : ℝ) + 1) * gibbsSchurTerm n m =
      2 * (gibbsSchurBoundary n m - gibbsSchurBoundary n (m+1)) := by
  unfold gibbsSchurTerm gibbsSchurBoundary
  rw [gibbsSchurWeight_succ]
  push_cast
  field_simp
  <;> ring

theorem gibbsSchurTerm_tsum_recurrence (n : ℕ) :
    ((n : ℝ) + 5/2) * (∑' m, gibbsSchurTerm (n+1) m) =
      ((n : ℝ) + 1) * (∑' m, gibbsSchurTerm n m) := by
  let d : ℕ → ℝ := fun m =>
    ((n : ℝ) + 5/2) * gibbsSchurTerm (n+1) m -
      ((n : ℝ) + 1) * gibbsSchurTerm n m
  have hd : Summable d :=
    ((gibbsSchurTerm_summable (n+1)).mul_left _).sub
      ((gibbsSchurTerm_summable n).mul_left _)
  have ht : HasSum d 0 := by
    apply hd.hasSum_iff_tendsto_nat.mpr
    have hp (N : ℕ) : (∑ m ∈ Finset.range N, d m) =
        -(2 * gibbsSchurBoundary n N) := by
      simp only [d, gibbsSchurTerm_recurrence, ← Finset.mul_sum,
        Finset.sum_range_sub']
      simp [gibbsSchurBoundary]
    simp_rw [hp]
    simpa only [mul_zero, neg_zero] using ((gibbsSchurBoundary_tendsto n).const_mul 2).neg
  have he := ht.tsum_eq
  dsimp [d] at he
  rw [((gibbsSchurTerm_summable (n+1)).mul_left _).tsum_sub
    ((gibbsSchurTerm_summable n).mul_left _), tsum_mul_left, tsum_mul_left] at he
  exact sub_eq_zero.mp he

end
end RiemannResearch.RH.Pareto
