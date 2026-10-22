import RiemannResearch.RH.AnnularPrimePairTargets
import RiemannResearch.RH.AnnularArithmeticIntegrals
import RiemannResearch.LinearAlgebra.FiniteIntegralGram
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Dist
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Tactic.Linarith

/-!
# Actual annular arithmetic integral kernel

Prepared as a mathematical source continuation for coordinator checking.
Current checking evidence and remaining obligations are recorded in
`RiemannResearch/ANNULAR_FORMALIZATION_20261010.md`.
This historical preparation note is not a current verification claim.

This closes the local product integrability and actual integral/quadratic
identification targets from AnnularPrimePairTargets, subject to compilation.

The integrals use the original Icc 1 X restriction. The arithmetic signal has
the actual von Mangoldt coefficients minus one, including n = 1. Fixed-cutoff
replacement is exact by support, with no discarded endpoint or singleton term.
No singular-series asymptotic, RH energy criterion, or residual estimate is
proved or assumed by the local identities below.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators

namespace RiemannResearch.RH.AnnularPrimePair
open RiemannResearch.LinearAlgebra

theorem continuousOn_annularScaled (n : ℕ) (X : ℝ) :
    ContinuousOn (fun x : ℝ => annularArithmeticWeight ((n : ℝ) / x)) (Icc 1 X) := by
  apply continuous_annularArithmeticWeight.comp_continuousOn'
  exact continuousOn_const.div continuousOn_id
    (fun x hx => ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1))

theorem continuousOn_kernelIntegrand (X : ℝ) (n k : ℕ) :
    ContinuousOn
      (fun x : ℝ => annularArithmeticWeight ((n : ℝ) / x) *
        annularArithmeticWeight ((k : ℝ) / x) / x ^ 2) (Icc 1 X) := by
  apply ((continuousOn_annularScaled n X).mul
    (continuousOn_annularScaled k X)).div (continuousOn_id.pow 2)
  intro x hx
  exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1))

/-- Actual local integrability is unconditional, even when Icc 1 X is empty. -/
theorem kernelIntegrand_integrableOn (X : ℝ) (n k : ℕ) :
    IntegrableOn
      (fun x : ℝ => annularArithmeticWeight ((n : ℝ) / x) *
        annularArithmeticWeight ((k : ℝ) / x) / x ^ 2) (Icc 1 X) :=
  (continuousOn_kernelIntegrand X n k).integrableOn_Icc

theorem kernelGram_productIntegrable (X : ℝ) (n k : ℕ) :
    Integrable (fun x : ℝ =>
      annularArithmeticWeight ((n : ℝ) / x) *
        annularArithmeticWeight ((k : ℝ) / x) * (1 / x ^ 2))
      (volume.restrict (Icc 1 X)) := by
  simpa only [IntegrableOn, div_eq_mul_inv, one_mul] using
    kernelIntegrand_integrableOn X n k

theorem localKernelIntegrability : LocalKernelIntegrability := by
  intro X hX n k
  exact kernelIntegrand_integrableOn X n k

theorem kernel_symmetric (X : ℝ) (n k : ℕ) : kernel X n k = kernel X k n := by
  unfold kernel
  apply integral_congr_ae
  exact Eventually.of_forall (fun _ => by ring)

theorem kernel_nonnegative (X : ℝ) (n k : ℕ) : 0 ≤ kernel X n k := by
  unfold kernel
  apply integral_nonneg_of_ae
  exact Eventually.of_forall (fun x => div_nonneg
    (mul_nonneg (annularArithmeticWeight_nonnegative _)
      (annularArithmeticWeight_nonnegative _)) (sq_nonneg x))

/-- The exact ratio-eight boundary is zero, rather than an exceptional pair. -/
theorem kernel_eq_zero_of_eight_mul_le (X : ℝ) (n k : ℕ)
    (hnk : 8 * k ≤ n) : kernel X n k = 0 := by
  unfold kernel
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx.1
  have hnk' : (8 : ℝ) * (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnk
  rw [annularArithmeticWeight_mul_eq_zero_of_eight_mul_le hx0 hnk']
  simp

/-- Symmetric form of exact separation; equality k = 8*n also vanishes. -/
theorem kernel_eq_zero_of_eight_mul_le_right (X : ℝ) (n k : ℕ)
    (hnk : 8 * n ≤ k) : kernel X n k = 0 := by
  rw [kernel_symmetric X n k]
  exact kernel_eq_zero_of_eight_mul_le X k n hnk

theorem indices_mono {x X : ℝ} (h : x ≤ X) : indices x ⊆ indices X := by
  intro n hn
  simp only [indices, Finset.mem_Icc] at hn ⊢
  exact ⟨hn.1, hn.2.trans (Nat.floor_mono h)⟩

/-- The variable cutoff may be replaced on [1,X] by the single finite cutoff X. -/
theorem actualCentered_eq_fixed_cutoff {x X : ℝ} (hx : 1 ≤ x) (hX : x ≤ X) :
    actualCentered x = annularCenteredFinite (indices X) x := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  unfold actualCentered annularCenteredFinite
  apply Finset.sum_subset (indices_mono hX)
  intro n hn hnnot
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hnf : Nat.floor x < n := by
    by_contra h
    exact hnnot (Finset.mem_Icc.mpr ⟨hn1, le_of_not_gt h⟩)
  have hcast : (Nat.floor x : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mpr hnf)
  have hxn : x < (n : ℝ) := (Nat.lt_floor_add_one x).trans_le hcast
  have hratio : 1 ≤ (n : ℝ) / x :=
    (le_div_iff₀ hx0).mpr (by simpa using hxn.le)
  rw [annularArithmeticWeight_eq_zero_of_one_le hratio]
  exact mul_zero _

theorem continuousOn_annularCenteredFinite (s : Finset ℕ) (X : ℝ) :
    ContinuousOn (annularCenteredFinite s) (Icc 1 X) := by
  unfold annularCenteredFinite
  exact continuousOn_finsetSum s (fun n hn =>
    continuousOn_const.mul (continuousOn_annularScaled n X))

theorem actualCentered_continuousOn (X : ℝ) :
    ContinuousOn actualCentered (Icc 1 X) := by
  apply (continuousOn_annularCenteredFinite (indices X) X).congr
  intro x hx
  exact actualCentered_eq_fixed_cutoff hx.1 hx.2

theorem actualEnergyDensity_integrableOn (X : ℝ) :
    IntegrableOn (fun x : ℝ => actualCentered x ^ 2 / x ^ 2) (Icc 1 X) := by
  apply ContinuousOn.integrableOn_Icc
  apply ((actualCentered_continuousOn X).pow 2).div (continuousOn_id.pow 2)
  intro x hx
  exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le zero_lt_one hx.1))

theorem kernel_eq_integralWeightedGram (X : ℝ) :
    kernel X = integralWeightedGram (volume.restrict (Icc 1 X))
      (fun x : ℝ => 1 / x ^ 2)
      (fun n : ℕ => fun x : ℝ => annularArithmeticWeight ((n : ℝ) / x)) := by
  funext n k
  simp only [kernel, integralWeightedGram, div_eq_mul_inv, one_mul]

/-- The actual integral, rather than merely an abstract matrix quadratic,
equals the diagonal plus the signed model and residual terms. -/
theorem actualIntegralEnergy_eq_quadratic (X : ℝ) :
    actualIntegralEnergy X = actualQuadraticEnergy X := by
  have hpair : ∀ n ∈ indices X, ∀ k ∈ indices X,
      Integrable (fun x : ℝ =>
        annularArithmeticWeight ((n : ℝ) / x) *
          annularArithmeticWeight ((k : ℝ) / x) * (1 / x ^ 2))
        (volume.restrict (Icc 1 X)) := by
    intro n hn k hk
    exact kernelGram_productIntegrable X n k
  have hgram := centeredKernelEnergy_integralGram_eq
    (volume.restrict (Icc 1 X)) (indices X)
    ArithmeticFunction.vonMangoldt (fun _ => 1)
    (fun x : ℝ => 1 / x ^ 2)
    (fun n : ℕ => fun x : ℝ => annularArithmeticWeight ((n : ℝ) / x)) hpair
  unfold actualQuadraticEnergy
  rw [kernel_eq_integralWeightedGram, hgram]
  unfold actualIntegralEnergy
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [actualCentered_eq_fixed_cutoff hx.1 hx.2]
  simp only [annularCenteredFinite, div_eq_mul_inv, one_mul]

theorem actualIntegralQuadraticIdentity : ActualIntegralQuadraticIdentity := by
  intro X hX
  exact actualIntegralEnergy_eq_quadratic X

theorem actualIntegralEnergy_eq_model_add_residual (X : ℝ) :
    actualIntegralEnergy X = actualModel X + actualResidual X := by
  rw [actualIntegralEnergy_eq_quadratic, actualQuadraticEnergy_eq_model_add_residual]

theorem actualQuadraticEnergy_nonnegative (X : ℝ) : 0 ≤ actualQuadraticEnergy X := by
  rw [← actualIntegralEnergy_eq_quadratic]
  unfold actualIntegralEnergy
  apply integral_nonneg_of_ae
  exact Eventually.of_forall (fun x => div_nonneg (sq_nonneg _) (sq_nonneg x))

/-- The actual diagonal, with the singleton coefficient at n = 1 retained. -/
def actualDiagonal (X : ℝ) : ℝ :=
  ∑ n ∈ indices X, (ArithmeticFunction.vonMangoldt n - 1) ^ 2 * kernel X n n

theorem actualQuadraticEnergy_eq_diagonal_add_strictTriangle (X : ℝ) :
    actualQuadraticEnergy X = actualDiagonal X +
      2 * ∑ k ∈ indices X, ∑ n ∈ indices X with n < k,
        (ArithmeticFunction.vonMangoldt n - 1) *
          (ArithmeticFunction.vonMangoldt k - 1) * kernel X n k := by
  have hsym : ∀ n k : ℕ,
      (ArithmeticFunction.vonMangoldt n - 1) *
          (ArithmeticFunction.vonMangoldt k - 1) * kernel X n k =
        (ArithmeticFunction.vonMangoldt k - 1) *
          (ArithmeticFunction.vonMangoldt n - 1) * kernel X k n := by
    intro n k
    rw [kernel_symmetric X n k]
    ring
  simpa only [actualQuadraticEnergy, centeredKernelEnergy, actualDiagonal, pow_two] using
    symmetric_sum_finset_diagonal_triangle (indices X)
      (fun n k => (ArithmeticFunction.vonMangoldt n - 1) *
        (ArithmeticFunction.vonMangoldt k - 1) * kernel X n k) hsym

theorem actualModel_eq_diagonal_add_strictTriangle (X : ℝ) :
    actualModel X = actualDiagonal X +
      2 * ∑ k ∈ indices X, ∑ n ∈ indices X with n < k,
        (singularSeries (k - n) - 1) * kernel X n k := by
  let F : ℕ → ℕ → ℝ := fun n k =>
    (if n = k then (ArithmeticFunction.vonMangoldt n - 1) ^ 2 else
      singularSeries (Nat.dist n k) - 1) * kernel X n k
  have hsym : ∀ n k, F n k = F k n := by
    intro n k
    by_cases hnk : n = k
    · subst k
      rfl
    · simp only [F, if_neg hnk, if_neg (Ne.symm hnk)]
      rw [Nat.dist_comm n k, kernel_symmetric X n k]
  have htriangle :
      (∑ k ∈ indices X, ∑ n ∈ indices X with n < k, F n k) =
        ∑ k ∈ indices X, ∑ n ∈ indices X with n < k,
          (singularSeries (k - n) - 1) * kernel X n k := by
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro n hn
    have hnk : n < k := (Finset.mem_filter.mp hn).2
    simp only [F, if_neg (ne_of_lt hnk), Nat.dist_eq_sub_of_le hnk.le]
  have hid := symmetric_sum_finset_diagonal_triangle (indices X) F hsym
  rw [htriangle] at hid
  simpa only [actualModel, centeredKernelModel, F, one_mul, mul_one, if_pos rfl,
    ite_true, actualDiagonal] using hid

/-- Exact signed residual in the paper's ordered n < k convention. The
actual diagonal cancels against the model diagonal; neither singleton term
is dropped and the +2 is kept explicitly. -/
theorem actualResidual_eq_twice_strictTriangle (X : ℝ) :
    actualResidual X =
      2 * ∑ k ∈ indices X, ∑ n ∈ indices X with n < k,
        (ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt k -
          ArithmeticFunction.vonMangoldt n - ArithmeticFunction.vonMangoldt k +
          2 - singularSeries (k - n)) * kernel X n k := by
  have hpair :
      (∑ k ∈ indices X, ∑ n ∈ indices X with n < k,
        (ArithmeticFunction.vonMangoldt n - 1) *
          (ArithmeticFunction.vonMangoldt k - 1) * kernel X n k) -
      (∑ k ∈ indices X, ∑ n ∈ indices X with n < k,
        (singularSeries (k - n) - 1) * kernel X n k) =
      ∑ k ∈ indices X, ∑ n ∈ indices X with n < k,
        (ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt k -
          ArithmeticFunction.vonMangoldt n - ArithmeticFunction.vonMangoldt k +
          2 - singularSeries (k - n)) * kernel X n k := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hid := actualQuadraticEnergy_eq_model_add_residual X
  rw [actualQuadraticEnergy_eq_diagonal_add_strictTriangle,
    actualModel_eq_diagonal_add_strictTriangle] at hid
  linarith

/-- Exact arithmetic localization of the full signed prime-pair residual.
Both inequalities are strict: n = k is the already canceled diagonal and
k = 8*n has exactly zero kernel. No arithmetic pair estimate is used. -/
theorem actualResidual_eq_twice_comparableTriangle (X : ℝ) :
    actualResidual X =
      2 * ∑ k ∈ indices X, ∑ n ∈ indices X with n < k ∧ k < 8 * n,
        (ArithmeticFunction.vonMangoldt n * ArithmeticFunction.vonMangoldt k -
          ArithmeticFunction.vonMangoldt n - ArithmeticFunction.vonMangoldt k +
          2 - singularSeries (k - n)) * kernel X n k := by
  rw [actualResidual_eq_twice_strictTriangle]
  apply congrArg (fun z : ℝ => 2 * z)
  apply Finset.sum_congr rfl
  intro k hk
  have hsub :
      (indices X).filter (fun n => n < k ∧ k < 8 * n) ⊆
        (indices X).filter (fun n => n < k) := by
    intro n hn
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hn).1, (Finset.mem_filter.mp hn).2.1⟩
  symm
  apply Finset.sum_subset hsub
  intro n hn hnnot
  have hnk : n < k := (Finset.mem_filter.mp hn).2
  have h8 : 8 * n ≤ k := by
    apply le_of_not_gt
    intro hkn
    exact hnnot (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1, hnk, hkn⟩)
  rw [kernel_eq_zero_of_eight_mul_le_right X n k h8]
  exact mul_zero _

end RiemannResearch.RH.AnnularPrimePair
