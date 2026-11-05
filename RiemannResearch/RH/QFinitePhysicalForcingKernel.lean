/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QFiniteSchurEighth
import RiemannResearch.RH.QSquarefreeKernelLocalization

/-! # Physical kernel for the matched finite forcing

Compose the inverse evaluation rows with the physical input map. The resulting
kernel uses the full stage projection and has a uniformly bounded first moment
of its squared column norm. A fourth-moment test gives a sufficient RH criterion.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QSquarefreeFiniteDisplacement
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open QSquarefreeCorrectionKernel QShiftedReciprocal QFiniteSupportDualCriterion ArithmeticCumulative

/-- The full stage projection kernel, composed with the physical forcing on its input side. -/
def physicalForcingKernel (N n k : ℕ) : ℝ := qSequence (kernel N n) k / (k : ℝ)

/-- Finite actual-input variance at one evaluated site. -/
def physicalForcingVariance (N T n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (T + 1), weight k * (physicalForcingKernel N n k) ^ 2

/-- The complete signed projection answer for the actual physical input coordinates. -/
theorem physicalForcing_pairing (N T n : ℕ) (f : QHilbert) :
    zetaTwo * qSequence ((stage N).starProjection (finiteHead T (B f))) n =
      ∑ k ∈ Finset.range (T + 1), weight k * qSequence f k * physicalForcingKernel N n k := by
  have he : inner ℝ (kernel N n) (finiteHead T (B f)) =
      qSequence ((stage N).starProjection (finiteHead T (B f))) n := by
    change inner ℝ ((stage N).starProjection (evaluation n)) (finiteHead T (B f)) = _
    rw [RiemannResearch.Analysis.ResidualizedProjectionKernel.projection_inner,
      real_inner_comm, inner_evaluation]
  rw [← he]
  exact forcingSchurRHS_physical T f (kernel N n)

/-- This is the physical pairing of the complete signed inverse-Schur row. -/
theorem schur_row_composed_pairing (N T d0 n : ℕ) (f : QHilbert)
    (hT : 1 ≤ T) (ha : T < d0) (hd : d0 ≤ N + 1) (hs : Squarefree d0) :
    zetaTwo * dotProduct (schurEvaluationRow N T d0 n) (forcingSchurRHS T d0 f) =
      ∑ k ∈ Finset.range (T + 1), weight k * qSequence f k * physicalForcingKernel N n k := by
  rw [← schur_head_pairing N T d0 n f hT ha hd hs]
  exact physicalForcing_pairing N T n f

theorem physicalForcing_variance_bound (N T n : ℕ) (f : QHilbert) :
    (zetaTwo * qSequence ((stage N).starProjection (finiteHead T (B f))) n) ^ 2 ≤
      (∑ k ∈ Finset.range (T + 1), weight k * (qSequence f k) ^ 2) *
        physicalForcingVariance N T n := by
  let a := fun k => Real.sqrt (weight k) * qSequence f k
  let b := fun k => Real.sqrt (weight k) * physicalForcingKernel N n k
  have hroot (k : ℕ) : Real.sqrt (weight k) ^ 2 = weight k :=
    Real.sq_sqrt (Pareto.positiveWeight_nonneg k)
  have hab (k : ℕ) : a k * b k = weight k * qSequence f k * physicalForcingKernel N n k := by
    calc
      _ = Real.sqrt (weight k) ^ 2 * qSequence f k * physicalForcingKernel N n k := by
        dsimp only [a,b]
        ring
      _ = _ := by rw [hroot]
  have ha (k : ℕ) : (a k) ^ 2 = weight k * (qSequence f k) ^ 2 := by
    dsimp only [a]; rw [mul_pow, hroot]
  have hb (k : ℕ) : (b k) ^ 2 = weight k * (physicalForcingKernel N n k) ^ 2 := by
    dsimp only [b]; rw [mul_pow, hroot]
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (T + 1)) a b
  simp only [hab, ha, hb] at h
  rw [physicalForcing_pairing]
  exact h

theorem projectedFiniteForcing_physical_variance (N T n : ℕ) :
    (zetaTwo * qSequence (projectedFiniteForcing N T) n) ^ 2 ≤ physicalForcingVariance N T n := by
  rw [projectedFiniteForcing, B_finiteHead_eq]
  have hV : 0 ≤ physicalForcingVariance N T n := Finset.sum_nonneg
    (fun k _ => mul_nonneg (Pareto.positiveWeight_nonneg k) (sq_nonneg _))
  exact (physicalForcing_variance_bound N T n _).trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (finite_pareto_energy_le N _) hV)

/-- Every complete column has Q energy at most ζ(2), independently of the stage. -/
theorem physicalForcing_kernel_column_le (N k : ℕ) (s : Finset ℕ) :
    (∑ n ∈ s, positiveQWeight n * (physicalForcingKernel N n k) ^ 2) ≤ zetaTwo := by
  cases k with
  | zero => simpa [physicalForcingKernel] using zetaTwo_pos.le
  | succ j =>
    let g := kernel N (j + 1)
    have hhead : (∑ n ∈ s, positiveQWeight n * (qSequence g n) ^ 2) ≤ ‖g‖^2 := by
      rw [qNorm_weighted_sq]
      exact (qSequence_square_summable g).sum_le_tsum s
        (fun n _ => mul_nonneg (positiveQWeight_nonneg _) (sq_nonneg _))
    have hnorm : ‖g‖^2 ≤ zetaTwo * ((j + 1 : ℕ) : ℝ) ^ 2 := by
      simpa only [Nat.cast_add, Nat.cast_one, g] using kernel_norm_sq_le N j
    calc
      _ = (∑ n ∈ s, positiveQWeight n * (qSequence g n) ^ 2) / ((j + 1 : ℕ) : ℝ) ^ 2 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro n hn
        rw [physicalForcingKernel, kernel_physical_symmetry N n (j + 1), div_pow]
        ring
      _ ≤ zetaTwo := (div_le_iff₀ (by positivity)).mpr (hhead.trans hnorm)

/-- The entire first Q-moment of these composed variances is uniformly bounded,
as seen on arbitrary finite output sets. -/
theorem physicalForcing_variance_first_moment (N T : ℕ) (s : Finset ℕ) :
    (∑ n ∈ s, positiveQWeight n * physicalForcingVariance N T n) ≤ zetaTwo := by
  have hw : (∑ k ∈ Finset.range (T + 1), weight k) ≤ 1 := by
    exact (Pareto.positiveWeight_summable.sum_le_tsum (Finset.range (T + 1))
      (fun k _ => Pareto.positiveWeight_nonneg k)).trans_eq Pareto.positiveWeight_tsum
  calc
    _ = ∑ n ∈ s, ∑ k ∈ Finset.range (T + 1),
          positiveQWeight n * (weight k * (physicalForcingKernel N n k) ^ 2) := by
        simp only [physicalForcingVariance, Finset.mul_sum]
    _ = ∑ k ∈ Finset.range (T + 1), ∑ n ∈ s,
          positiveQWeight n * (weight k * (physicalForcingKernel N n k) ^ 2) := Finset.sum_comm
    _ = ∑ k ∈ Finset.range (T + 1), weight k *
          (∑ n ∈ s, positiveQWeight n * (physicalForcingKernel N n k) ^ 2) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        exact Finset.sum_congr rfl (fun n _ => by ring)
    _ ≤ ∑ k ∈ Finset.range (T + 1), weight k * zetaTwo :=
        Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left
          (physicalForcing_kernel_column_le N k s) (Pareto.positiveWeight_nonneg k))
    _ ≤ zetaTwo := by
        rw [← Finset.sum_mul]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hw zetaTwo_pos.le

/-- Aligned fourth moment of the physical input variances. -/
def physicalForcingVarianceFourthHead (N T : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), (physicalForcingVariance N T n) ^ 4 / (n : ℝ) ^ 2

theorem projectedFiniteForcing_eighth_le_composed (N T : ℕ) :
    zetaTwo ^ 8 * eighthHead (projectedFiniteForcing N T) N ≤
      physicalForcingVarianceFourthHead N T := by
  unfold eighthHead physicalForcingVarianceFourthHead
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  rw [← mul_div_assoc, Even.pow_abs (by decide : Even 8)]
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  have h := pow_le_pow_left₀ (sq_nonneg _) (projectedFiniteForcing_physical_variance N T n) 4
  simpa only [← pow_mul, mul_pow] using h

/-- A cofinal fourth-moment test on the true inputs, with no auxiliary anchor choice. -/
theorem riemannHypothesis_of_physicalForcing_variance (happrox : HasSubcriticalApproximation)
    (T : ℕ → ℕ) (hT : Tendsto T atTop atTop) (C : ℝ)
    (h : ∃ᶠ N : ℕ in atTop, physicalForcingVarianceFourthHead N (T N) ≤ C) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_displacement_eighth happrox
  apply summable_eighth_of_frequent_diagonal (projectedFiniteForcing_tendsto T hT)
    (C / zetaTwo ^ 8)
  apply h.mono
  intro N hN
  apply (le_div_iff₀ (pow_pos zetaTwo_pos 8)).mpr
  rw [mul_comm (eighthHead _ _)]
  exact (projectedFiniteForcing_eighth_le_composed N (T N)).trans hN

open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage ZetaTwoParetoTransfer
open QShiftedReciprocal QFiniteSupportDualCriterion QSquarefreeCorrectionKernel ArithmeticCumulative

/-- The finite physical kernel, in the Pareto Hilbert space of the matched fit. -/
def paretoPhysicalTest (N T n : ℕ) : Pareto.ThresholdHilbert :=
  toPareto (finiteHead T (ZetaTwoHilbert.reciprocalD (kernel N n)))

/-- Only the part orthogonal to the actual Pareto stage can pair with its residual. -/
def paretoPhysicalDefect (N T n : ℕ) : Pareto.ThresholdHilbert :=
  paretoPhysicalTest N T n - (paretoStage N).starProjection (paretoPhysicalTest N T n)

private theorem head_reciprocal_change (T : ℕ) (z : QHilbert) :
    finiteHead T (ZetaTwoHilbert.reciprocalD z) - B (finiteHead T (ZetaTwoHilbert.reciprocalD z)) =
      B (finiteHead T z) := by
  apply lp.ext
  funext j
  change finiteHead T (ZetaTwoHilbert.reciprocalD z) j -
      B (finiteHead T (ZetaTwoHilbert.reciprocalD z)) j = B (finiteHead T z) j
  rw [B_apply, B_apply]
  by_cases hj : j < T
  · simp only [finiteHead_apply_of_lt T _ j hj, ZetaTwoHilbert.reciprocalD_apply]
    field_simp [show (j : ℝ) + 1 ≠ 0 by positivity, show (j : ℝ) + 2 ≠ 0 by positivity]
    ring
  · simp only [finiteHead_apply_eq_zero T _ j (by omega), zero_div, sub_zero]

private theorem pareto_head_kernel_pairing (T : ℕ) (f z : QHilbert) :
    inner ℝ (toPareto f) (toPareto (finiteHead T (ZetaTwoHilbert.reciprocalD z))) =
      zetaTwo * inner ℝ z (finiteHead T (B f)) := by
  rw [pareto_inner_identity, ← inner_sub_right, head_reciprocal_change,
    ← B_symmetric, ← finiteHead_inner, real_inner_comm (finiteHead T (B f)) z]

theorem paretoPhysicalTest_norm_sq (N T n : ℕ) :
    ‖paretoPhysicalTest N T n‖^2 = physicalForcingVariance N T n := by
  let g := ZetaTwoHilbert.reciprocalD (kernel N n)
  have hh (k : ℕ) (hk : k ≤ T) : qSequence (finiteHead T g) k = qSequence g k := by
    cases k with
    | zero => simp
    | succ j => rw [qSequence_succ, qSequence_succ, finiteHead_apply_of_lt _ _ _ (by omega)]
  rw [← real_inner_self_eq_norm_sq]
  unfold paretoPhysicalTest
  rw [pareto_head_kernel_pairing, forcingSchurRHS_physical]
  unfold physicalForcingVariance physicalForcingKernel
  apply Finset.sum_congr rfl
  intro k hk
  have hkT : k ≤ T := by have := Finset.mem_range.mp hk; omega
  change weight k * qSequence (finiteHead T g) k * (qSequence (kernel N n) k / (k : ℝ)) = _
  rw [hh k hkT]
  change weight k * qSequence (ZetaTwoHilbert.reciprocalD (kernel N n)) k *
    (qSequence (kernel N n) k / (k : ℝ)) = _
  rw [qSequence_reciprocalD]
  ring

theorem projectedFiniteForcing_pareto_residual_pairing (N T n : ℕ) :
    zetaTwo * qSequence (projectedFiniteForcing N T) n =
      inner ℝ (toPareto (qOne - finitePFit N)) (paretoPhysicalDefect N T n) := by
  let f := qOne - finitePFit N
  let U := paretoPhysicalTest N T n
  let W := paretoStage N
  have hf : toPareto f = Pareto.hilbertOne - W.starProjection Pareto.hilbertOne := by
    dsimp only [f, W, finitePFit]
    rw [QParetoClosedProjectionComparison.toPareto_sub,
      QParetoClosedProjectionComparison.toPareto_pFit, toPareto_qOne]
  have hz : inner ℝ (toPareto f) (W.starProjection U) = 0 := by
    rw [hf, real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal (W.starProjection_apply_mem U)
      (Submodule.sub_starProjection_mem_orthogonal _)
  have he : inner ℝ (kernel N n) (finiteHead T (B f)) =
      qSequence (projectedFiniteForcing N T) n := by
    rw [projectedFiniteForcing, B_finiteHead_eq]
    change inner ℝ ((stage N).starProjection (evaluation n)) (finiteHead T (B f)) = _
    rw [RiemannResearch.Analysis.ResidualizedProjectionKernel.projection_inner,
      real_inner_comm, inner_evaluation]
  change _ = inner ℝ (toPareto f) (U - W.starProjection U)
  rw [inner_sub_right, hz, sub_zero, ← he]
  exact (pareto_head_kernel_pairing T f (kernel N n)).symm

/-- Moving the matched orthogonal projection onto the kernel leaves a pairing with 1. -/
theorem projectedFiniteForcing_pareto_defect_mean (N T n : ℕ) :
    zetaTwo * qSequence (projectedFiniteForcing N T) n =
      inner ℝ Pareto.hilbertOne (paretoPhysicalDefect N T n) := by
  rw [projectedFiniteForcing_pareto_residual_pairing, finitePFit,
    QParetoClosedProjectionComparison.toPareto_sub,
    QParetoClosedProjectionComparison.toPareto_pFit, toPareto_qOne, inner_sub_left]
  have hz : inner ℝ ((paretoStage N).starProjection Pareto.hilbertOne)
      (paretoPhysicalDefect N T n) = 0 :=
    Submodule.inner_right_of_mem_orthogonal ((paretoStage N).starProjection_apply_mem _)
      (Submodule.sub_starProjection_mem_orthogonal (K := paretoStage N) (paretoPhysicalTest N T n))
  rw [hz, sub_zero]

theorem projectedFiniteForcing_defect_variance (N T n : ℕ) :
    (zetaTwo * qSequence (projectedFiniteForcing N T) n) ^ 2 ≤ ‖paretoPhysicalDefect N T n‖^2 := by
  rw [projectedFiniteForcing_pareto_defect_mean]
  have h := real_inner_mul_inner_self_le Pareto.hilbertOne (paretoPhysicalDefect N T n)
  simpa only [← pow_two, real_inner_self_eq_norm_sq, Pareto.hilbertOne_norm_sq, one_mul] using h

/-- The full physical variance splits into a legal component and the effective variance. -/
theorem physicalForcing_variance_split (N T n : ℕ) :
    physicalForcingVariance N T n =
      ‖paretoPhysicalDefect N T n‖^2 +
        ‖(paretoStage N).starProjection (paretoPhysicalTest N T n)‖^2 := by
  rw [← paretoPhysicalTest_norm_sq]
  have ht := RiemannResearch.Analysis.projection_trial_energy (paretoStage N)
    (paretoPhysicalTest N T n) 0 (Submodule.zero_mem _)
  simpa only [sub_zero, paretoPhysicalDefect] using ht

/-- The effective kernel moment retains the Pareto orthogonal complement at every site. -/
def paretoDefectEighthHead (N T : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), ‖paretoPhysicalDefect N T n‖ ^ 8 / (n : ℝ) ^ 2

/-- Keep the energy of the actual projection residual when summing the physical upper bound. -/
theorem projectedFiniteForcing_eighth_le_pareto_defect (N T : ℕ) :
    zetaTwo ^ 8 * eighthHead (projectedFiniteForcing N T) N ≤
      ‖toPareto (qOne - finitePFit N)‖ ^ 8 * paretoDefectEighthHead N T := by
  unfold eighthHead paretoDefectEighthHead
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _
  rw [← mul_div_assoc, ← mul_div_assoc, Even.pow_abs (by decide : Even 8)]
  apply div_le_div_of_nonneg_right _ (sq_nonneg (n : ℝ))
  have h := real_inner_mul_inner_self_le
    (toPareto (qOne - finitePFit N)) (paretoPhysicalDefect N T n)
  rw [← projectedFiniteForcing_pareto_residual_pairing, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, ← pow_two] at h
  simpa only [← pow_mul, mul_pow] using pow_le_pow_left₀ (sq_nonneg _) h 4

/-- The Pareto residual energy may offset growth of the effective kernel moment
while the input head increases arbitrarily slowly. -/
theorem riemannHypothesis_of_cofinal_pareto_defect (happrox : HasSubcriticalApproximation)
    (T : ℕ → ℕ) (hT : Tendsto T atTop atTop) (C : ℝ)
    (h : ∃ᶠ N : ℕ in atTop, ‖toPareto (qOne - finitePFit N)‖ ^ 8 *
      paretoDefectEighthHead N (T N) ≤ C) : RiemannHypothesis := by
  apply riemannHypothesis_of_displacement_eighth happrox
  apply summable_eighth_of_frequent_diagonal (projectedFiniteForcing_tendsto T hT) (C / zetaTwo ^ 8)
  apply h.mono
  intro N hN
  apply (le_div_iff₀ (pow_pos zetaTwo_pos 8)).mpr
  rw [mul_comm (eighthHead _ _)]
  exact (projectedFiniteForcing_eighth_le_pareto_defect N (T N)).trans hN

end RiemannResearch.RH.QSquarefreeFiniteDisplacement
