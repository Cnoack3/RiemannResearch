/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.CenteredHyperbolicFrames
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Concrete finite hyperbolic rows

Source: user-provided `Landau_Density_Providers_and_Stronger_Frames.tex`,
centered hyperbolic factorization proof. Arbitrary finite rectangular matrices
include every original zero copy and frequency; no distribution theorem is
required. The concrete remainder is identified with the absolutely convergent
centered operator series before bounding its norm.
-/

noncomputable section
open scoped BigOperators InnerProductSpace

namespace RiemannResearch.Analysis.CenteredHyperbolicFrames

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- A rectangular matrix in the actual Euclidean Hilbert norm. -/
def rowAnalysis (M : κ → ι → ℂ) :
    EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ κ :=
  ((Matrix.toLpLin 2 2) (Matrix.of M)).toContinuousLinearMap

omit [DecidableEq κ] in
@[simp] theorem rowAnalysis_apply (M : κ → ι → ℂ)
    (f : EuclideanSpace ℂ ι) (k : κ) :
    rowAnalysis M f k = ∑ i, M k i*f i := by
  change (((Matrix.toLpLin 2 2) (Matrix.of M)) f) k = _
  rw [Matrix.toLpLin_apply]
  rfl

@[simp] theorem rowAnalysis_single (M : κ → ι → ℂ) (k : κ) (i : ι) :
    rowAnalysis M (EuclideanSpace.single i 1) k = M k i := by
  rw [rowAnalysis_apply]
  simp [PiLp.single_apply]

def rectangleEntryCLM (k : κ) (i : ι) :
    (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ κ) →L[ℂ] ℂ :=
  (innerSL ℂ ((EuclideanSpace.basisFun κ ℂ) k)).comp
    (ContinuousLinearMap.apply ℂ (EuclideanSpace ℂ κ)
      ((EuclideanSpace.basisFun ι ℂ) i))

omit [DecidableEq κ] in
@[simp] theorem rectangleEntryCLM_apply
    (V : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ κ) (k : κ) (i : ι) :
    rectangleEntryCLM k i V = V (EuclideanSpace.single i 1) k := by
  change inner ℂ ((EuclideanSpace.basisFun κ ℂ) k)
    (V ((EuclideanSpace.basisFun ι ℂ) i)) = _
  rw [EuclideanSpace.basisFun_inner, EuclideanSpace.basisFun_apply]

theorem rectangleEntry_ext
    {V W : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ κ}
    (h : ∀ k i, V (EuclideanSpace.single i 1) k = W (EuclideanSpace.single i 1) k) :
    V = W := by
  ext f k
  have hf : f = ∑ i : ι, f i • EuclideanSpace.single i 1 := by
    ext i
    simp [Pi.single_apply]
  rw [hf, map_sum, map_sum]
  simp only [map_smul, WithLp.ofLp_sum, Finset.sum_apply,
    WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  change (∑ i, f i*V (EuclideanSpace.single i 1) k) =
    (∑ i, f i*W (EuclideanSpace.single i 1) k)
  apply Finset.sum_congr rfl
  intro i hi
  rw [h k i]

def cosineAnalysis (M : κ → ι → ℂ) (a : κ → ℝ) (x : ι → ℝ) :=
  rowAnalysis (fun k i => (Real.cosh (a k*x i) : ℂ)*M k i)

def sineAnalysis (M : κ → ι → ℂ) (a : κ → ℝ) (x : ι → ℝ) :=
  rowAnalysis (fun k i => (Real.sinh (a k*x i) : ℂ)*M k i)

def centerMultiplier (a : κ → ℝ) (b : ℝ) :
    EuclideanSpace ℂ κ →L[ℂ] EuclideanSpace ℂ κ :=
  EuclideanSpace.diagonalCLM (fun k => ((1+Real.cosh (a k*b))/2 : ℝ))

def centeredRemainder (M : κ → ι → ℂ) (a : κ → ℝ) (x : ι → ℝ) (b : ℝ) :=
  rowAnalysis (fun k i =>
    ((Real.cosh (a k*x i)-(1+Real.cosh (a k*b))/2 : ℝ) : ℂ)*M k i)

/-- The full finite hyperbolic quadratic form equals its actual C and S
row norm squares, with the negative square and every row retained. -/
theorem finite_hyperbolic_form_eq (M : κ → ι → ℂ)
    (a : κ → ℝ) (x : ι → ℝ) (f : EuclideanSpace ℂ ι) :
    (ZeroSamplingQuadratic.form Finset.univ
      (hyperbolicKernel Finset.univ (fun _ : κ => (1 : ℝ)) a x M)
      (fun i => f i)).re =
      ‖cosineAnalysis M a x f‖^2-‖sineAnalysis M a x f‖^2 := by
  have hC (k : κ) : (∑ i, f i*cosineRow a x M k i) =
      cosineAnalysis M a x f k := by
    rw [cosineAnalysis, rowAnalysis_apply]
    apply Finset.sum_congr rfl
    intro i hi
    unfold cosineRow
    ring
  have hS (k : κ) : (∑ i, f i*sineRow a x M k i) =
      sineAnalysis M a x f k := by
    rw [sineAnalysis, rowAnalysis_apply]
    apply Finset.sum_congr rfl
    intro i hi
    unfold sineRow
    ring
  rw [hyperbolic_form_factorization]
  simp only [hC, hS, Complex.ofReal_one, one_mul, Complex.re_sum,
    Complex.sub_re, Complex.ofReal_re, EuclideanSpace.norm_sq_eq,
    Finset.sum_sub_distrib]

/-- The concrete finite centered identity keeps the complete remainder. -/
theorem cosineAnalysis_eq_centered (M : κ → ι → ℂ)
    (a : κ → ℝ) (x : ι → ℝ) (b : ℝ) :
    cosineAnalysis M a x = (centerMultiplier a b).comp (rowAnalysis M) +
      centeredRemainder M a x b := by
  apply rectangleEntry_ext
  intro k i
  change cosineAnalysis M a x (EuclideanSpace.single i 1) k =
    centerMultiplier a b (rowAnalysis M (EuclideanSpace.single i 1)) k +
      centeredRemainder M a x b (EuclideanSpace.single i 1) k
  simp only [cosineAnalysis, centerMultiplier, centeredRemainder,
    rowAnalysis_single, EuclideanSpace.diagonalCLM_apply]
  push_cast
  ring

theorem centeredEvenTerm_entry (M : κ → ι → ℂ)
    (a : κ → ℝ) (x : ι → ℝ) (b : ℝ) (j : ℕ) (k : κ) (i : ι) :
    centeredEvenTerm (EuclideanSpace.diagonalCLM (fun k => (a k : ℂ)))
      (rowAnalysis M) (EuclideanSpace.diagonalCLM (fun i => (x i : ℂ))) b j
        (EuclideanSpace.single i 1) k =
      ((a k^(2*(j+1))*(x i^(2*(j+1))-b^(2*(j+1))/2) /
        (Nat.factorial (2*(j+1)) : ℝ) : ℝ) : ℂ)*M k i := by
  have hcol :
      (EuclideanSpace.diagonalCLM (fun i => (x i : ℂ)))^(2*(j+1)) -
        (b^(2*(j+1))/2) • (1 : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) =
      EuclideanSpace.diagonalCLM
        (fun i => ((x i^(2*(j+1))-b^(2*(j+1))/2 : ℝ) : ℂ)) := by
    ext f i
    change (((EuclideanSpace.diagonalCLM (fun i => (x i : ℂ)))^(2*(j+1))) f) i -
      (b^(2*(j+1))/2 : ℝ) • f i =
      EuclideanSpace.diagonalCLM
        (fun i => ((x i^(2*(j+1))-b^(2*(j+1))/2 : ℝ) : ℂ)) f i
    rw [diagonalCLM_pow_apply, EuclideanSpace.diagonalCLM_apply,
      RCLike.real_smul_eq_coe_smul (K := ℂ)]
    push_cast
    ring_nf
    rfl
  unfold centeredEvenTerm
  rw [hcol, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, EuclideanSpace.diagonalCLM_single,
    map_smul]
  change (Nat.factorial (2*(j+1)) : ℝ)⁻¹ •
    (((EuclideanSpace.diagonalCLM (fun k => (a k : ℂ)))^(2*(j+1)))
      (((x i^(2*(j+1))-b^(2*(j+1))/2 : ℝ) : ℂ) •
        rowAnalysis M (EuclideanSpace.single i 1))) k = _
  rw [map_smul]
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  rw [diagonalCLM_pow_apply, rowAnalysis_single,
    RCLike.real_smul_eq_coe_smul (K := ℂ)]
  push_cast
  ring

/-- The concrete row remainder equals the complete centered operator series.
All row and coordinate bounds are elementary finite-diagonal providers. -/
theorem centeredRemainder_eq_tsum (M : κ → ι → ℂ)
    (a : κ → ℝ) (x : ι → ℝ) (b δ : ℝ)
    (hb : 0 ≤ b) (hδ : 0 ≤ δ) (ha : ∀ k, |a k| ≤ δ) (hx : ∀ i, |x i| ≤ b) :
    centeredRemainder M a x b =
      ∑' j, centeredEvenTerm (EuclideanSpace.diagonalCLM (fun k => (a k : ℂ)))
        (rowAnalysis M) (EuclideanSpace.diagonalCLM (fun i => (x i : ℂ))) b j := by
  have hA : ‖EuclideanSpace.diagonalCLM (fun k => (a k : ℂ))‖ ≤ δ := by
    apply EuclideanSpace.norm_diagonalCLM_le _ _ hδ
    intro k
    simpa only [Complex.norm_real, Real.norm_eq_abs] using ha k
  have hs := (centeredEvenSeries_summable_and_norm_le
    (EuclideanSpace.diagonalCLM (fun k => (a k : ℂ))) (rowAnalysis M)
    (EuclideanSpace.diagonalCLM (fun i => (x i : ℂ))) b δ hb hδ hA
    (fun j => diagonal_even_power_center_norm_le x b hb hx (j+1))).2.1
  apply rectangleEntry_ext
  intro k i
  rw [← rectangleEntryCLM_apply, ← rectangleEntryCLM_apply,
    (rectangleEntryCLM k i).map_tsum hs]
  simp only [rectangleEntryCLM_apply, centeredEvenTerm_entry,
    centeredRemainder, rowAnalysis_single]
  rw [tsum_mul_right, ← Complex.ofReal_tsum, centered_cosh_tsum]

/-- The dimension-free concrete remainder bound discharges the centered
factorization's Q premise, including the sharp one-half factor. -/
theorem centeredRemainder_norm_le (M : κ → ι → ℂ)
    (a : κ → ℝ) (x : ι → ℝ) (b δ : ℝ)
    (hb : 0 ≤ b) (hδ : 0 ≤ δ) (ha : ∀ k, |a k| ≤ δ) (hx : ∀ i, |x i| ≤ b) :
    ‖centeredRemainder M a x b‖ ≤ ((Real.cosh (δ*b)-1)/2)*‖rowAnalysis M‖ := by
  have hA : ‖EuclideanSpace.diagonalCLM (fun k => (a k : ℂ))‖ ≤ δ := by
    apply EuclideanSpace.norm_diagonalCLM_le _ _ hδ
    intro k
    simpa only [Complex.norm_real, Real.norm_eq_abs] using ha k
  rw [centeredRemainder_eq_tsum M a x b δ hb hδ ha hx]
  exact (centeredEvenSeries_summable_and_norm_le
    (EuclideanSpace.diagonalCLM (fun k => (a k : ℂ))) (rowAnalysis M)
    (EuclideanSpace.diagonalCLM (fun i => (x i : ℂ))) b δ hb hδ hA
    (fun j => diagonal_even_power_center_norm_le x b hb hx (j+1))).2.2

theorem centerMultiplier_norm_le (a : κ → ℝ) (b δ : ℝ)
    (hb : 0 ≤ b) (hδ : 0 ≤ δ) (ha : ∀ k, |a k| ≤ δ) :
    ‖centerMultiplier a b‖ ≤ (1+Real.cosh (δ*b))/2 := by
  apply EuclideanSpace.norm_diagonalCLM_le _ _ (by positivity)
  intro k
  have hcosh : Real.cosh (a k*b) ≤ Real.cosh (δ*b) := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_mul, abs_of_nonneg hb, abs_of_nonneg (mul_nonneg hδ hb)]
    exact mul_le_mul_of_nonneg_right (ha k) hb
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ (1+Real.cosh (a k*b))/2)]
  linarith

/-- The concrete centered finite-frame lower estimate. Only the actual
hyperbolic form's lower bound remains as an application input. -/
theorem finite_centered_frame_lower (M : κ → ι → ℂ)
    (a : κ → ℝ) (x : ι → ℝ) (b δ hminus : ℝ)
    (hb : 0 ≤ b) (hδ : 0 ≤ δ) (ha : ∀ k, |a k| ≤ δ) (hx : ∀ i, |x i| ≤ b)
    (hh : 0 ≤ hminus)
    (hform : ∀ f, hminus*‖f‖^2 ≤ ‖cosineAnalysis M a x f‖^2-
      ‖sineAnalysis M a x f‖^2) :
    ∀ f, ((Real.sqrt hminus-((Real.cosh (δ*b)-1)/2)*‖rowAnalysis M‖) /
      ((1+Real.cosh (δ*b))/2))*‖f‖ ≤ ‖rowAnalysis M f‖ := by
  apply norm_lower_of_centered_factorization (rowAnalysis M)
    (cosineAnalysis M a x) (sineAnalysis M a x) (centeredRemainder M a x b)
    (centerMultiplier a b) hminus ((1+Real.cosh (δ*b))/2)
    (((Real.cosh (δ*b)-1)/2)*‖rowAnalysis M‖) hh (by positivity)
    (cosineAnalysis_eq_centered M a x b)
    (centerMultiplier_norm_le a b δ hb hδ ha)
    (centeredRemainder_norm_le M a x b δ hb hδ ha hx) hform

end RiemannResearch.Analysis.CenteredHyperbolicFrames
