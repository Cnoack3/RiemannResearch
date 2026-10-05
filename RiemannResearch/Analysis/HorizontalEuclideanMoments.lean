/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs

/-!
# Euclidean finite phase-moment centering

The Rayleigh norm characterization proves the actual continuous-operator
centering bound from quadratic-form inequalities. Finite nonnegative rank-one
sums give exact weighted domination and the centered even-moment norm provider.
The original copy set and normalizer are retained, including repetitions.

Source for the proof strategy: Mathlib's proved Rayleigh characterization and
positive rank-one operators, revision 51e6992efd06126df61a496bebf8f49482a4e129:
https://github.com/leanprover-community/mathlib4/blob/51e6992efd06126df61a496bebf8f49482a4e129/Mathlib/Analysis/InnerProductSpace/Rayleigh.lean
and the sibling Positive.lean. The actual-zero consumer is
Analysis/ActualZeroPhaseMoments.lean. This module supplies moment centering and
positive-operator norm comparison.
The full actual correction identity is proved in ActualZeroPhaseOperators;
analytic distribution estimates remain separate obligations.
-/

open scoped InnerProductSpace BigOperators ComplexOrder

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem qform_sub (S T : E →L[ℂ] E) (x : E) :
    (S - T).reApplyInnerSelf x = S.reApplyInnerSelf x - T.reApplyInnerSelf x := by
  change (inner ℂ (S x - T x) x).re =
    (inner ℂ (S x) x).re - (inner ℂ (T x) x).re
  simp only [inner_sub_left, Complex.sub_re]

theorem qform_real_smul (r : ℝ) (T : E →L[ℂ] E) (x : E) :
    (r • T).reApplyInnerSelf x = r * T.reApplyInnerSelf x := by
  change (inner ℂ (r • T x) x).re = r * (inner ℂ (T x) x).re
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_real_left]
  simp [Complex.real_smul]

theorem qform_one (x : E) :
    (1 : E →L[ℂ] E).reApplyInnerSelf x = ‖x‖ ^ 2 := by
  change (inner ℂ x x).re = ‖x‖ ^ 2
  exact inner_self_eq_norm_sq (𝕜 := ℂ) x

/-- Rayleigh norm characterization discharges centering from actual quadratic
form bounds. It does not require finite dimension or a spectral hypothesis. -/
theorem norm_center_le_of_qform_bounds (T : E →L[ℂ] E) (b : ℝ)
    (hb : 0 ≤ b) (hT : T.IsSymmetric)
    (hlo : ∀ x, 0 ≤ T.reApplyInnerSelf x)
    (hhi : ∀ x, T.reApplyInnerSelf x ≤ b * ‖x‖ ^ 2) :
    ‖T - (b / 2) • (1 : E →L[ℂ] E)‖ ≤ b / 2 := by
  have hs : (T - (b / 2) • (1 : E →L[ℂ] E)).IsSymmetric := by
    intro x y
    change inner ℂ (T x - (b / 2) • x) y = inner ℂ x (T y - (b / 2) • y)
    simp only [inner_sub_left, inner_sub_right,
      RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_real_left, inner_smul_real_right]
    have hh := hT x y
    change inner ℂ (T x) y = inner ℂ x (T y) at hh
    simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ)] using
      congrArg (fun z : ℂ => z - (b / 2) • inner ℂ x y) hh
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ hs]
  apply ciSup_le
  intro x
  by_cases hx : x = 0
  · simp only [hx, ContinuousLinearMap.rayleighQuotient_apply_zero, abs_zero]
    positivity
  have hx2 : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) 2
  change |(T - (b / 2) • (1 : E →L[ℂ] E)).reApplyInnerSelf x / ‖x‖ ^ 2| ≤ b / 2
  rw [abs_div, abs_sq, div_le_iff₀ hx2,
    qform_sub, qform_real_smul, qform_one, abs_le]
  constructor <;> nlinarith [hlo x, hhi x]

/-- The Loewner statement 0 <= T <= bI, expressed with actual positivity. -/
theorem norm_center_le_of_positive (T : E →L[ℂ] E) (b : ℝ)
    (hb : 0 ≤ b) (hT : T.IsPositive)
    (hupper : (b • (1 : E →L[ℂ] E) - T).IsPositive) :
    ‖T - (b / 2) • (1 : E →L[ℂ] E)‖ ≤ b / 2 := by
  apply norm_center_le_of_qform_bounds T b hb hT.isSymmetric hT.2
  intro x
  have hx := hupper.2 x
  rw [qform_sub, qform_real_smul, qform_one] at hx
  linarith

/-- Norm upper bound for any actual operator's quadratic form. -/
theorem qform_le_norm (T : E →L[ℂ] E) (x : E) :
    T.reApplyInnerSelf x ≤ ‖T‖ * ‖x‖ ^ 2 := by
  by_cases hx : x = 0
  · simp [hx, ContinuousLinearMap.reApplyInnerSelf_apply]
  have hx2 : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) 2
  have h := (le_abs_self (T.rayleighQuotient x)).trans (T.rayleighQuotient_le_norm x)
  exact (div_le_iff₀ hx2).mp h

/-- A positive operator's norm is bounded by an actual quadratic-form upper
bound. This is a direct consequence of the proved Rayleigh characterization. -/
theorem norm_le_of_positive_qform_upper_bound
    (S : E →L[ℂ] E) (b : ℝ) (hb : 0 ≤ b) (hS : S.IsPositive)
    (hhi : ∀ x, S.reApplyInnerSelf x ≤ b * ‖x‖ ^ 2) :
    ‖S‖ ≤ b := by
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ hS.isSymmetric]
  apply ciSup_le
  intro x
  by_cases hx : x = 0
  · simp only [hx, ContinuousLinearMap.rayleighQuotient_apply_zero, abs_zero]
    exact hb
  have hx2 : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) 2
  change |S.reApplyInnerSelf x / ‖x‖ ^ 2| ≤ b
  rw [abs_div, abs_sq, abs_of_nonneg (hS.2 x), div_le_iff₀ hx2]
  exact hhi x

/-- Positive domination never increases operator norm. The upper operator
need not carry a separate positivity premise: the signed difference supplies
the required actual quadratic-form comparison. -/
theorem norm_le_of_positive_domination
    (S T : E →L[ℂ] E) (hS : S.IsPositive)
    (hupper : (T - S).IsPositive) :
    ‖S‖ ≤ ‖T‖ := by
  apply norm_le_of_positive_qform_upper_bound S ‖T‖ (norm_nonneg _) hS
  intro x
  have hh := hupper.2 x
  rw [qform_sub] at hh
  exact (by linarith : S.reApplyInnerSelf x ≤ T.reApplyInnerSelf x).trans
    (qform_le_norm T x)

/-- A genuine symmetric CLM's absolute real quadratic-form bound controls
its actual operator norm. This also covers the zero-dimensional case. -/
theorem norm_le_of_abs_re_inner_le (A : E →L[ℂ] E) (B : ℝ) (hB : 0 ≤ B)
    (hA : A.IsSymmetric)
    (hform : ∀ f : E, |(inner ℂ f (A f)).re| ≤ B*‖f‖^2) :
    ‖A‖ ≤ B := by
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ hA]
  apply ciSup_le
  intro f
  by_cases hf : f = 0
  · simp only [hf, ContinuousLinearMap.rayleighQuotient_apply_zero, abs_zero]
    exact hB
  have hf2 : 0 < ‖f‖^2 := pow_pos (norm_pos_iff.mpr hf) 2
  change |A.reApplyInnerSelf f/‖f‖^2| ≤ B
  rw [abs_div, abs_sq, div_le_iff₀ hf2]
  change |(inner ℂ (A f) f).re| ≤ B*‖f‖^2
  have he := hA f f
  change inner ℂ (A f) f = inner ℂ f (A f) at he
  rw [he]
  exact hform f

/-- Both endpoints of a symmetric operator's actual quadratic-form interval
give the centered operator norm, including in the zero-dimensional case. -/
theorem norm_sub_center_le_of_re_inner_interval (A : E →L[ℂ] E)
    (lo hi : ℝ) (hlohi : lo ≤ hi) (hA : A.IsSymmetric)
    (hlo : ∀ f : E, lo*‖f‖^2 ≤ (inner ℂ f (A f)).re)
    (hhi : ∀ f : E, (inner ℂ f (A f)).re ≤ hi*‖f‖^2) :
    ‖A-((lo+hi)/2) • (1 : E →L[ℂ] E)‖ ≤ (hi-lo)/2 := by
  let c : ℝ := (lo+hi)/2
  have hS : (A-c • (1 : E →L[ℂ] E)).IsSymmetric := by
    intro x y
    change inner ℂ (A x-c • x) y = inner ℂ x (A y-c • y)
    simp only [inner_sub_left, inner_sub_right,
      RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_real_left,
      inner_smul_real_right]
    have hh := hA x y
    change inner ℂ (A x) y = inner ℂ x (A y) at hh
    simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ)] using
      congrArg (fun z : ℂ => z-c • inner ℂ x y) hh
  apply norm_le_of_abs_re_inner_le _ _ (by linarith) hS
  intro f
  have hq : (inner ℂ f ((A-c • (1 : E →L[ℂ] E)) f)).re =
      (inner ℂ f (A f)).re-c*‖f‖^2 := by
    have hsf := hS f f
    change inner ℂ ((A-c • (1 : E →L[ℂ] E)) f) f =
      inner ℂ f ((A-c • (1 : E →L[ℂ] E)) f) at hsf
    rw [← hsf]
    change (A-c • (1 : E →L[ℂ] E)).reApplyInnerSelf f = _
    rw [qform_sub, qform_real_smul, qform_one]
    change (inner ℂ (A f) f).re-c*‖f‖^2 = _
    have haf := hA f f
    change inner ℂ (A f) f = inner ℂ f (A f) at haf
    rw [haf]
  rw [hq, abs_le]
  dsimp [c]
  constructor <;> nlinarith [hlo f, hhi f]

end ContinuousLinearMap

namespace RiemannResearch.Analysis.HorizontalEuclideanMoments

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable {ι : Type*}

/-- Complete finite-copy Gram with the stated normalization. -/
noncomputable def copyGram (s : Finset ι) (κ : ℝ) (v : ι → E) : E →L[ℂ] E :=
  κ • ∑ i ∈ s, InnerProductSpace.rankOne ℂ (v i) (v i)

/-- Copy weights retain the complete original index set. In particular the
good-copy cutoff is represented by zero weights, not a changed normalizer. -/
noncomputable def weightedCopyGram (s : Finset ι) (κ : ℝ)
    (w : ι → ℝ) (v : ι → E) : E →L[ℂ] E :=
  κ • ∑ i ∈ s, w i • InnerProductSpace.rankOne ℂ (v i) (v i)

theorem weightedCopyGram_positive (s : Finset ι) (κ : ℝ)
    (w : ι → ℝ) (v : ι → E) (hκ : 0 ≤ κ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (weightedCopyGram s κ w v).IsPositive := by
  have hs : (∑ i ∈ s, w i • InnerProductSpace.rankOne ℂ (v i) (v i)).IsPositive := by
    apply ContinuousLinearMap.isPositive_sum
    intro i hi
    have hp := InnerProductSpace.isPositive_rankOne_self (𝕜 := ℂ) (v i)
    simpa only [RCLike.real_smul_eq_coe_smul (K := ℂ)] using
      hp.smul_of_nonneg ((RCLike.ofReal_nonneg (K := ℂ)).2 (hw i hi))
  unfold weightedCopyGram
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact hs.smul_of_nonneg ((RCLike.ofReal_nonneg (K := ℂ)).2 hκ)

/-- Exact finite weighted domination identity. -/
theorem weightedCopyGram_domination_identity (s : Finset ι) (κ c : ℝ)
    (w : ι → ℝ) (v : ι → E) :
    c • copyGram s κ v - weightedCopyGram s κ w v =
      weightedCopyGram s κ (fun i => c - w i) v := by
  unfold copyGram weightedCopyGram
  simp only [Finset.smul_sum, smul_smul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← sub_smul]
  congr 1
  ring

/-- The complete finite rank-one weighted moment supplies the exact centered
norm premise consumed by HorizontalPhaseBootstrap.evenCorrection_summable_and_norm_le. -/
theorem weightedCopyGram_center_norm_le (s : Finset ι) (κ c : ℝ)
    (w : ι → ℝ) (v : ι → E) (hκ : 0 ≤ κ) (hc : 0 ≤ c)
    (hw : ∀ i ∈ s, 0 ≤ w i ∧ w i ≤ c) :
    ‖weightedCopyGram s κ w v -
      (c * ‖copyGram s κ v‖ / 2) • (1 : E →L[ℂ] E)‖ ≤
      c * ‖copyGram s κ v‖ / 2 := by
  have hp := weightedCopyGram_positive s κ w v hκ (fun i hi => (hw i hi).1)
  have hd : (c • copyGram s κ v - weightedCopyGram s κ w v).IsPositive := by
    rw [weightedCopyGram_domination_identity]
    exact weightedCopyGram_positive s κ (fun i => c - w i) v hκ
      (fun i hi => sub_nonneg.mpr (hw i hi).2)
  apply norm_center_le_of_qform_bounds _ (c * ‖copyGram s κ v‖)
    (mul_nonneg hc (norm_nonneg _)) hp.isSymmetric hp.2
  intro x
  have hh := hd.2 x
  rw [qform_sub, qform_real_smul] at hh
  calc
    _ ≤ c * (copyGram s κ v).reApplyInnerSelf x := by linarith
    _ ≤ c * (‖copyGram s κ v‖ * ‖x‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (qform_le_norm _ _) hc
    _ = _ := by ring

noncomputable def goodEvenWeight (δ : ℝ) (k : ℕ) (ρ : ℂ) : ℝ :=
  if |ρ.re - 1 / 2| ≤ δ then (ρ.re - 1 / 2) ^ (2 * k) else 0

theorem goodEvenWeight_bounds (δ : ℝ) (hδ : 0 ≤ δ) (k : ℕ) (ρ : ℂ) :
    0 ≤ goodEvenWeight δ k ρ ∧ goodEvenWeight δ k ρ ≤ δ ^ (2 * k) := by
  unfold goodEvenWeight
  split_ifs with h
  · have hs : (ρ.re - 1 / 2) ^ 2 ≤ δ ^ 2 := by
      have := (sq_le_sq₀ (abs_nonneg (ρ.re - 1 / 2)) hδ).2 h
      simpa only [sq_abs] using this
    constructor
    · rw [pow_mul]
      exact pow_nonneg (sq_nonneg _) k
    · rw [pow_mul, pow_mul]
      exact pow_le_pow_left₀ (sq_nonneg _) hs k
  · constructor
    · rfl
    · positivity

/-- All integer frequencies 1,...,d, in the actual Euclidean Hilbert norm. -/
noncomputable def copyPhaseVector (d : ℕ) (ρ : ℂ) : EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 fun n : Fin d =>
    Complex.exp (((ρ.im * Real.log ((n.val + 1 : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)

/-- Full normalized multiplicity Gram of arbitrary finite complex copies.
Repeated complex values or repeated ordinates remain separate indices. -/
noncomputable def finitePhaseGram (d : ℕ) (s : Finset ι) (ρ : ι → ℂ) :
    EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d) :=
  copyGram s (s.card : ℝ)⁻¹ (fun i => copyPhaseVector d (ρ i))

/-- Actual finite even horizontal moment, normalized by all original copies. -/
noncomputable def finiteGoodMoment (d : ℕ) (s : Finset ι) (ρ : ι → ℂ)
    (δ : ℝ) (k : ℕ) :
    EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d) :=
  weightedCopyGram s (s.card : ℝ)⁻¹
    (fun i => goodEvenWeight δ k (ρ i)) (fun i => copyPhaseVector d (ρ i))

/-- Exact actual finite Euclidean moment-norm provider. A condition saying
every ρ i is a zeta zero is unnecessary: positivity and cutoff domination hold
for every finite family and therefore specialize without an analytic premise. -/
theorem finiteGoodMoment_center_norm_le (d : ℕ) (s : Finset ι) (ρ : ι → ℂ)
    (δ : ℝ) (hδ : 0 ≤ δ) (k : ℕ) :
    ‖finiteGoodMoment d s ρ δ k -
      (δ ^ (2 * k) * ‖finitePhaseGram d s ρ‖ / 2) •
        (1 : EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d))‖ ≤
      δ ^ (2 * k) * ‖finitePhaseGram d s ρ‖ / 2 := by
  unfold finiteGoodMoment finitePhaseGram
  apply weightedCopyGram_center_norm_le
  · positivity
  · positivity
  · intro i hi
    exact goodEvenWeight_bounds δ hδ k (ρ i)

/-- Domination by the zeroth masked moment retains the cutoff exactly. -/
theorem goodEvenWeight_le_zeroth
    (δ : ℝ) (hδ : 0 ≤ δ) (k : ℕ) (ρ : ℂ) :
    goodEvenWeight δ k ρ ≤
      δ ^ (2 * k) * goodEvenWeight δ 0 ρ := by
  by_cases h : |ρ.re - 1 / 2| ≤ δ
  · simpa only [goodEvenWeight, if_pos h, Nat.mul_zero, pow_zero, mul_one] using
      (goodEvenWeight_bounds δ hδ k ρ).2
  · simp only [goodEvenWeight, if_neg h, mul_zero, le_refl]

end RiemannResearch.Analysis.HorizontalEuclideanMoments
