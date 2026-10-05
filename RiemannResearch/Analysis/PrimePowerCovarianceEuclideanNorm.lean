/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.PrimePowerCovarianceConjugation
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Euclidean norm of the full integer prime-power covariance

The actual symmetric matrix retains every integer frequency 1,...,d,
including composite frequencies. On a divisibility pair with ratio k its
entry is Lambda(k)/sqrt(k); the diagonal vanishes exactly. Its continuous
operator acts on the Euclidean space indexed by `Finset.Ioc 0 d`.

The existing exact weighted Schur row identity and upper pairing estimate
give `norm <= log d + log 4 + 4`. The same actual Mertens provider's lower
bound, applied to the Schur vector n^(-1/2), gives the complete quadratic
identity and `log d - 2 <= norm` for d >= 1. Hence the main operator has
logarithmic growth with leading constant 1. Real scaling keeps the signed
Landau normalization in the operator definition.

Source for the arithmetic statement and weighted Schur direction:
user-provided manuscript `Prime_Phases_Agenda_Proof_Attempts.tex`, Theorem
`growing-phase-gram`, and the proved sibling modules
`PrimePowerCovarianceRowBudget` and `PrimePowerCovarianceConjugation`.
The lower estimate reuses `Mertens.E₁Λ.ge` from the project's complete
elementary Mertens port. Source for the operator identification and proof
strategy: Mathlib's star algebra equivalence `Matrix.toEuclideanCLM` and
Rayleigh norm characterization, revision
51e6992efd06126df61a496bebf8f49482a4e129:
https://github.com/leanprover-community/mathlib4/blob/51e6992efd06126df61a496bebf8f49482a4e129/Mathlib/Analysis/CStarAlgebra/Matrix.lean
https://github.com/leanprover-community/mathlib4/blob/51e6992efd06126df61a496bebf8f49482a4e129/Mathlib/Analysis/InnerProductSpace/Rayleigh.lean

These are unconditional arithmetic operator estimates. Their analytic
Landau zero-sum specialization is a separate provider obligation.
-/

open scoped BigOperators InnerProductSpace

namespace RiemannResearch.Fourier

/-- Every integer frequency from 1 through d is retained. -/
abbrev integerFrequencyIndex (d : ℕ) := ↥(Finset.Ioc 0 d)

/-- The actual Lambda(k)/sqrt(k) covariance matrix, including all composite
frequencies and every divisibility pair. -/
noncomputable def primePowerMainMatrix (d : ℕ) :
    Matrix (integerFrequencyIndex d) (integerFrequencyIndex d) ℂ :=
  fun n m => (primePowerCovarianceSymmetricEntry n.val m.val : ℂ)

/-- The arithmetic main matrix in the Euclidean operator norm. -/
noncomputable def primePowerMainOperator (d : ℕ) :
    EuclideanSpace ℂ (integerFrequencyIndex d) →L[ℂ]
      EuclideanSpace ℂ (integerFrequencyIndex d) :=
  Matrix.toEuclideanCLM (n := integerFrequencyIndex d) (𝕜 := ℂ) (primePowerMainMatrix d)

private noncomputable def extendFrequencyCoefficients (d : ℕ)
    (x : EuclideanSpace ℂ (integerFrequencyIndex d)) : ℕ → ℂ :=
  fun n => if hn : n ∈ Finset.Ioc 0 d then x ⟨n, hn⟩ else 0

private theorem extendFrequencyCoefficients_apply (d : ℕ)
    (x : EuclideanSpace ℂ (integerFrequencyIndex d))
    (n : integerFrequencyIndex d) :
    extendFrequencyCoefficients d x n.val = x n := by
  simp only [extendFrequencyCoefficients, dif_pos n.property]

theorem primePowerMainMatrix_selfAdjoint (d : ℕ) :
    IsSelfAdjoint (primePowerMainMatrix d) := by
  change star (primePowerMainMatrix d) = primePowerMainMatrix d
  ext n m
  change star (primePowerCovarianceSymmetricEntry m.val n.val : ℂ) =
    (primePowerCovarianceSymmetricEntry n.val m.val : ℂ)
  simp only [RCLike.star_def, Complex.conj_ofReal]
  exact congrArg (fun r : ℝ => (r : ℂ))
    (primePowerCovarianceSymmetricEntry_symm m.val n.val
      (Finset.mem_Ioc.mp m.property).1 (Finset.mem_Ioc.mp n.property).1)

theorem primePowerMainOperator_isSymmetric (d : ℕ) :
    (primePowerMainOperator d).IsSymmetric := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
  change star (Matrix.toEuclideanCLM (n := integerFrequencyIndex d) (𝕜 := ℂ)
      (primePowerMainMatrix d)) =
    Matrix.toEuclideanCLM (n := integerFrequencyIndex d) (𝕜 := ℂ) (primePowerMainMatrix d)
  rw [← map_star, (primePowerMainMatrix_selfAdjoint d).star_eq]

/-- The quadratic form is exactly the already proved finite pairing. -/
theorem primePowerMainOperator_inner_eq_pairing (d : ℕ)
    (x : EuclideanSpace ℂ (integerFrequencyIndex d)) :
    inner ℂ x (primePowerMainOperator d x) =
      finiteGramErrorPairing (Finset.Ioc 0 d) (extendFrequencyCoefficients d x)
        (fun n m => (primePowerCovarianceSymmetricEntry n m : ℂ)) := by
  have happ (n : integerFrequencyIndex d) :
      primePowerMainOperator d x n =
        ∑ m : integerFrequencyIndex d, primePowerMainMatrix d n m * x m := by
    rfl
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, happ, Finset.sum_mul]
  unfold finiteGramErrorPairing
  simp_rw [← (Finset.Ioc 0 d).sum_coe_sort]
  simp only [extendFrequencyCoefficients_apply]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro m hm
  change (primePowerCovarianceSymmetricEntry n.val m.val : ℂ) * x m *
      star (x n) = star (x n) *
        (primePowerCovarianceSymmetricEntry n.val m.val : ℂ) * x m
  ring

theorem primePowerMainOperator_inner_norm_le (d : ℕ)
    (x : EuclideanSpace ℂ (integerFrequencyIndex d)) :
    ‖inner ℂ x (primePowerMainOperator d x)‖ ≤
      (Real.log d + Real.log 4 + 4) * ‖x‖ ^ 2 := by
  have h := primePowerCovarianceSymmetricEntry_pairing_bound d
    (extendFrequencyCoefficients d x)
  have henergy : (∑ n ∈ Finset.Ioc 0 d,
      ‖extendFrequencyCoefficients d x n‖ ^ 2) = ‖x‖ ^ 2 := by
    rw [← (Finset.Ioc 0 d).sum_coe_sort]
    simp only [extendFrequencyCoefficients_apply]
    exact (EuclideanSpace.norm_sq_eq x).symm
  rw [primePowerMainOperator_inner_eq_pairing, ← henergy]
  exact h

/-- A Rayleigh bridge specialized to the actual full arithmetic matrix.
The Schur constant is O(log d), rather than a power of the dictionary size. -/
theorem primePowerMainOperator_norm_le (d : ℕ) :
    ‖primePowerMainOperator d‖ ≤ Real.log d + Real.log 4 + 4 := by
  have hdlog : 0 ≤ Real.log (d : ℝ) := by
    by_cases hd : d = 0
    · simp [hd]
    · apply Real.log_nonneg
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd
  have hconstant : 0 ≤ Real.log (d : ℝ) + Real.log 4 + 4 := by
    have hfour : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
    positivity
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _
    (primePowerMainOperator_isSymmetric d)]
  apply ciSup_le
  intro x
  by_cases hx : x = 0
  · simp only [hx, ContinuousLinearMap.rayleighQuotient_apply_zero, abs_zero]
    exact hconstant
  have hx2 : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) 2
  change |(primePowerMainOperator d).reApplyInnerSelf x / ‖x‖ ^ 2| ≤ _
  rw [abs_div, abs_sq, div_le_iff₀ hx2]
  change |(inner ℂ (primePowerMainOperator d x) x).re| ≤ _
  have hsymre : (inner ℂ (primePowerMainOperator d x) x).re =
      (inner ℂ x (primePowerMainOperator d x)).re := by
    simpa using (inner_re_symm (𝕜 := ℂ) (primePowerMainOperator d x) x)
  rw [hsymre]
  exact (Complex.abs_re_le_norm _).trans
    (primePowerMainOperator_inner_norm_le d x)

/-- Exact real scaling preserves the sign in the operator definition;
only its norm estimate uses the absolute value. This specializes to
r=-T/(2*pi*Ncount), with the original zero-count normalizer retained. -/
theorem real_smul_primePowerMainOperator_norm_le (d : ℕ) (r : ℝ) :
    ‖r • primePowerMainOperator d‖ ≤
      |r| * (Real.log d + Real.log 4 + 4) := by
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (primePowerMainOperator_norm_le d) (abs_nonneg r)

/-- The lower row budget is the other side of the same actual Mertens
provider used by the existing upper row theorem. -/
theorem primePowerCovarianceRowBudget_ge (N n : ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) :
    Real.log N - 2 ≤ primePowerCovarianceRowBudget N n := by
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le hnpos (by exact_mod_cast hnN)
  have hratio : (1 : ℝ) ≤ (N : ℝ) / (n : ℝ) :=
    (one_le_div hnpos).mpr (by exact_mod_cast hnN)
  have hm := Mertens.E₁Λ.ge hratio
  change -2 ≤ (∑ q ∈ Finset.Ioc 0 ⌊(N : ℝ) / n⌋₊,
    ArithmeticFunction.vonMangoldt q / (q : ℝ)) - Real.log ((N : ℝ) / n) at hm
  rw [Nat.floor_div_natCast, Nat.floor_natCast] at hm
  rw [Real.log_div hNpos.ne' hnpos.ne'] at hm
  rw [primePowerCovarianceRowBudget_eq]
  linarith

/-- The actual positive Schur direction in the same Euclidean space. -/
noncomputable def primePowerSchurVector (d : ℕ) :
    EuclideanSpace ℂ (integerFrequencyIndex d) :=
  WithLp.toLp 2 (fun n => (integerFrequencySchurWeight n.val : ℂ))

private theorem primePowerSchurVector_apply (d : ℕ) (n : integerFrequencyIndex d) :
    primePowerSchurVector d n = (integerFrequencySchurWeight n.val : ℂ) := rfl

/-- Exact action on the Schur vector, reusing the complete proved weighted
row identity. No divisor or multiple is dropped. -/
theorem primePowerMainOperator_schurVector_apply (d : ℕ)
    (n : integerFrequencyIndex d) :
    primePowerMainOperator d (primePowerSchurVector d) n =
      ((integerFrequencySchurWeight n.val *
        primePowerCovarianceRowBudget d n.val : ℝ) : ℂ) := by
  have hn := Finset.mem_Ioc.mp n.property
  have hr := primePowerCovarianceSymmetricEntry_weighted_row d n.val hn.1 hn.2
  simp_rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (primePowerCovarianceSymmetricEntry_nonneg n.val _)] at hr
  have hrsub :
      (∑ m : integerFrequencyIndex d, primePowerCovarianceSymmetricEntry n.val m.val *
        integerFrequencySchurWeight m.val) =
      integerFrequencySchurWeight n.val * primePowerCovarianceRowBudget d n.val := by
    change (∑ m : ↥(Finset.Ioc 0 d),
      primePowerCovarianceSymmetricEntry n.val m.val * integerFrequencySchurWeight m.val) = _
    exact (Finset.sum_coe_sort (Finset.Ioc 0 d) (fun m : ℕ =>
      primePowerCovarianceSymmetricEntry n.val m * integerFrequencySchurWeight m)).trans hr
  change (∑ m : integerFrequencyIndex d,
      (primePowerCovarianceSymmetricEntry n.val m.val : ℂ) *
        (integerFrequencySchurWeight m.val : ℂ)) = _
  exact_mod_cast hrsub

/-- Complete exact quadratic identity for the Schur direction. The
logarithmic lower norm estimate follows from this identity and Mertens. -/
theorem primePowerMainOperator_schurVector_qform (d : ℕ) :
    (primePowerMainOperator d).reApplyInnerSelf (primePowerSchurVector d) =
      ∑ n : integerFrequencyIndex d, integerFrequencySchurWeight n.val ^ 2 *
        primePowerCovarianceRowBudget d n.val := by
  change (inner ℂ (primePowerMainOperator d (primePowerSchurVector d))
    (primePowerSchurVector d)).re = _
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, primePowerMainOperator_schurVector_apply,
    primePowerSchurVector_apply, Complex.conj_ofReal]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem primePowerSchurVector_norm_sq (d : ℕ) :
    ‖primePowerSchurVector d‖ ^ 2 =
      ∑ n : integerFrequencyIndex d, integerFrequencySchurWeight n.val ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [primePowerSchurVector_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem primePowerSchurVector_ne_zero (d : ℕ) (hd : 1 ≤ d) :
    primePowerSchurVector d ≠ 0 := by
  let n : integerFrequencyIndex d := ⟨1, Finset.mem_Ioc.mpr ⟨by decide, hd⟩⟩
  intro hzero
  have hz := congrArg (fun y : EuclideanSpace ℂ (integerFrequencyIndex d) => y n) hzero
  have hone : (1 : ℂ) = 0 := by
    simpa [primePowerSchurVector, integerFrequencySchurWeight, n] using hz
  exact one_ne_zero hone

/-- The full integer-frequency main operator grows logarithmically.
Together with the upper bound, this gives log d + O(1). In particular,
the operator does not decompose into uniformly bounded prime blocks. -/
theorem primePowerMainOperator_norm_ge (d : ℕ) (hd : 1 ≤ d) :
    Real.log d - 2 ≤ ‖primePowerMainOperator d‖ := by
  let w := primePowerSchurVector d
  have hlo : (Real.log d - 2) * ‖w‖ ^ 2 ≤
      (primePowerMainOperator d).reApplyInnerSelf w := by
    change (Real.log d - 2) * ‖primePowerSchurVector d‖ ^ 2 ≤ _
    rw [primePowerSchurVector_norm_sq, primePowerMainOperator_schurVector_qform]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hi := Finset.mem_Ioc.mp n.property
    have hb := primePowerCovarianceRowBudget_ge d n.val hi.1 hi.2
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left hb (sq_nonneg (integerFrequencySchurWeight n.val))
  have hw : w ≠ 0 := primePowerSchurVector_ne_zero d hd
  have hw2 : 0 < ‖w‖ ^ 2 := pow_pos (norm_pos_iff.mpr hw) 2
  have hr : Real.log d - 2 ≤ (primePowerMainOperator d).rayleighQuotient w :=
    (le_div_iff₀ hw2).mpr hlo
  exact hr.trans ((le_abs_self _).trans
    ((primePowerMainOperator d).rayleighQuotient_le_norm w))

end RiemannResearch.Fourier
