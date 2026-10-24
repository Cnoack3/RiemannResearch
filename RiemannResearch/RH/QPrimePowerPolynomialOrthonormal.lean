/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimePowerMonomialLift
import RiemannResearch.RH.QPrimePowerValuationBasisProjection
import RiemannResearch.RH.QPrimePowerInfiniteProjection
import RiemannResearch.RH.QPrimePowerWaveletCoefficients
import RiemannResearch.RH.QPrimePowerHilbertFrame
import RiemannResearch.RH.QPrimePowerCofactorResidual
import RiemannResearch.RH.PrimeValuationHilbertBasis
import RiemannResearch.RH.PrimePowerTargetMellin
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module
import Lean.Elab.Tactic.Omega

/-!
# All-order orthonormal valuation-polynomial innovations

Source: user-provided valuation/Meixner research direction and
FpOrthonormalBasisResearch20261020.md. The construction uses Mathlib's
GramSchmidtOrtho normalization and span-preservation theorems.

The exact wavelet coefficients prove that the monomial lifts are linearly
independent: any finite dependence gives a real polynomial with infinitely
many distinct natural-number roots. Thus Gram-Schmidt has no zero innovations
at any order. Each mode lies in the finite span of raw lifts up to its index.
The constant together with these modes is orthonormal for the actual Q law.
The first mode is the positive normalized valuation; all later target
coefficients vanish. The signed finite-trial identity retains the full
cofactor residual and every mean, linear, and higher-mode discrepancy.

We do not identify every mode with a classical closed Meixner formula or
assert density of this polynomial span in the full valuation space.
Polynomial/tensor completeness and legal F_2/F_3 saturation remain open.
F_p is Nat.log p n, not v_p(n); no legal membership is inferred.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace RiemannResearch.RH.PrimePowerTarget
open ZetaTwoHilbert QDivisorHilbert PrimeValuationBasis InnerProductSpace
/-- Every finite dependence would give a polynomial vanishing at all natural numbers. -/
theorem primePowerMonomialLift_linearIndependent (p : ℕ) (hp : p.Prime) :
    LinearIndependent ℝ (primePowerMonomialLift p hp) := by
  classical
  rw [linearIndependent_iff']
  intro s a ha i hi
  let P : Polynomial ℝ := ∑ m ∈ s, Polynomial.C (a m) * Polynomial.X^m
  have hc (k : ℕ) : inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1)) ≠ 0 := by
    rw [qTarget_inner_primePowerFrame_succ]
    have hpos : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hd : (0 : ℝ) < (p : ℝ)^2-1 := by nlinarith
    exact ne_of_gt (by positivity)
  have he (k : ℕ) : P.eval (k : ℝ) = 0 := by
    have h := congrArg (fun f => inner ℝ (primePowerFrame p hp (k+1)) f) ha
    simp only [inner_sum, real_inner_smul_right, primePowerMonomialLift_inner_frame,
      inner_zero_right] at h
    have hs : (∑ m ∈ s, a m * (k : ℝ)^m) *
        inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1)) = 0 := by
      simpa only [Finset.sum_mul, mul_assoc] using h
    simpa [P, Polynomial.eval_finsetSum] using (mul_eq_zero.mp hs).resolve_right (hc k)
  have hP : P = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.infinite_range_of_injective
      (Nat.cast_injective : Function.Injective (fun k : ℕ => (k : ℝ)))).mono
    rintro x ⟨k, rfl⟩
    exact he k
  have hcoeff := congrArg (fun Q : Polynomial ℝ => Q.coeff i) hP
  simpa [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, hi] using hcoeff

/-- Normalized Gram-Schmidt innovations of the raw lifts, indexed from the linear mode. -/
def valuationPolynomialMode (p : ℕ) (hp : p.Prime) : ℕ → QHilbert :=
  gramSchmidtNormed ℝ (primePowerMonomialLift p hp)

/-- All orders are nonzero and orthonormal in the actual Q Hilbert space. -/
theorem valuationPolynomialMode_orthonormal (p : ℕ) (hp : p.Prime) :
    Orthonormal ℝ (valuationPolynomialMode p hp) :=
  gramSchmidtNormed_orthonormal (primePowerMonomialLift_linearIndependent p hp)

/-- The full algebraic span is preserved; no density assertion is made. -/
theorem valuationPolynomialMode_span (p : ℕ) (hp : p.Prime) :
    Submodule.span ℝ (Set.range (valuationPolynomialMode p hp)) =
      Submodule.span ℝ (Set.range (primePowerMonomialLift p hp)) := by
  rw [valuationPolynomialMode, span_gramSchmidtNormed_range, span_gramSchmidt]

/-- Every normalized mode is a physical valuation-only observable. -/
theorem valuationPolynomialMode_mem (p : ℕ) (hp : p.Prime) (j : ℕ) :
    valuationPolynomialMode p hp j ∈ valuationSpace p := by
  have hs : Submodule.span ℝ (Set.range (valuationPolynomialMode p hp)) ≤ valuationSpace p := by
    rw [valuationPolynomialMode_span]
    exact Submodule.span_le.mpr (by rintro x ⟨m, rfl⟩; exact primePowerMonomialLift_mem p hp m)
  exact hs (Submodule.subset_span ⟨j, rfl⟩)

/-- Every normalized mode has actual-Q mean zero. -/
theorem valuationPolynomialMode_centered (p : ℕ) (hp : p.Prime) (j : ℕ) :
    inner ℝ qOne (valuationPolynomialMode p hp j) = 0 := by
  have hs : Submodule.span ℝ (Set.range (valuationPolynomialMode p hp)) ≤
      (innerSL ℝ qOne).ker := by
    rw [valuationPolynomialMode_span]
    exact Submodule.span_le.mpr (by rintro x ⟨m, rfl⟩; exact primePowerMonomialLift_centered p hp m)
  exact hs (Submodule.subset_span ⟨j, rfl⟩)

/-- Each finite initial span is preserved exactly. -/
theorem valuationPolynomialMode_span_Iic (p : ℕ) (hp : p.Prime) (N : ℕ) :
    Submodule.span ℝ (valuationPolynomialMode p hp '' Set.Iic N) =
      Submodule.span ℝ (primePowerMonomialLift p hp '' Set.Iic N) := by
  rw [valuationPolynomialMode, span_gramSchmidtNormed, span_gramSchmidt_Iic]

/-- Every later innovation is orthogonal to the entire linear valuation projection. -/
theorem valuationPolynomialMode_inner_projection (p : ℕ) (hp : p.Prime)
    (j : ℕ) (hj : j ≠ 0) :
    inner ℝ (valuationPolynomialMode p hp j) (primePowerProjection p hp) = 0 := by
  have he : primePowerMonomialLift p hp 0 = primePowerProjection p hp := by
    simp [primePowerMonomialLift, primePowerProjection]
  have hm : primePowerProjection p hp ∈
      Submodule.span ℝ (valuationPolynomialMode p hp '' Set.Iic 0) := by
    rw [valuationPolynomialMode_span_Iic, ← he]
    exact Submodule.subset_span ⟨0, by simp, rfl⟩
  have hs : Submodule.span ℝ (valuationPolynomialMode p hp '' Set.Iic 0) ≤
      (innerSL ℝ (valuationPolynomialMode p hp j)).ker := by
    apply Submodule.span_le.mpr
    rintro x ⟨k, hk, rfl⟩
    have hk0 : k = 0 := by simpa using hk
    subst k
    exact (valuationPolynomialMode_orthonormal p hp).2 hj
  exact hs hm

/-- All higher normalized innovations have exactly zero floor-log target coefficient. -/
theorem qTarget_inner_valuationPolynomialMode_succ (p : ℕ) (hp : p.Prime) (j : ℕ) :
    inner ℝ (qTarget p hp.one_lt) (valuationPolynomialMode p hp (j+1)) = 0 := by
  apply qTarget_inner_valuation_higher p hp
    ⟨_, valuationPolynomialMode_mem p hp (j+1)⟩
    (valuationPolynomialMode_centered p hp (j+1))
  change inner ℝ (primePowerProjectionUnit p hp) (valuationPolynomialMode p hp (j+1)) = 0
  rw [primePowerProjectionUnit, real_inner_smul_left]
  have h := valuationPolynomialMode_inner_projection p hp (j+1) (by omega)
  rw [show inner ℝ (primePowerProjection p hp) (valuationPolynomialMode p hp (j+1)) =
    inner ℝ (valuationPolynomialMode p hp (j+1)) (primePowerProjection p hp) from real_inner_comm _ _,
    h, mul_zero]


/-- The first innovation has the established positive linear-valuation orientation. -/
theorem valuationPolynomialMode_zero (p : ℕ) (hp : p.Prime) :
    valuationPolynomialMode p hp 0 = primePowerProjectionUnit p hp := by
  have he : primePowerMonomialLift p hp 0 = primePowerProjection p hp := by
    simp [primePowerMonomialLift, primePowerProjection]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hd : (0 : ℝ) < (p : ℝ)^2 - 1 := by nlinarith
  have hn : ‖primePowerProjection p hp‖ = (p : ℝ) / ((p : ℝ)^2-1) := by
    have h := primePowerProjection_norm_sq p hp
    have hr : (0 : ℝ) < (p : ℝ) / ((p : ℝ)^2-1) := by positivity
    have hs : ((p : ℝ) / ((p : ℝ)^2-1))^2 = (p : ℝ)^2 / ((p : ℝ)^2-1)^2 := by
      rw [div_pow]
    nlinarith [norm_nonneg (primePowerProjection p hp)]
  change ‖gramSchmidt ℝ (primePowerMonomialLift p hp) (⊥ : ℕ)‖⁻¹ •
    gramSchmidt ℝ (primePowerMonomialLift p hp) (⊥ : ℕ) = _
  rw [gramSchmidt_bot]
  change ‖primePowerMonomialLift p hp 0‖⁻¹ • primePowerMonomialLift p hp 0 = _
  rw [he, hn, primePowerProjectionUnit, inv_div]

/-- The complete sequence of floor-log coefficients in the centered family. -/
theorem qTarget_valuationPolynomialMode_coefficient (p : ℕ) (hp : p.Prime) (j : ℕ) :
    inner ℝ (qTarget p hp.one_lt) (valuationPolynomialMode p hp j) =
      if j = 0 then (p : ℝ) / ((p : ℝ)^2-1) else 0 := by
  cases j with
  | zero => simp [valuationPolynomialMode_zero, qTarget_inner_primePowerProjectionUnit]
  | succ j => simp [qTarget_inner_valuationPolynomialMode_succ]

/-- The j-th mode uses only raw lifts of orders at most j. -/
theorem valuationPolynomialMode_mem_finite_span (p : ℕ) (hp : p.Prime) (j : ℕ) :
    valuationPolynomialMode p hp j ∈
      Submodule.span ℝ (primePowerMonomialLift p hp '' Set.Iic j) := by
  rw [← valuationPolynomialMode_span_Iic]
  exact Submodule.subset_span ⟨j, by simp, rfl⟩

/-- Every signed trial discrepancy and the full cofactor residual are retained. -/
theorem qTarget_valuationPolynomial_signed_error (p : ℕ) (hp : p.Prime)
    (s : Finset ℕ) (a : ℕ → ℝ) (mu b : ℝ) :
    ‖qTarget p hp.one_lt - (mu • qOne + b • valuationPolynomialMode p hp 0 +
      ∑ j ∈ s, a j • valuationPolynomialMode p hp (j+1))‖^2 =
      ‖primeCofactorResidual p hp‖^2 +
      (inner ℝ (qTarget p hp.one_lt) qOne - mu)^2 +
      ((p : ℝ) / ((p : ℝ)^2-1) - b)^2 + ∑ j ∈ s, (a j)^2 := by
  let g := ∑ j ∈ s, a j • valuationPolynomialMode p hp (j+1)
  let d := inner ℝ (qTarget p hp.one_lt) qOne - mu
  let c := (p : ℝ) / ((p : ℝ)^2-1) - b
  have ho : Orthonormal ℝ (fun j => valuationPolynomialMode p hp (j+1)) :=
    (valuationPolynomialMode_orthonormal p hp).comp (fun j : ℕ => j+1) (by
      intro i j h; exact Nat.add_right_cancel h)
  have hg : ‖g‖^2 = ∑ j ∈ s, (a j)^2 := by
    rw [← real_inner_self_eq_norm_sq]
    simpa [g, pow_two] using ho.inner_sum a a s
  have h1g : inner ℝ qOne g = 0 := by
    simp [g, inner_sum, real_inner_smul_right, valuationPolynomialMode_centered]
  have h0g : inner ℝ (valuationPolynomialMode p hp 0) g = 0 := by
    have hz (j : ℕ) : inner ℝ (valuationPolynomialMode p hp 0)
        (valuationPolynomialMode p hp (j+1)) = 0 :=
      (valuationPolynomialMode_orthonormal p hp).2 (by omega)
    simp [g, inner_sum, real_inner_smul_right, hz]
  have h10 := valuationPolynomialMode_centered p hp 0
  have hnorm0 := (valuationPolynomialMode_orthonormal p hp).1 0
  have hnorm1 : ‖qOne‖ = 1 := by
    simpa only [primePowerFrame_zero] using (primePowerFrame_orthonormal p hp).1 0
  have hP : primePowerProjection p hp =
      ((p : ℝ) / ((p : ℝ)^2-1)) • valuationPolynomialMode p hp 0 := by
    rw [valuationPolynomialMode_zero, primePowerProjectionUnit, smul_smul]
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hp0 : (p : ℝ) ≠ 0 := by linarith
    have hd : (p : ℝ)^2-1 ≠ 0 := by nlinarith
    field_simp
    simp
  have hmem : mu • qOne + b • valuationPolynomialMode p hp 0 + g ∈ valuationSpace p := by
    apply (valuationSpace p).add_mem
    · exact (valuationSpace p).add_mem
        ((valuationSpace p).smul_mem _ (qOne_mem_valuationSpace p hp))
        ((valuationSpace p).smul_mem _ (valuationPolynomialMode_mem p hp 0))
    · exact (valuationSpace p).sum_mem (fun j hj =>
        (valuationSpace p).smul_mem _ (valuationPolynomialMode_mem p hp (j+1)))
  have h := qTarget_valuation_error_exact p hp ⟨_, hmem⟩
  have he : (valuationTargetProjection p hp).val -
      (mu • qOne + b • valuationPolynomialMode p hp 0 + g) =
      (d • qOne + c • valuationPolynomialMode p hp 0) - g := by
    change inner ℝ (qTarget p hp.one_lt) qOne • qOne + primePowerProjection p hp -
      (mu • qOne + b • valuationPolynomialMode p hp 0 + g) = _
    rw [hP]
    dsimp [d,c]
    module
  have hn : ‖(d • qOne + c • valuationPolynomialMode p hp 0) - g‖^2 =
      d^2 + c^2 + ∑ j ∈ s, (a j)^2 := by
    rw [norm_sub_sq_real, norm_add_sq_real]
    simp only [inner_add_left, real_inner_smul_left, real_inner_smul_right,
      h1g, h0g, h10, norm_smul, hnorm1, hnorm0, hg,
      Real.norm_eq_abs, mul_one, mul_zero, add_zero, sub_zero, sq_abs]
  rw [he, hn] at h
  change _ = ‖primeCofactorResidual p hp‖^2 + d^2 + c^2 + ∑ j ∈ s, (a j)^2
  change ‖qTarget p hp.one_lt - (mu • qOne + b • valuationPolynomialMode p hp 0 + g)‖^2 = _
  linarith


/-- Include the constant before all centered polynomial innovations. -/
def valuationPolynomialFrame (p : ℕ) (hp : p.Prime) : ℕ → QHilbert
  | 0 => qOne
  | j+1 => valuationPolynomialMode p hp j

/-- Actual-Q orthonormality includes the constant and every nonzero innovation. -/
theorem valuationPolynomialFrame_orthonormal (p : ℕ) (hp : p.Prime) :
    Orthonormal ℝ (valuationPolynomialFrame p hp) := by
  constructor
  · intro i
    cases i with
    | zero =>
      simpa only [valuationPolynomialFrame, primePowerFrame_zero] using
        (primePowerFrame_orthonormal p hp).1 0
    | succ i => exact (valuationPolynomialMode_orthonormal p hp).1 i
  · intro i j hij
    cases i with
    | zero =>
      cases j with
      | zero => exact (hij rfl).elim
      | succ j => exact valuationPolynomialMode_centered p hp j
    | succ i =>
      cases j with
      | zero =>
        change inner ℝ (valuationPolynomialMode p hp i) qOne = 0
        rw [real_inner_comm]
        exact valuationPolynomialMode_centered p hp i
      | succ j => exact (valuationPolynomialMode_orthonormal p hp).2 (by omega)

end RiemannResearch.RH.PrimePowerTarget
