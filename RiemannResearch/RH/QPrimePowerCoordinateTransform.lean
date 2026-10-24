/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimePowerWaveletCompleteness
import RiemannResearch.RH.PrimeValuationHilbertBasis
import RiemannResearch.RH.QPrimePowerHilbertFrame
import RiemannResearch.RH.QDivisorHilbertBasis
import RiemannResearch.RH.QDivisibilityDensity
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Data.Nat.Factorization.Basic
/-!
# Exact level-to-wavelet coordinates for prime valuations

Source: user-provided valuation/Meixner research direction; see
FpOrthonormalBasisResearch20261020.md. The two previously constructed complete
bases give an explicit invertible isometry of coefficient spaces. The physical
entries are computed from adjacent divisibility tails. This is infrastructure
for comparing future polynomial modes, not a proof of Meixner completeness
or of floor-logarithm membership in the legal squarefree closure.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace RiemannResearch.RH.PrimeValuationBasis
open ZetaTwoHilbert QDivisibilityDensity QDivisorHilbert

/-- Signed change-of-basis matrix, with wavelet rows and exact-level columns. -/
def valuationChangeKernel (p : ℕ) (hp : p.Prime) (k j : ℕ) : ℝ :=
  inner ℝ (valuationWavelet p hp k) (valuationUnit p hp j)

/-- Physical evaluation formula for every matrix entry. -/
theorem valuationChangeKernel_eval (p : ℕ) (hp : p.Prime) (k j : ℕ) :
    valuationChangeKernel p hp k j =
      qSequence (primePowerFrame p hp k) (p ^ j) * Real.sqrt (valuationMass p j) := by
  exact valuationUnit_coefficient p hp (valuationWavelet p hp k) j

/-- The constant row consists of square roots of exact Zipf masses. -/
theorem valuationChangeKernel_zero (p : ℕ) (hp : p.Prime) (j : ℕ) :
    valuationChangeKernel p hp 0 j = Real.sqrt (valuationMass p j) := by
  rw [valuationChangeKernel_eval, primePowerFrame_zero, qSequence_qOne]
  simp [qOneSequence, hp.ne_zero]

/-- Explicit signed threshold formula for every nonconstant row. -/
theorem valuationChangeKernel_succ (p : ℕ) (hp : p.Prime) (k j : ℕ) :
    valuationChangeKernel p hp (k+1) j =
    (Real.sqrt (qJordanTwo (p^(k+1))))⁻¹ *
      (((p : ℝ)^(k+1))^2 * (if k+1 ≤ j then 1 else 0) -
       ((p : ℝ)^k)^2 * (if k ≤ j then 1 else 0)) *
       Real.sqrt (valuationMass p j) := by
  rw [valuationChangeKernel_eval]
  unfold primePowerFrame normalizedDivisorWavelet
  change qSequenceLinear (_ • divisorWavelet (p^(k+1))) (p^j) * _ = _
  rw [map_smul]
  change (Real.sqrt (qJordanTwo (p^(k+1))))⁻¹ *
    qSequence (divisorWavelet (p^(k+1))) (p^j) * _ = _
  rw [divisorWavelet_prime_pow_succ p k hp]
  change _ * qSequenceLinear (_ - _) (p^j) * _ = _
  simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  change _ * (_ * qSequence (qDivisor (p^(k+1))) (p^j) -
    _ * qSequence (qDivisor (p^k)) (p^j)) * _ = _
  simp only [qSequence_qDivisor, positiveDivisor, pow_ne_zero _ hp.ne_zero, if_false,
    hp.pow_dvd_iff_le_factorization (pow_ne_zero _ hp.ne_zero)]
  simp [Nat.factorization_pow, hp.factorization]

/-- Complete row orthogonality, including convergence of the full series. -/
theorem valuationChangeKernel_rows (p : ℕ) (hp : p.Prime) (k l : ℕ) :
    HasSum (fun j => valuationChangeKernel p hp k j * valuationChangeKernel p hp l j)
      (if k = l then 1 else 0) := by
  have h := (valuationHilbertBasis p hp).hasSum_inner_mul_inner
    (valuationWavelet p hp k) (valuationWavelet p hp l)
  simpa only [valuationHilbertBasis_apply, real_inner_comm (valuationUnit p hp _),
    valuationChangeKernel,
    orthonormal_iff_ite.mp (valuationWavelet_orthonormal p hp)] using h

/-- Complete column orthogonality, including convergence of the full series. -/
theorem valuationChangeKernel_columns (p : ℕ) (hp : p.Prime) (j l : ℕ) :
    HasSum (fun k => valuationChangeKernel p hp k j * valuationChangeKernel p hp k l)
      (if j = l then 1 else 0) := by
  have h := (valuationWaveletBasis p hp).hasSum_inner_mul_inner
    (valuationUnit p hp j) (valuationUnit p hp l)
  simpa only [valuationWaveletBasis_apply, real_inner_comm (valuationUnit p hp j),
    valuationChangeKernel,
    orthonormal_iff_ite.mp (valuationUnit_orthonormal p hp)] using h

/-- Convergent forward coefficient transform for any valuation observable. -/
theorem valuation_level_to_wavelet (p : ℕ) (hp : p.Prime)
    (f : valuationSpace p) (k : ℕ) :
    HasSum (fun j => (qSequence f.val (p^j) * Real.sqrt (valuationMass p j)) *
      valuationChangeKernel p hp k j) (inner ℝ f (valuationWavelet p hp k)) := by
  have hc (j : ℕ) : inner ℝ (valuationUnit p hp j) (valuationWavelet p hp k) =
      valuationChangeKernel p hp k j := real_inner_comm _ _
  simpa only [valuationHilbertBasis_apply, hc, valuationUnit_coefficient] using
    (valuationHilbertBasis p hp).hasSum_inner_mul_inner f (valuationWavelet p hp k)

/-- Convergent inverse coefficient transform for any valuation observable. -/
theorem valuation_wavelet_to_level (p : ℕ) (hp : p.Prime)
    (f : valuationSpace p) (j : ℕ) :
    HasSum (fun k => inner ℝ f (valuationWavelet p hp k) *
      valuationChangeKernel p hp k j)
      (qSequence f.val (p^j) * Real.sqrt (valuationMass p j)) := by
  simpa only [valuationWaveletBasis_apply, valuationChangeKernel,
    valuationUnit_coefficient] using
    (valuationWaveletBasis p hp).hasSum_inner_mul_inner f (valuationUnit p hp j)

/-- Invertible norm-preserving transform on all square-summable real coefficients. -/
def valuationCoordinateEquiv (p : ℕ) (hp : p.Prime) :
    lp (fun _ : ℕ => ℝ) 2 ≃ₗᵢ[ℝ] lp (fun _ : ℕ => ℝ) 2 :=
  (valuationHilbertBasis p hp).repr.symm.trans (valuationWaveletBasis p hp).repr

/-- The isometry is realized by the explicit infinite matrix series. -/
theorem valuationCoordinateEquiv_apply (p : ℕ) (hp : p.Prime)
    (a : lp (fun _ : ℕ => ℝ) 2) (k : ℕ) :
    HasSum (fun j => a j * valuationChangeKernel p hp k j)
      (valuationCoordinateEquiv p hp a k) := by
  have h := valuation_level_to_wavelet p hp ((valuationHilbertBasis p hp).repr.symm a) k
  have hc (j : ℕ) :
      qSequence ((valuationHilbertBasis p hp).repr.symm a).val (p^j) *
        Real.sqrt (valuationMass p j) = a j := by
    rw [← valuationUnit_coefficient p hp ((valuationHilbertBasis p hp).repr.symm a) j]
    have he := congrArg (fun b : lp (fun _ : ℕ => ℝ) 2 => b j)
      ((valuationHilbertBasis p hp).repr.apply_symm_apply a)
    simpa only [HilbertBasis.repr_apply_apply, valuationHilbertBasis_apply,
      real_inner_comm] using he
  simpa only [hc, valuationCoordinateEquiv, LinearIsometryEquiv.trans_apply,
    HilbertBasis.repr_apply_apply, valuationWaveletBasis_apply, real_inner_comm] using h

end RiemannResearch.RH.PrimeValuationBasis
