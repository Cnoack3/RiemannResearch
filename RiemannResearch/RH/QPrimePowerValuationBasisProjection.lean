/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.PrimeValuationHilbertBasis
import RiemannResearch.RH.QPrimePowerCofactorExpansion
import RiemannResearch.RH.QPrimePowerCofactorResidual
import RiemannResearch.RH.QPrimePowerInfiniteProjection
import RiemannResearch.RH.QPrimePowerValuationProjection
import RiemannResearch.RH.PrimePowerTargetMellin
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.QDivisibilityDensity
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact floor-logarithm projection onto all valuation observables

Source: user-provided valuation/Meixner direction, 20 October 2026,
and FpOrthonormalBasisResearch20261020.md.
Completeness of the actual level basis extends the previously computed
wavelet cancellation to every square-integrable function of v_p.
The mean plus centered valuation is the optimal valuation-only approximant.
Every signed discrepancy and the full cofactor residual remain in the
exact Parseval error identity. The coefficient formula applies in particular
to F_2 and F_3, with F_p always meaning Nat.log p n.

The zero-coefficient theorem applies to any valuation vector orthogonal
to the constant and first mode. It does not assume or establish general
Meixner orthogonality/completeness or legal-closure membership.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace RiemannResearch.RH.PrimePowerTarget
open ZetaTwoHilbert QDivisorHilbert QDivisibilityDensity PrimeValuationBasis

/-- The centered valuation projection belongs to the physical valuation subspace. -/
theorem primePowerProjection_mem_valuationSpace (p : ℕ) (hp : p.Prime) :
    primePowerProjection p hp ∈ valuationSpace p := by
  intro n hn
  rw [primePowerProjection_sequence p n hp hn,
    primePowerProjection_sequence p _ hp (pow_ne_zero _ hp.ne_zero)]
  simp [Nat.factorization_pow, hp.factorization]

/-- The target mean plus centered valuation, as a member of the full valuation space. -/
def valuationTargetProjection (p : ℕ) (hp : p.Prime) : valuationSpace p :=
  ⟨inner ℝ (qTarget p hp.one_lt) qOne • qOne + primePowerProjection p hp,
    (valuationSpace p).add_mem
      ((valuationSpace p).smul_mem _ (qOne_mem_valuationSpace p hp))
      (primePowerProjection_mem_valuationSpace p hp)⟩

/-- The complete cofactor residual is orthogonal to every exact valuation level. -/
theorem primeCofactorResidual_inner_valuationLevel (p k : ℕ) (hp : p.Prime) :
    inner ℝ (primeCofactorResidual p hp) (valuationLevel p k) = 0 := by
  have hone : qDivisor 1 = qOne := by
    apply qSequence_injective
    funext n
    rw [qSequence_qDivisor, qSequence_qOne]
    simp [positiveDivisor, qOneSequence]
  have hz (j : ℕ) : inner ℝ (primeCofactorResidual p hp) (qDivisor (p ^ j)) = 0 := by
    have h := primeCofactorResidual_scaled_divisor p j 1 hp (by norm_num)
    rw [mul_one, hone, primeCofactorResidual_inner_qOne] at h
    exact (mul_eq_zero.mp h).resolve_left
      (pow_ne_zero _ (pow_ne_zero _ (by exact_mod_cast hp.ne_zero)))
  rw [valuationLevel, inner_sub_right, hz, hz, sub_self]

/-- Completeness extends residual orthogonality to every valuation observable. -/
theorem primeCofactorResidual_inner_valuationSpace (p : ℕ) (hp : p.Prime)
    (f : valuationSpace p) :
    inner ℝ (primeCofactorResidual p hp) f.val = 0 := by
  have hs := (valuation_hasSum p hp f).mapL (valuationSpace p).subtypeL
  have hi := hs.mapL (innerSL ℝ (primeCofactorResidual p hp))
  have hz (k : ℕ) :
      inner ℝ (primeCofactorResidual p hp) (valuationUnit p hp k).val = 0 := by
    change inner ℝ _ ((Real.sqrt (valuationMass p k))⁻¹ • valuationLevel p k) = 0
    rw [real_inner_smul_right, primeCofactorResidual_inner_valuationLevel, mul_zero]
  have he : HasSum (fun _ : ℕ => (0 : ℝ))
      (inner ℝ (primeCofactorResidual p hp) f.val) := by
    change HasSum (fun k => inner ℝ (primeCofactorResidual p hp)
      ((qSequence f.val (p ^ k) * Real.sqrt (valuationMass p k)) •
        (valuationUnit p hp k).val)) (inner ℝ (primeCofactorResidual p hp) f.val) at hi
    simpa only [real_inner_smul_right, hz, mul_zero] using hi
  simpa using he.unique (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)

/-- Exact best-approximation identity for every square-integrable valuation-only trial. -/
theorem qTarget_valuation_error_exact (p : ℕ) (hp : p.Prime)
    (f : valuationSpace p) :
    ‖qTarget p hp.one_lt - f.val‖^2 =
      ‖primeCofactorResidual p hp‖^2 +
        ‖(valuationTargetProjection p hp).val - f.val‖^2 := by
  have he : qTarget p hp.one_lt - f.val =
      primeCofactorResidual p hp + ((valuationTargetProjection p hp).val - f.val) := by
    dsimp [primeCofactorResidual, valuationTargetProjection]
    abel
  rw [he, norm_add_sq_real, inner_sub_right,
    primeCofactorResidual_inner_valuationSpace p hp (valuationTargetProjection p hp),
    primeCofactorResidual_inner_valuationSpace p hp f]
  ring

/-- Every valuation mode orthogonal to the constant and linear mode has zero target coefficient. -/
theorem qTarget_inner_valuation_higher (p : ℕ) (hp : p.Prime)
    (f : valuationSpace p)
    (hmean : inner ℝ qOne f.val = 0)
    (hlinear : inner ℝ (primePowerProjectionUnit p hp) f.val = 0) :
    inner ℝ (qTarget p hp.one_lt) f.val = 0 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hscale : ((p : ℝ)^2 - 1) / p ≠ 0 := by
    apply div_ne_zero <;> nlinarith
  rw [primePowerProjectionUnit, real_inner_smul_left] at hlinear
  have hz := (mul_eq_zero.mp hlinear).resolve_left hscale
  have h := primeCofactorResidual_inner_valuationSpace p hp f
  rw [primeCofactorResidual, inner_sub_left, inner_sub_left,
    real_inner_smul_left, hmean, hz] at h
  simpa using h


/-- The optimal valuation-only approximation has affine valuation coordinates. -/
theorem valuationTargetProjection_sequence (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    qSequence (valuationTargetProjection p hp).val n =
      (n.factorization p : ℝ) + inner ℝ (qTarget p hp.one_lt) qOne -
        1 / ((p : ℝ)^2 - 1) := by
  change qSequenceLinear (_ • qOne + primePowerProjection p hp) n = _
  rw [map_add, map_smul]
  change inner ℝ (qTarget p hp.one_lt) qOne * qSequence qOne n +
    qSequence (primePowerProjection p hp) n = _
  rw [qSequence_qOne, primePowerProjection_sequence p n hp hn]
  simp only [qOneSequence, hn, if_false]
  ring

/-- Every normalized level coefficient of the floor-logarithm target is explicit. -/
theorem qTarget_valuation_level_coefficient (p k : ℕ) (hp : p.Prime) :
    inner ℝ (qTarget p hp.one_lt) (valuationUnit p hp k).val =
      ((k : ℝ) + inner ℝ (qTarget p hp.one_lt) qOne -
        1 / ((p : ℝ)^2 - 1)) * Real.sqrt (valuationMass p k) := by
  have h := primeCofactorResidual_inner_valuationSpace p hp (valuationUnit p hp k)
  rw [primeCofactorResidual, inner_sub_left, inner_sub_left, real_inner_smul_left] at h
  have he : inner ℝ (qTarget p hp.one_lt) (valuationUnit p hp k).val =
      inner ℝ (valuationTargetProjection p hp) (valuationUnit p hp k) := by
    change inner ℝ (qTarget p hp.one_lt) (valuationUnit p hp k).val =
      inner ℝ (inner ℝ (qTarget p hp.one_lt) qOne • qOne +
        primePowerProjection p hp) (valuationUnit p hp k).val
    rw [inner_add_left, real_inner_smul_left]
    linarith
  rw [he, valuationUnit_coefficient, valuationTargetProjection_sequence p _ hp
    (pow_ne_zero _ hp.ne_zero)]
  simp [Nat.factorization_pow, hp.factorization]

/-- All signed level discrepancies and the full cofactor residual in one exact identity. -/
theorem qTarget_valuation_signed_parseval (p : ℕ) (hp : p.Prime)
    (f : valuationSpace p) :
    ‖qTarget p hp.one_lt - f.val‖^2 =
      ‖primeCofactorResidual p hp‖^2 +
        ∑' k : ℕ, valuationMass p k *
          ((k : ℝ) + inner ℝ (qTarget p hp.one_lt) qOne -
            1 / ((p : ℝ)^2 - 1) - qSequence f.val (p ^ k))^2 := by
  rw [qTarget_valuation_error_exact p hp f]
  congr 1
  change ‖valuationTargetProjection p hp - f‖^2 = _
  have h := valuation_parseval p hp (valuationTargetProjection p hp - f)
  rw [← h]
  apply tsum_congr
  intro k
  congr 2
  change qSequenceLinear ((valuationTargetProjection p hp).val - f.val) (p ^ k) = _
  rw [map_sub]
  change qSequence (valuationTargetProjection p hp).val (p ^ k) -
    qSequence f.val (p ^ k) = _
  rw [valuationTargetProjection_sequence p _ hp (pow_ne_zero _ hp.ne_zero)]
  simp [Nat.factorization_pow, hp.factorization]

end RiemannResearch.RH.PrimePowerTarget
