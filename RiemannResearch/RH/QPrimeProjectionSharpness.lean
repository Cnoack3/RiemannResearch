/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimeResampling
import RiemannResearch.RH.QDivisorLegality
import RiemannResearch.RH.QDivisibilityHilbertMoments
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Prime.Basic
import RiemannResearch.RH.QPrimeProjectionPoincare
import RiemannResearch.RH.QPrimeResamplingParity
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ArithmeticCumulativeBasic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic.NormNum

/-!
# A nonzero equality witness for the actual prime Poincare inequality

The centered dyadic residue is affected by exactly the prime-two coordinate.
Its complete countable prime energy equals its variance. Thus the constant
one in the Poincare bound is sharp, for actual Q functions.
-/

noncomputable section
open scoped ENNReal
namespace RiemannResearch.RH.QPrimeResampling
open ZetaTwoHilbert ArithmeticCumulative

def dyadicCenteredAtom : QHilbert := qResidue 2 - (3 / 8 : ℝ) • qOne

@[simp] theorem C_two_dyadicCenteredAtom : C 2 dyadicCenteredAtom = 0 := by
  simp [dyadicCenteredAtom, map_sub, map_smul, C_two_qResidue_two, C_qOne]

@[simp] theorem C_odd_dyadicCenteredAtom (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    C p dyadicCenteredAtom = dyadicCenteredAtom := by
  simp only [dyadicCenteredAtom, map_sub, map_smul,
    C_odd_qResidue_two p hp hp2, C_qOne p hp.ne_zero]

theorem dyadicCenteredAtom_mean_zero : inner ℝ qOne dyadicCenteredAtom = 0 := by
  have h := C_preserves_mean 2 (by norm_num) dyadicCenteredAtom
  simpa only [C_two_dyadicCenteredAtom, inner_zero_right] using h.symm

theorem dyadicCenteredAtom_ne_zero : dyadicCenteredAtom ≠ 0 := by
  intro he
  have h := congrArg (fun f : QHilbert => qSequence f 2) he
  change qSequenceLinear (qResidue 2 - (3 / 8 : ℝ) • qOne) 2 = qSequenceLinear 0 2 at h
  rw [map_sub, map_smul, map_zero] at h
  change qSequence (qResidue 2) 2 - (3 / 8 : ℝ) * qSequence qOne 2 = 0 at h
  rw [qSequence_qResidue, qSequence_qOne] at h
  norm_num [residueFraction, qOneSequence] at h

/-- Equality holds at a genuine nonzero mean-zero Hilbert vector. -/
theorem primeProjectionEnergy_dyadicCenteredAtom :
    primeProjectionEnergy dyadicCenteredAtom = ENNReal.ofReal (‖dyadicCenteredAtom‖ ^ 2) := by
  unfold primeProjectionEnergy
  rw [tsum_eq_single 2]
  · rw [if_pos Nat.prime_two, C_two_dyadicCenteredAtom, sub_zero]
  · intro p hp2
    by_cases hp : p.Prime
    · simp [hp, C_odd_dyadicCenteredAtom p hp hp2]
    · simp [hp]

/-- Exact nondegenerate saturation of the countable-prime gap-one bound. -/
theorem prime_projection_poincare_equality_witness :
    ∃ f : QHilbert, f ≠ 0 ∧ inner ℝ qOne f = 0 ∧
      primeProjectionEnergy f = ENNReal.ofReal (‖f‖ ^ 2) :=
  ⟨dyadicCenteredAtom, dyadicCenteredAtom_ne_zero, dyadicCenteredAtom_mean_zero,
    primeProjectionEnergy_dyadicCenteredAtom⟩

open QDivisibilityDensity QDivisorLegality

/-- Exact variance of the centered actual dyadic residue atom. -/
theorem dyadicCenteredAtom_norm_sq : ‖dyadicCenteredAtom‖ ^ 2 = (3 / 64 : ℝ) := by
  have hm : inner ℝ qOne (qResidue 2) = (3 / 8 : ℝ) := by
    have h := C_preserves_mean 2 (by norm_num) (qResidue 2)
    rw [C_two_qResidue_two, real_inner_smul_right, real_inner_self_eq_norm_sq,
      qOne_norm_sq, mul_one] at h
    exact h.symm
  have hg := qDivisor_norm_sq 2 (by norm_num)
  rw [qDivisor_two_eq, norm_sub_sq_real, real_inner_smul_right, norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs, qOne_norm_sq, hm] at hg
  have he := norm_sub_sq_real (qResidue 2) ((3 / 8 : ℝ) • qOne)
  rw [real_inner_smul_right, real_inner_comm qOne (qResidue 2), hm,
    norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, qOne_norm_sq] at he
  change ‖qResidue 2 - (3 / 8 : ℝ) • qOne‖ ^ 2 = _
  norm_num at hg
  nlinarith only [hg, he]

end RiemannResearch.RH.QPrimeResampling
