/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimePowerCofactorResidual
import RiemannResearch.RH.QPrimePowerInfiniteProjection
import RiemannResearch.RH.QPrimePowerHilbertFrame
import RiemannResearch.RH.QPrimePowerMixedWavelet
import RiemannResearch.RH.QDivisibilityHilbertMoments
import RiemannResearch.RH.QDivisibilityDensity
import RiemannResearch.RH.QDivisorWaveletDensity
import RiemannResearch.RH.QDivisorHilbertBasis
import RiemannResearch.RH.QResidueMoments
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.PrimePowerTargetMellin
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Tactic.Module
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Complete coprime-conductor expansion of the floor-logarithm residual

Source: user-provided valuation-basis research direction, 20 October 2026,
and FpOrthonormalBasisResearch20261020.md. We use the already proved complete
ambient arithmetic divisor Hilbert basis, not an unproved Meixner basis.

The prime-free cofactor residual is invariant under multiplication by p-powers.
Exact dilation moments then cancel every wavelet whose conductor is divisible
by p. At nonconstant p-coprime conductors its coefficients equal those of F_p.
Completeness reconstructs the residual from precisely those coefficients.
The full target expansion, exact infinite energy, and signed trial-error
identities retain every mode; no residual vanishing or legal membership is
assumed. F_p remains Nat.log p n, not the valuation. Higher Meixner completeness
and membership of qTarget 2 and qTarget 3 in closureWithConstants remain open.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace RiemannResearch.RH.PrimePowerTarget
open ZetaTwoHilbert ZetaTwoProbability QDivisibilityDensity QDivisorHilbert

/-- The p-invariant residual has an exact scaled divisibility moment. -/
theorem primeCofactorResidual_scaled_divisor (p k d : ℕ) (hp : p.Prime)
    (hd : 0 < d) :
    ((p : ℝ) ^ k) ^ 2 * inner ℝ (primeCofactorResidual p hp) (qDivisor (p ^ k * d)) =
      inner ℝ (primeCofactorResidual p hp) (qDivisor d) := by
  have he : inversePowerMean 0
      (fun n => qSequence (primeCofactorResidual p hp) (p ^ k * d*n)) =
      inversePowerMean 0 (fun n => qSequence (primeCofactorResidual p hp) (d * n)) := by
    unfold inversePowerMean
    apply tsum_congr
    intro n
    dsimp only
    rw [mul_assoc, primeCofactorResidual_sequence_mul_power p k (d * (n + 1)) hp
      (mul_ne_zero (ne_of_gt hd) (Nat.succ_ne_zero n))]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  rw [inner_qDivisor_eq_dilation _ _ (mul_pos (pow_pos hp.pos _) hd),
    he, inner_qDivisor_eq_dilation _ d hd, Nat.cast_mul, Nat.cast_pow]
  field_simp

/-- Every conductor divisible by p has zero residual coefficient, including pure powers. -/
theorem primeCofactorResidual_inner_wavelet_of_dvd (p t : ℕ) (hp : p.Prime)
    (ht : t ≠ 0) (hpt : p ∣ t) :
    inner ℝ (primeCofactorResidual p hp) (divisorWavelet t) = 0 := by
  have hv := hp.factorization_pos_of_dvd ht hpt
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hv)
  let r := t / p ^ t.factorization p
  have hpr : p.Coprime r := Nat.coprime_ordCompl hp ht
  have he : t = p ^ (k + 1) * r := by
    simpa only [r, hk] using (Nat.ordProj_mul_ordCompl_eq_self t p).symm
  rw [he, divisorWavelet_primePower_mul p k r hp hpr]
  unfold mixedPrimePowerWavelet
  rw [inner_sum]
  apply Finset.sum_eq_zero
  intro d hd
  rw [real_inner_smul_right, inner_sub_right, real_inner_smul_right,
    real_inner_smul_right, primeCofactorResidual_scaled_divisor p (k + 1) d hp
      (Nat.pos_of_mem_divisors hd),
    primeCofactorResidual_scaled_divisor p k d hp (Nat.pos_of_mem_divisors hd),
    sub_self, mul_zero]

/-- The same-prime projection is orthogonal to every p-coprime basis wavelet. -/
theorem primePowerProjection_inner_coprime_wavelet (p : ℕ) (hp : p.Prime)
    (t : ℕ+) (ht : p.Coprime (t : ℕ)) :
    inner ℝ (primePowerProjection p hp) (normalizedDivisorWavelet t) = 0 := by
  have hi (k : ℕ) : inner ℝ (normalizedDivisorWavelet t)
      (primePowerFrame p hp (k + 1)) = 0 := by
    apply normalizedDivisorWavelet_orthonormal.2
    intro he
    have hn : (t : ℕ) = p ^ (k + 1) := congrArg (fun x : ℕ+ => (x : ℕ)) he
    apply (hp.coprime_iff_not_dvd.mp ht)
    rw [hn, pow_succ]
    exact dvd_mul_left p (p ^ k)
  rw [real_inner_comm]
  change (innerSL ℝ (normalizedDivisorWavelet t)) (∑' k : ℕ, _) = 0
  rw [(innerSL ℝ (normalizedDivisorWavelet t)).map_tsum
    (primePower_nonconstant_summable p hp)]
  change (∑' k : ℕ, inner ℝ (normalizedDivisorWavelet t)
    (inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k + 1)) •
      primePowerFrame p hp (k + 1))) = 0
  simp [real_inner_smul_right, hi]

/-- The complete coefficient support of the centered cofactor residual. -/
theorem primeCofactorResidual_inner_basis (p : ℕ) (hp : p.Prime) (t : ℕ+) :
    inner ℝ (primeCofactorResidual p hp) (normalizedDivisorWavelet t) =
      if t ≠ 1 ∧ p.Coprime (t : ℕ) then
        inner ℝ (qTarget p hp.one_lt) (normalizedDivisorWavelet t) else 0 := by
  by_cases h1 : t = 1
  · subst t
    have hone : normalizedDivisorWavelet (1 : ℕ+) = qOne := by
      change (Real.sqrt (qJordanTwo 1))⁻¹ • divisorWavelet 1 = qOne
      simp [divisorWavelet_one, qJordanTwo]
    simp [hone, primeCofactorResidual_inner_qOne]
  · by_cases hc : p.Coprime (t : ℕ)
    · rw [if_pos ⟨h1, hc⟩, primeCofactorResidual, inner_sub_left, inner_sub_left,
        real_inner_smul_left, primePowerProjection_inner_coprime_wavelet p hp t hc]
      have hone : inner ℝ qOne (normalizedDivisorWavelet t) = 0 := by
        unfold normalizedDivisorWavelet
        rw [real_inner_smul_right, qOne_divisorWavelet_inner, if_neg h1, mul_zero]
      rw [hone]
      ring
    · rw [if_neg (by simp [hc])]
      unfold normalizedDivisorWavelet
      rw [real_inner_smul_right,
        primeCofactorResidual_inner_wavelet_of_dvd p (t : ℕ) hp (ne_of_gt t.pos)
          (by simpa only [hp.coprime_iff_not_dvd, not_not] using hc), mul_zero]

/-- The coprime-conductor series converges unconditionally to the full residual. -/
theorem primeCofactorResidual_hasSum_coprime (p : ℕ) (hp : p.Prime) :
    HasSum (fun t : ℕ+ =>
      (if t ≠ 1 ∧ p.Coprime (t : ℕ) then
        inner ℝ (qTarget p hp.one_lt) (normalizedDivisorWavelet t) else 0) •
        normalizedDivisorWavelet t) (primeCofactorResidual p hp) := by
  have h := divisorHilbertBasis.hasSum_repr (primeCofactorResidual p hp)
  have hc (t : ℕ+) : inner ℝ (normalizedDivisorWavelet t) (primeCofactorResidual p hp) =
      if t ≠ 1 ∧ p.Coprime (t : ℕ) then
        inner ℝ (qTarget p hp.one_lt) (normalizedDivisorWavelet t) else 0 := by
    rw [real_inner_comm]
    exact primeCofactorResidual_inner_basis p hp t
  simpa only [HilbertBasis.repr_apply_apply, divisorHilbertBasis_apply, hc] using h

/-- All residual energy is retained in the infinite coprime coefficient sum. -/
theorem primeCofactorResidual_parseval_coprime (p : ℕ) (hp : p.Prime) :
    (∑' t : ℕ+, if t ≠ 1 ∧ p.Coprime (t : ℕ) then
      (inner ℝ (qTarget p hp.one_lt) (normalizedDivisorWavelet t)) ^ 2 else 0) =
      ‖primeCofactorResidual p hp‖ ^ 2 := by
  have h := divisorHilbertBasis.tsum_inner_mul_inner
    (primeCofactorResidual p hp) (primeCofactorResidual p hp)
  have he (t : ℕ+) : inner ℝ (primeCofactorResidual p hp) (normalizedDivisorWavelet t) *
      inner ℝ (normalizedDivisorWavelet t) (primeCofactorResidual p hp) =
      if t ≠ 1 ∧ p.Coprime (t : ℕ) then
        (inner ℝ (qTarget p hp.one_lt) (normalizedDivisorWavelet t)) ^ 2 else 0 := by
    have hc : inner ℝ (normalizedDivisorWavelet t) (primeCofactorResidual p hp) =
        inner ℝ (primeCofactorResidual p hp) (normalizedDivisorWavelet t) :=
      real_inner_comm _ _
    rw [hc, primeCofactorResidual_inner_basis]
    split_ifs <;> simp [pow_two]
  simpa only [divisorHilbertBasis_apply, he, real_inner_self_eq_norm_sq] using h

/-- Reconstruct the floor-log target from its mean, valuation projection, and cofactor modes. -/
theorem qTarget_eq_mean_projection_coprime_tsum (p : ℕ) (hp : p.Prime) :
    qTarget p hp.one_lt =
      inner ℝ (qTarget p hp.one_lt) qOne • qOne + primePowerProjection p hp +
        ∑' t : ℕ+, (if t ≠ 1 ∧ p.Coprime (t : ℕ) then
          inner ℝ (qTarget p hp.one_lt) (normalizedDivisorWavelet t) else 0) •
          normalizedDivisorWavelet t := by
  rw [(primeCofactorResidual_hasSum_coprime p hp).tsum_eq, primeCofactorResidual]
  module

/-- Complete target Parseval identity with the residual expressed as its full coefficient sum. -/
theorem qTarget_coprime_energy_exact (p : ℕ) (hp : p.Prime) :
    ‖qTarget p hp.one_lt‖ ^ 2 =
      (inner ℝ (qTarget p hp.one_lt) qOne) ^ 2 + (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1) ^ 2 +
        ∑' t : ℕ+, if t ≠ 1 ∧ p.Coprime (t : ℕ) then
          (inner ℝ (qTarget p hp.one_lt) (normalizedDivisorWavelet t)) ^ 2 else 0 := by
  rw [primeCofactorResidual_parseval_coprime]
  exact qTarget_primePower_centered_energy_exact p hp

/-- Exact full target error for arbitrary signed trial data, including every off-support mode. -/
theorem qTarget_coprime_expansion_error_exact (p : ℕ) (hp : p.Prime) (f : QHilbert) :
    (∑' t : ℕ+,
      ((if t ≠ 1 ∧ p.Coprime (t : ℕ) then
        inner ℝ (qTarget p hp.one_lt) (normalizedDivisorWavelet t) else 0) -
      inner ℝ (f - inner ℝ (qTarget p hp.one_lt) qOne • qOne -
        primePowerProjection p hp) (normalizedDivisorWavelet t)) ^ 2) =
      ‖qTarget p hp.one_lt - f‖ ^ 2 := by
  let g := f - inner ℝ (qTarget p hp.one_lt) qOne • qOne - primePowerProjection p hp
  have hg : primeCofactorResidual p hp - g = qTarget p hp.one_lt - f := by
    dsimp [primeCofactorResidual, g]
    module
  have h := divisorHilbertBasis.tsum_inner_mul_inner
    (primeCofactorResidual p hp - g) (primeCofactorResidual p hp - g)
  have he (t : ℕ+) :
      inner ℝ (primeCofactorResidual p hp - g) (normalizedDivisorWavelet t) *
        inner ℝ (normalizedDivisorWavelet t) (primeCofactorResidual p hp - g) =
      ((if t ≠ 1 ∧ p.Coprime (t : ℕ) then
        inner ℝ (qTarget p hp.one_lt) (normalizedDivisorWavelet t) else 0) -
        inner ℝ g (normalizedDivisorWavelet t)) ^ 2 := by
    have hc : inner ℝ (normalizedDivisorWavelet t) (primeCofactorResidual p hp - g) =
        inner ℝ (primeCofactorResidual p hp - g) (normalizedDivisorWavelet t) :=
      real_inner_comm _ _
    rw [hc, inner_sub_left, primeCofactorResidual_inner_basis, pow_two]
  simp only [divisorHilbertBasis_apply] at h
  simp_rw [he] at h
  rw [real_inner_self_eq_norm_sq, hg] at h
  exact h

end RiemannResearch.RH.PrimePowerTarget
