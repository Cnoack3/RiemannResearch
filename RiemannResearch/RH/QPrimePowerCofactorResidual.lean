/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimePowerValuationProjection
import RiemannResearch.RH.QPrimePowerInfiniteProjection
import RiemannResearch.RH.QPrimePowerWaveletCoefficients
import RiemannResearch.RH.PrimePowerTargetMellin
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
/-!
# The prime-free cofactor residual of a floor-logarithm target

Source: user-provided valuation/Meixner basis research direction, 20 October 2026,
and the decomposition proposed in FpOrthonormalBasisResearch20261020.md.
We identify the complete remainder after all same-prime modes with the centered
floor logarithm of n / p^(v_p(n)), using the actual Q-Hilbert representatives.
The target remains F_p = Nat.log p n, distinct from the prime valuation.

The exact weighted residual series is retained. The coordinates at 1 and p + 1
differ by one; completing their weighted square gives the lower bound
1 / (zeta(2) * (1 + (p + 1) ^ 2)). Hence all same-prime modes and the constant still
leave positive energy. This is an ambient projection statement, not a proof
of membership or nonmembership of F_2 or F_3 in closureWithConstants.
Higher Meixner completeness and the remaining cofactor coefficients stay open.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace RiemannResearch.RH.PrimePowerTarget
open ZetaTwoHilbert

/-- Splitting off the full prime-power divisor separates the floor logarithm exactly. -/
theorem log_eq_factorization_add_ordCompl (p n : ℕ) (hp : 1 < p) (hn : n ≠ 0) :
    Nat.log p n = n.factorization p + Nat.log p (n / p ^ n.factorization p) := by
  have h := log_mul_power p (n.factorization p) (n / p ^ n.factorization p) hp
    (ne_of_gt (Nat.ordCompl_pos p hn))
  rw [Nat.ordProj_mul_ordCompl_eq_self] at h
  omega

/-- The actual Q-Hilbert floor-logarithm target after removing its valuation. -/
def primeCofactorTarget (p : ℕ) (hp : p.Prime) : QHilbert :=
  qTarget p hp.one_lt - primeValuationVector p hp

/-- The remaining target is the floor logarithm of the prime-free cofactor. -/
theorem primeCofactorTarget_sequence (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    qSequence (primeCofactorTarget p hp) n =
      (Nat.log p (n / p ^ n.factorization p) : ℝ) := by
  unfold primeCofactorTarget
  change qSequenceLinear (_ - _) n = _
  rw [map_sub]
  change qSequence (qTarget p hp.one_lt) n - qSequence (primeValuationVector p hp) n = _
  rw [qTarget_sequence, primeValuationVector_sequence p n hp hn]
  change (Nat.log p n : ℝ) - (n.factorization p : ℝ) = _
  rw [log_eq_factorization_add_ordCompl p n hp.one_lt hn, Nat.cast_add]
  ring

/-- Exact mean of the cofactor target, including the valuation mean correction. -/
theorem primeCofactorTarget_mean (p : ℕ) (hp : p.Prime) :
    inner ℝ (primeCofactorTarget p hp) qOne =
      inner ℝ (qTarget p hp.one_lt) qOne - 1 / ((p : ℝ) ^ 2 - 1) := by
  have hz : inner ℝ (primePowerProjection p hp) qOne = 0 := by
    rw [real_inner_comm]
    exact qOne_inner_primePowerProjection p hp
  rw [primeCofactorTarget, inner_sub_left, primeValuationVector, inner_add_left,
    real_inner_smul_left, hz, real_inner_self_eq_norm_sq, qOne_norm_sq]
  ring

/-- The complete centered residual after all nonconstant same-prime modes. -/
def primeCofactorResidual (p : ℕ) (hp : p.Prime) : QHilbert :=
  qTarget p hp.one_lt - inner ℝ (qTarget p hp.one_lt) qOne • qOne -
    primePowerProjection p hp

/-- The existing projection residual is exactly the centered cofactor target. -/
theorem primeCofactorResidual_eq_centered (p : ℕ) (hp : p.Prime) :
    primeCofactorResidual p hp =
      primeCofactorTarget p hp - inner ℝ (primeCofactorTarget p hp) qOne • qOne := by
  rw [primeCofactorTarget_mean]
  unfold primeCofactorResidual primeCofactorTarget primeValuationVector
  module

/-- Positive physical coordinates of the complete cofactor residual. -/
theorem primeCofactorResidual_sequence (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    qSequence (primeCofactorResidual p hp) n =
      (Nat.log p (n / p ^ n.factorization p) : ℝ) -
        (inner ℝ (qTarget p hp.one_lt) qOne - 1 / ((p : ℝ) ^ 2 - 1)) := by
  rw [primeCofactorResidual_eq_centered]
  change qSequenceLinear (_ - _ • _) n = _
  rw [map_sub, map_smul]
  change qSequence (primeCofactorTarget p hp) n -
    inner ℝ (primeCofactorTarget p hp) qOne * qSequence qOne n = _
  rw [primeCofactorTarget_sequence p n hp hn, primeCofactorTarget_mean, qSequence_qOne]
  simp [qOneSequence, hn]

/-- The cofactor residual has zero actual Q mean. -/
theorem primeCofactorResidual_inner_qOne (p : ℕ) (hp : p.Prime) :
    inner ℝ (primeCofactorResidual p hp) qOne = 0 := by
  rw [primeCofactorResidual_eq_centered, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, qOne_norm_sq]
  ring

/-- Multiplying the input by any p-power leaves the cofactor residual unchanged. -/
theorem primeCofactorResidual_sequence_mul_power (p k n : ℕ) (hp : p.Prime)
    (hn : n ≠ 0) :
    qSequence (primeCofactorResidual p hp) (p ^ k * n) =
      qSequence (primeCofactorResidual p hp) n := by
  rw [primeCofactorResidual_sequence p _ hp
    (mul_ne_zero (pow_ne_zero k hp.ne_zero) hn),
    primeCofactorResidual_sequence p n hp hn]
  have h := Nat.ordCompl_div_pow_of_dvd k hp (dvd_mul_right (p ^ k) n)
  have hc : (p ^ k * n) / p ^ (p ^ k * n).factorization p =
      n / p ^ n.factorization p := by
    simpa only [Nat.mul_div_cancel_left n (pow_pos hp.pos k)] using h.symm
  rw [hc]

/-- Two positive coordinates differ by one, independent of the centering constant. -/
theorem primeCofactorResidual_coordinate_gap (p : ℕ) (hp : p.Prime) :
    qSequence (primeCofactorResidual p hp) (p + 1) -
      qSequence (primeCofactorResidual p hp) 1 = 1 := by
  have hnot : ¬ p ∣ p + 1 := by
    intro h
    have h1 : p ∣ 1 := (Nat.dvd_add_iff_right (dvd_refl p)).mpr h
    have := Nat.le_of_dvd (by omega : 0 < 1) h1
    have := hp.one_lt
    omega
  have hf := Nat.factorization_eq_zero_of_not_dvd hnot
  have hl : Nat.log p (p + 1) = 1 := by
    apply Nat.log_eq_of_pow_le_of_lt_pow
    · simp
    · have := hp.one_lt
      simp only [pow_succ]
      nlinarith
  rw [primeCofactorResidual_sequence p _ hp (by omega),
    primeCofactorResidual_sequence p 1 hp (by omega)]
  simp [hf, hl]
  ring

/-- The cofactor residual cannot vanish in the actual complete Q Hilbert space. -/
theorem primeCofactorResidual_ne_zero (p : ℕ) (hp : p.Prime) :
    primeCofactorResidual p hp ≠ 0 := by
  intro h
  have hg := primeCofactorResidual_coordinate_gap p hp
  change qSequenceLinear (primeCofactorResidual p hp) (p + 1) -
    qSequenceLinear (primeCofactorResidual p hp) 1 = 1 at hg
  simp [h] at hg

/-- The mean and all same-prime modes capture strictly less than the total target energy. -/
theorem qTarget_primePower_captured_energy_lt (p : ℕ) (hp : p.Prime) :
    (inner ℝ (qTarget p hp.one_lt) qOne) ^ 2 + (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1) ^ 2 <
      ‖qTarget p hp.one_lt‖ ^ 2 := by
  have hpos := sq_pos_of_pos (norm_pos_iff.mpr (primeCofactorResidual_ne_zero p hp))
  have he := qTarget_primePower_centered_energy_exact p hp
  change ‖qTarget p hp.one_lt‖ ^ 2 =
    (inner ℝ (qTarget p hp.one_lt) qOne) ^ 2 + (p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1) ^ 2 +
      ‖primeCofactorResidual p hp‖ ^ 2 at he
  linarith

/-- The full residual norm is the exact weighted cofactor series, with no terms removed. -/
theorem primeCofactorResidual_norm_sq_series (p : ℕ) (hp : p.Prime) :
    ‖primeCofactorResidual p hp‖ ^ 2 =
      ∑' n : ℕ, positiveQWeight n *
        ((Nat.log p (n / p ^ n.factorization p) : ℝ) -
          (inner ℝ (qTarget p hp.one_lt) qOne - 1 / ((p : ℝ) ^ 2 - 1))) ^ 2 := by
  rw [qNorm_weighted_sq]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp [positiveQWeight]
  · rw [primeCofactorResidual_sequence p n hp hn]

/-- The two physical coordinates 1 and p + 1 give an explicit positive residual-energy bound. -/
theorem primeCofactorResidual_energy_lower_bound (p : ℕ) (hp : p.Prime) :
    1 / (ZetaTwoProbability.zetaTwo * (1 + ((p : ℝ) + 1) ^ 2)) ≤
      ‖primeCofactorResidual p hp‖ ^ 2 := by
  let R := primeCofactorResidual p hp
  let a := qSequence R 1
  let b := qSequence R (p + 1)
  let z := ZetaTwoProbability.zetaTwo
  let t : ℝ := ((p : ℝ) + 1) ^ 2
  have hz : 0 < z := ZetaTwoProbability.zetaTwo_pos
  have ht : 0 < t := by dsimp [t]; positivity
  have hab : b = a + 1 := by
    have hg := primeCofactorResidual_coordinate_gap p hp
    change b - a = 1 at hg
    linarith
  have hsum := (qSequence_square_summable R).sum_le_tsum ({1, p + 1} : Finset ℕ)
    (fun i _ => mul_nonneg (positiveQWeight_nonneg i) (sq_nonneg _))
  have hne : (1 : ℕ) ≠ p + 1 := by have := hp.pos; omega
  rw [Finset.sum_pair hne, ← qNorm_weighted_sq] at hsum
  simp only [positiveQWeight, Nat.cast_one, Nat.cast_add, one_pow, mul_one] at hsum
  change (1 / z) * a ^ 2 + (1 / (z * t)) * b ^ 2 ≤ ‖R‖ ^ 2 at hsum
  have hs : a ^ 2 / z + b ^ 2 / (z * t) ≤ ‖R‖ ^ 2 := by
    simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using hsum
  have hid : a ^ 2 / z + (a + 1) ^ 2 / (z * t) - 1 / (z * (1+t)) =
      ((1+t) * a + 1) ^ 2 / (z * t*(1+t)) := by
    field_simp
    ring
  have hnon : 0 ≤ ((1+t) * a + 1) ^ 2 / (z * t*(1+t)) := by positivity
  change 1 / (z * (1+t)) ≤ ‖R‖ ^ 2
  rw [hab] at hs
  linarith

end RiemannResearch.RH.PrimePowerTarget
