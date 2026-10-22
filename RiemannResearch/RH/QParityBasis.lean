/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoParitySignal
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Orthonormal constant and parity coordinates in the Zipf-two Hilbert space

Source: user-provided orthonormal-basis research direction, 20 October 2026.
The weighted mean and even-index identities support a normalized two-vector
orthonormal family. Its approximation has an exact energy decomposition with
the complete residual norm retained. This module makes no enclosure-membership
claim and does not depend on the prime-power targets.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace RiemannResearch.RH
namespace ZetaTwoHilbert
open ZetaTwoProbability

theorem qWeighted_one_term (f : QHilbert) (k : ℕ) :
    positiveQWeight k * qSequence f k * qSequence qOne k =
      positiveQWeight k * qSequence f k := by
  by_cases hk : k = 0
  · subst k
    simp
  · simp [qSequence_qOne, qOneSequence, hk]

theorem qInner_one_tsum (f : QHilbert) :
    inner ℝ f qOne = ∑' k : ℕ, positiveQWeight k * qSequence f k := by
  rw [qInner_weighted]
  exact tsum_congr (qWeighted_one_term f)

theorem qWeighted_summable (f : QHilbert) :
    Summable (fun k : ℕ => positiveQWeight k * qSequence f k) := by
  have h := qSequence_product_summable f qOne
  simpa only [qWeighted_one_term] using h

end ZetaTwoHilbert

namespace ZetaTwoParitySignal
open ZetaTwoHilbert ZetaTwoProbability

theorem qInner_even_reindex (f : QHilbert) :
    inner ℝ f qEven =
      ∑' k : ℕ, positiveQWeight (2 * k) * qSequence f (2 * k) := by
  rw [qInner_weighted]
  have hterms : (fun k => positiveQWeight k * qSequence f k * qSequence qEven k) =
      fun k => if 2 ∣ k then positiveQWeight k * qSequence f k else 0 := by
    funext k
    by_cases hk : k = 0
    · subst k
      simp
    · by_cases hd : 2 ∣ k <;> simp [qSequence_qEven, hk, hd]
  rw [hterms]
  apply tsum_eq_tsum_of_ne_zero_bij
    (fun k : Function.support (fun j : ℕ =>
      positiveQWeight (2 * j) * qSequence f (2 * j)) => 2 * k.val)
  · intro a b hab
    apply Subtype.ext
    change 2 * a.val = 2 * b.val at hab
    omega
  · intro k hk
    change (if 2 ∣ k then positiveQWeight k * qSequence f k else 0) ≠ 0 at hk
    have hd : 2 ∣ k := by
      by_contra hnot
      apply hk
      exact if_neg hnot
    obtain ⟨a, ha⟩ := hd
    refine ⟨⟨a, ?_⟩, ha.symm⟩
    change positiveQWeight (2 * a) * qSequence f (2 * a) ≠ 0
    rw [← ha]
    simpa only [if_pos (show 2 ∣ k from ⟨a, ha⟩)] using hk
  · intro k
    exact if_pos (dvd_mul_right 2 k.val)

def parityCentered : QHilbert := (4 : ℝ) • qEven - qOne

theorem parityCentered_inner_one : inner ℝ parityCentered qOne = 0 := by
  rw [parityCentered, inner_sub_left, real_inner_smul_left,
    qEven_inner_qOne, real_inner_self_eq_norm_sq, qOne_norm_sq]
  norm_num

theorem parityCentered_norm_sq : ‖parityCentered‖ ^ 2 = 3 := by
  have hOE : inner ℝ qOne qEven = (1 / 4 : ℝ) := by
    rw [real_inner_comm, qEven_inner_qOne]
  rw [← real_inner_self_eq_norm_sq]
  simp only [parityCentered, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right,
    qEven_inner_qOne, hOE, real_inner_self_eq_norm_sq, qOne_norm_sq,
    norm_smul, Real.norm_eq_abs, mul_pow, qEven_norm_sq]
  norm_num

def parityUnit : QHilbert := (1 / Real.sqrt 3) • parityCentered

theorem parityUnit_inner_one : inner ℝ parityUnit qOne = 0 := by
  rw [parityUnit, real_inner_smul_left, parityCentered_inner_one, mul_zero]

theorem parityUnit_norm_sq : ‖parityUnit‖ ^ 2 = 1 := by
  rw [parityUnit, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    parityCentered_norm_sq, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

/-- The constant and centered parity coordinates, indexed by two Boolean values. -/
def parityFrame : Bool → QHilbert
  | false => qOne
  | true => parityUnit

/-- The constant and centered parity form an orthonormal family. -/
theorem parityFrame_orthonormal : Orthonormal ℝ parityFrame := by
  rw [orthonormal_iff_ite]
  have h1p : inner ℝ qOne parityUnit = 0 := by
    rw [real_inner_comm, parityUnit_inner_one]
  intro i j
  cases i <;> cases j <;>
    simp [parityFrame, qOne_norm_sq,
      parityUnit_norm_sq, parityUnit_inner_one, h1p]

/-- The orthogonal expansion on the constant and parity coordinates. -/
def parityApproximation (f : QHilbert) : QHilbert :=
  (inner ℝ f qOne) • qOne + (inner ℝ f parityUnit) • parityUnit

/-- Exact energy decomposition; the complete residual norm is retained. -/
theorem parityApproximation_energy_exact (f : QHilbert) :
    ‖f‖ ^ 2 = (inner ℝ f qOne) ^ 2 + (inner ℝ f parityUnit) ^ 2 +
      ‖f - parityApproximation f‖ ^ 2 := by
  have h11 : inner ℝ qOne qOne = 1 := by
    rw [real_inner_self_eq_norm_sq, qOne_norm_sq]
  have hpp : inner ℝ parityUnit parityUnit = 1 := by
    rw [real_inner_self_eq_norm_sq, parityUnit_norm_sq]
  have h1p : inner ℝ qOne parityUnit = 0 := by
    rw [real_inner_comm, parityUnit_inner_one]
  have h1f : inner ℝ qOne f = inner ℝ f qOne := real_inner_comm _ _
  have hpf : inner ℝ parityUnit f = inner ℝ f parityUnit := real_inner_comm _ _
  simp only [parityApproximation, ← real_inner_self_eq_norm_sq,
    inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right,
    h11, hpp, h1p, parityUnit_inner_one, h1f, hpf]
  ring

end ZetaTwoParitySignal
end RiemannResearch.RH
