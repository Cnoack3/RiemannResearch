/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimePowerWaveletCompleteness
import RiemannResearch.RH.PrimeValuationHilbertBasis
import RiemannResearch.RH.QPrimePowerHilbertFrame
import RiemannResearch.RH.QDivisorHilbertBasis
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
/-!
# Cross-prime geometry of complete physical valuation spaces

Source: user-provided valuation/Meixner and Zipf-independence research direction;
see FpOrthonormalBasisResearch20261020.md. Complete wavelet expansions extend
cross-prime orthogonality to arbitrary square-integrable valuation observables.
These are actual Q-Hilbert statements, not abstract finite Boolean identities.
The exact signed mean discrepancy and both centered norm squares are retained.

This supplies a Hilbert-space input for tensor-basis work. It does not prove
tensor or Meixner completeness and does not identify Nat.log with valuation.
No legal squarefree-closure membership is asserted.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace RiemannResearch.RH.PrimeValuationBasis
open ZetaTwoHilbert QDivisorHilbert

private theorem innerSL_eval (x y : QHilbert) : innerSL ℝ x y = inner ℝ x y := rfl

/-- A positive-degree p-wavelet annihilates every q-wavelet for distinct primes. -/
theorem primePowerFrame_inner_distinct (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (k l : ℕ) :
    inner ℝ (primePowerFrame p hp (k+1)) (primePowerFrame q hq l) = 0 := by
  have hne : (⟨p^(k+1), pow_pos hp.pos _⟩ : ℕ+) ≠ ⟨q^l, pow_pos hq.pos _⟩ := by
    intro he
    have heq : p^(k+1) = q^l := congrArg Subtype.val he
    have hd : p ∣ q := hp.dvd_of_dvd_pow (heq ▸ dvd_pow_self p (Nat.succ_ne_zero k))
    exact hpq ((Nat.dvd_prime hq).mp hd |>.resolve_left hp.ne_one)
  exact (orthonormal_iff_ite.mp normalizedDivisorWavelet_orthonormal _ _).trans
    (if_neg hne)

/-- A positive-degree p-wavelet annihilates the entire physical q-valuation space. -/
theorem inner_valuation_other_wavelet (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (g : valuationSpace q) (k : ℕ) :
    inner ℝ (primePowerFrame p hp (k+1)) g.val = 0 := by
  have h := (valuationWavelet_hasSum q hq g).mapL
    (innerSL ℝ (primePowerFrame p hp (k+1)))
  have hz : HasSum (fun _ : ℕ => (0 : ℝ)) 0 := hasSum_zero
  have he : (fun l => (innerSL ℝ (primePowerFrame p hp (k+1)))
      (inner ℝ (primePowerFrame q hq l) g.val • primePowerFrame q hq l)) =
      (fun _ : ℕ => (0 : ℝ)) := by
    funext l
    simp only [map_smul, innerSL_eval, smul_eq_mul,
      primePowerFrame_inner_distinct p q hp hq hpq, mul_zero]
  rw [he] at h
  exact h.unique hz

/-- The inner product of arbitrary distinct-prime valuation vectors factors into means. -/
theorem valuation_inner_distinct (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (f : valuationSpace p) (g : valuationSpace q) :
    inner ℝ f.val g.val = inner ℝ f.val qOne * inner ℝ qOne g.val := by
  have h := (valuationWavelet_hasSum p hp f).mapL (innerSL ℝ g.val)
  have he : (fun k => (innerSL ℝ g.val)
      (inner ℝ (primePowerFrame p hp k) f.val • primePowerFrame p hp k)) =
      (fun k : ℕ => if k = 0 then inner ℝ f.val qOne * inner ℝ qOne g.val else 0) := by
    funext k
    cases k with
    | zero => simp [real_inner_comm]
    | succ k =>
      simp only [map_smul, innerSL_eval, smul_eq_mul, Nat.succ_ne_zero, if_false]
      rw [show inner ℝ g.val (primePowerFrame p hp (k+1)) =
          inner ℝ (primePowerFrame p hp (k+1)) g.val from real_inner_comm _ _,
        inner_valuation_other_wavelet p q hp hq hpq g k, mul_zero]
  rw [he] at h
  have hh := h.unique (hasSum_ite_eq 0 (inner ℝ f.val qOne * inner ℝ qOne g.val))
  simpa only [innerSL_eval, real_inner_comm g.val f.val] using hh

/-- Centered physical valuation spaces for distinct primes are orthogonal. -/
theorem valuation_centered_inner_distinct (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (f : valuationSpace p) (g : valuationSpace q) :
    inner ℝ (f.val - inner ℝ f.val qOne • qOne)
      (g.val - inner ℝ g.val qOne • qOne) = 0 := by
  have hOne : inner ℝ qOne qOne = (1 : ℝ) := by
    simpa using orthonormal_iff_ite.mp (primePowerFrame_orthonormal p hp) 0 0
  rw [inner_sub_left, inner_sub_right, inner_sub_right,
    real_inner_smul_left, real_inner_smul_left, real_inner_smul_right,
    real_inner_smul_right, valuation_inner_distinct p q hp hq hpq, hOne]
  rw [real_inner_comm g.val qOne]
  ring

/-- Full variance and signed mean-discrepancy decomposition. -/
theorem valuation_cross_error_exact (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (f : valuationSpace p) (g : valuationSpace q) :
    ‖f.val - g.val‖^2 =
      ‖f.val - inner ℝ f.val qOne • qOne‖^2 +
      ‖g.val - inner ℝ g.val qOne • qOne‖^2 +
      (inner ℝ f.val qOne - inner ℝ g.val qOne)^2 := by
  have hOne : inner ℝ qOne qOne = (1 : ℝ) := by
    simpa using orthonormal_iff_ite.mp (primePowerFrame_orthonormal p hp) 0 0
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [valuation_inner_distinct p q hp hq hpq f g,
    valuation_inner_distinct q p hq hp (Ne.symm hpq) g f, hOne]
  rw [real_inner_comm qOne f.val, real_inner_comm qOne g.val]
  ring


/-- Exact best-approximation error over the other complete valuation space. -/
theorem valuation_cross_pythagoras (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (f : valuationSpace p) (g : valuationSpace q) :
    ‖f.val - g.val‖^2 =
      ‖f.val - inner ℝ f.val qOne • qOne‖^2 +
      ‖g.val - inner ℝ f.val qOne • qOne‖^2 := by
  have hOne : inner ℝ qOne qOne = (1 : ℝ) := by
    simpa using orthonormal_iff_ite.mp (primePowerFrame_orthonormal p hp) 0 0
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [valuation_inner_distinct p q hp hq hpq f g,
    valuation_inner_distinct q p hq hp (Ne.symm hpq) g f, hOne]
  rw [real_inner_comm qOne f.val, real_inner_comm qOne g.val]
  ring

/-- The mean constant is the unique best approximant in the other valuation space. -/
theorem valuation_cross_unique_best (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (f : valuationSpace p) (g : valuationSpace q) :
    ‖f.val - g.val‖^2 ≤ ‖f.val - inner ℝ f.val qOne • qOne‖^2 ↔
      g.val = inner ℝ f.val qOne • qOne := by
  rw [valuation_cross_pythagoras p q hp hq hpq]
  constructor
  · intro h
    have hz : ‖g.val - inner ℝ f.val qOne • qOne‖^2 = 0 := by
      nlinarith [sq_nonneg ‖g.val - inner ℝ f.val qOne • qOne‖]
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))
  · intro h
    simp [h]

/-- A physical vector depending separately on two distinct valuations is constant. -/
theorem valuation_intersection_constant (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (f : QHilbert) (hf : f ∈ valuationSpace p)
    (hg : f ∈ valuationSpace q) :
    f = inner ℝ f qOne • qOne := by
  apply (valuation_cross_unique_best p q hp hq hpq ⟨f,hf⟩ ⟨f,hg⟩).mp
  simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow]
  exact sq_nonneg _

end RiemannResearch.RH.PrimeValuationBasis
