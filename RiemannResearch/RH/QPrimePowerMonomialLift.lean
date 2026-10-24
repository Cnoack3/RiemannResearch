/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimePowerMeixnerTwo
import RiemannResearch.RH.QPrimePowerValuationProjection
import RiemannResearch.RH.QPrimePowerWaveletCoefficients
import RiemannResearch.RH.QPrimePowerHilbertFrame
import RiemannResearch.RH.PrimeValuationHilbertBasis
import RiemannResearch.RH.SquarefreeRadicalDifference
import RiemannResearch.RH.PrimePowerTargetMellin
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
/-!
# Monomial-weighted valuation lifts of every order

Source: user-provided valuation/Meixner basis research direction and
FpOrthonormalBasisResearch20261020.md. This extends the weighted-wavelet
construction used for the second Meixner mode to every monomial weight.
The physical coordinates retain the full finite power sum and endpoint
correction. Gram entries retain the entire convergent coefficient-moment
series. The order-two lift is explicitly a centered cubic valuation polynomial.

These raw lifts are not asserted orthonormal or complete. Normalization,
higher Meixner orthogonality and completeness remain separate obligations.
The floor-logarithm F_p remains distinct from valuation, and no legal
squarefree-closure membership or vanishing cofactor residual is asserted.
-/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace RiemannResearch.RH.PrimePowerTarget
open ZetaTwoHilbert QDivisorHilbert PrimeValuationBasis

/-- Every monomial-weighted wavelet series is absolutely summable in Q norm. -/
theorem primePower_monomial_summable (p m : ℕ) (hp : p.Prime) :
    Summable (fun k : ℕ => ((k : ℝ)^m *
      inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1))) •
        primePowerFrame p hp (k+1)) := by
  have h0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hr : ‖(p : ℝ)⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h0)]
    exact (inv_lt_one₀ h0).mpr h1
  apply Summable.of_norm
  apply ((summable_pow_mul_geometric_of_norm_lt_one m hr).mul_left
    (Real.sqrt ((p : ℝ)^2-1))⁻¹).congr
  intro k
  rw [norm_smul, (primePowerFrame_orthonormal p hp).1, mul_one,
    qTarget_inner_primePowerFrame_succ, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simp [one_div, mul_comm, mul_left_comm, mul_assoc]

/-- Actual Hilbert lift of a monomial weight on the wavelet index. -/
def primePowerMonomialLift (p : ℕ) (hp : p.Prime) (m : ℕ) : QHilbert :=
  ∑' k : ℕ, ((k : ℝ)^m *
    inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1))) •
      primePowerFrame p hp (k+1)

/-- Exact wavelet coefficients of the lift. -/
theorem primePowerMonomialLift_inner_frame (p : ℕ) (hp : p.Prime) (m j : ℕ) :
    inner ℝ (primePowerFrame p hp (j+1)) (primePowerMonomialLift p hp m) =
      (j : ℝ)^m * inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (j+1)) := by
  change (innerSL ℝ (primePowerFrame p hp (j+1))) (∑' k : ℕ, _) = _
  rw [(innerSL ℝ (primePowerFrame p hp (j+1))).map_tsum (primePower_monomial_summable p m hp)]
  change (∑' k : ℕ, inner ℝ (primePowerFrame p hp (j+1))
    (((k : ℝ)^m * inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1))) •
      primePowerFrame p hp (k+1))) = _
  simp only [real_inner_smul_right, orthonormal_iff_ite.mp (primePowerFrame_orthonormal p hp)]
  simp

/-- Pairing with the lift retains the whole convergent series. -/
theorem inner_primePowerMonomialLift (p : ℕ) (hp : p.Prime) (m : ℕ) (f : QHilbert) :
    inner ℝ f (primePowerMonomialLift p hp m) =
      ∑' k : ℕ, ((k : ℝ)^m *
        inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1))) *
        inner ℝ f (primePowerFrame p hp (k+1)) := by
  change (innerSL ℝ f) (∑' k : ℕ, _) = _
  rw [(innerSL ℝ f).map_tsum (primePower_monomial_summable p m hp)]
  change (∑' k : ℕ, inner ℝ f (_ • _)) = _
  simp only [real_inner_smul_right]

/-- Every monomial lift is centered under actual Q. -/
theorem primePowerMonomialLift_centered (p : ℕ) (hp : p.Prime) (m : ℕ) :
    inner ℝ qOne (primePowerMonomialLift p hp m) = 0 := by
  rw [inner_primePowerMonomialLift]
  have hi (k : ℕ) : inner ℝ qOne (primePowerFrame p hp (k+1)) = 0 := by
    rw [← primePowerFrame_zero p hp]
    exact (primePowerFrame_orthonormal p hp).2 (by omega)
  simp [hi]

/-- Complete Gram moment for any two monomial orders. -/
theorem primePowerMonomialLift_gram (p : ℕ) (hp : p.Prime) (m r : ℕ) :
    inner ℝ (primePowerMonomialLift p hp m) (primePowerMonomialLift p hp r) =
      ∑' k : ℕ, (k : ℝ)^(m+r) *
        (inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1)))^2 := by
  rw [inner_primePowerMonomialLift]
  apply tsum_congr
  intro k
  rw [show inner ℝ (primePowerMonomialLift p hp m) (primePowerFrame p hp (k+1)) =
      inner ℝ (primePowerFrame p hp (k+1)) (primePowerMonomialLift p hp m) from
      real_inner_comm _ _, primePowerMonomialLift_inner_frame, pow_add]
  ring

/-- Physical partial sums stabilize at the valuation cutoff, retaining the endpoint term. -/
theorem primePower_monomial_partial_sequence (p m n N : ℕ) (hp : p.Prime)
    (hn : n ≠ 0) (hN : n.factorization p < N) :
    qSequence (∑ k ∈ Finset.range N,
      ((k : ℝ)^m * inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1))) •
        primePowerFrame p hp (k+1)) n =
      (∑ k ∈ Finset.range (n.factorization p), (k : ℝ)^m) -
        (n.factorization p : ℝ)^m / ((p : ℝ)^2-1) := by
  let v := n.factorization p
  let f : ℕ → ℝ := fun k => (k : ℝ)^m *
    (((p : ℝ)^2 * (if k+1 ≤ v then 1 else 0) -
      (if k ≤ v then 1 else 0)) / ((p : ℝ)^2-1))
  have hd : (p : ℝ)^2-1 ≠ 0 := by
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    nlinarith
  have hsmall (k : ℕ) (hk : k ∈ Finset.range v) : f k = (k : ℝ)^m := by
    have hkv := Finset.mem_range.mp hk
    simp [f, hkv, show k ≤ v by omega, hd]
  have hend : f v = -(v : ℝ)^m / ((p : ℝ)^2-1) := by
    simp [f]
    ring
  have hzero (k : ℕ) (hk : v+1 ≤ k) : f k = 0 := by
    simp [f, show ¬k < v by omega, show ¬k ≤ v by omega]
  have hsub : ∑ k ∈ Finset.range (v+1), f k = ∑ k ∈ Finset.range N, f k := by
    apply Finset.sum_subset (Finset.range_mono (by dsimp [v]; omega))
    intro k hk hnot
    exact hzero k (by simpa using hnot)
  have hterm (k : ℕ) :
      qSequence (((k : ℝ)^m * inner ℝ (qTarget p hp.one_lt)
        (primePowerFrame p hp (k+1))) • primePowerFrame p hp (k+1)) n = f k := by
    rw [mul_smul]
    change qSequenceLinear ((k : ℝ)^m • _) n = _
    rw [map_smul]
    change (k : ℝ)^m * qSequence
      (inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1)) •
        primePowerFrame p hp (k+1)) n = _
    rw [primePower_projection_term_sequence p k n hp hn]
  change qSequenceLinear (∑ k ∈ Finset.range N, _) n = _
  rw [map_sum]
  simp only [Finset.sum_apply]
  change (∑ k ∈ Finset.range N, qSequence (_) n) = _
  simp_rw [hterm]
  rw [← hsub, Finset.sum_range_succ, hend, Finset.sum_congr rfl hsmall]
  dsimp only [v]
  ring

/-- Exact physical finite-power-sum formula for every order. -/
theorem primePowerMonomialLift_sequence (p : ℕ) (hp : p.Prime) (m n : ℕ)
    (hn : n ≠ 0) :
    qSequence (primePowerMonomialLift p hp m) n =
      (∑ k ∈ Finset.range (n.factorization p), (k : ℝ)^m) -
        (n.factorization p : ℝ)^m / ((p : ℝ)^2-1) := by
  have ht := (SquarefreeRadicalDifference.continuous_qSequence n).tendsto
    (primePowerMonomialLift p hp m)
  have hlim := ht.comp (primePower_monomial_summable p m hp).hasSum.tendsto_sum_nat
  have he : (fun N => qSequence (∑ k ∈ Finset.range N,
      ((k : ℝ)^m * inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1))) •
        primePowerFrame p hp (k+1)) n) =ᶠ[Filter.atTop]
      (fun _ => (∑ k ∈ Finset.range (n.factorization p), (k : ℝ)^m) -
        (n.factorization p : ℝ)^m / ((p : ℝ)^2-1)) := by
    filter_upwards [Filter.eventually_ge_atTop (n.factorization p+1)] with N hN
    exact primePower_monomial_partial_sequence p m n N hp hn (by omega)
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' he.symm)

/-- Every monomial lift belongs to the physical valuation space. -/
theorem primePowerMonomialLift_mem (p : ℕ) (hp : p.Prime) (m : ℕ) :
    primePowerMonomialLift p hp m ∈ valuationSpace p := by
  intro n hn
  rw [primePowerMonomialLift_sequence p hp m n hn,
    primePowerMonomialLift_sequence p hp m _ (pow_ne_zero _ hp.ne_zero)]
  simp [Nat.factorization_pow, hp.factorization]


/-- The full Gram series converges to the actual Hilbert pairing. -/
theorem primePowerMonomialLift_gram_hasSum (p : ℕ) (hp : p.Prime) (m r : ℕ) :
    HasSum (fun k : ℕ => (k : ℝ)^(m+r) *
      (inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1)))^2)
      (inner ℝ (primePowerMonomialLift p hp m) (primePowerMonomialLift p hp r)) := by
  rw [primePowerMonomialLift_gram]
  exact (primePower_coefficient_moment_summable p (m+r) hp).hasSum

/-- The floor-log target pairing is the full coefficient moment. -/
theorem qTarget_inner_primePowerMonomialLift (p : ℕ) (hp : p.Prime) (m : ℕ) :
    inner ℝ (qTarget p hp.one_lt) (primePowerMonomialLift p hp m) =
      ∑' k : ℕ, (k : ℝ)^m *
        (inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1)))^2 := by
  rw [inner_primePowerMonomialLift]
  apply tsum_congr
  intro k
  ring

/-- The order-two raw lift is an explicit centered cubic in the valuation. -/
theorem primePowerMonomialLift_two_sequence (p : ℕ) (hp : p.Prime) (n : ℕ)
    (hn : n ≠ 0) :
    qSequence (primePowerMonomialLift p hp 2) n =
      (n.factorization p : ℝ)*((n.factorization p : ℝ)-1)*
        (2*(n.factorization p : ℝ)-1)/6 -
      (n.factorization p : ℝ)^2 / ((p : ℝ)^2-1) := by
  have hs (v : ℕ) : (∑ k ∈ Finset.range v, (k : ℝ)^2) =
      (v : ℝ)*((v : ℝ)-1)*(2*(v : ℝ)-1)/6 := by
    induction v with
    | zero => simp
    | succ v ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring
  rw [primePowerMonomialLift_sequence p hp 2 n hn, hs]

end RiemannResearch.RH.PrimePowerTarget
