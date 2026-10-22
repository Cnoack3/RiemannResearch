/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimePowerInfiniteProjection
import RiemannResearch.RH.QPrimePowerHilbertFrame
import RiemannResearch.RH.QPrimePowerWaveletCoefficients
import RiemannResearch.RH.QPrimePowerOrthogonal
import RiemannResearch.RH.QDivisorWaveletOverlap
import RiemannResearch.RH.QDivisorHilbertBasis
import RiemannResearch.RH.QDivisibilityDensity
import RiemannResearch.RH.SquarefreeRadicalDifference
import RiemannResearch.RH.PrimeValuationClosureObstruction
import RiemannResearch.RH.PrimePowerTwoTargetCriterion
import RiemannResearch.RH.QSquarefreeDilationObstruction
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.PrimePowerTargetMellin
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Centered valuation coordinates of the infinite prime-power projection

Source: user-provided valuation/Meixner basis research direction, 20 October 2026.
The finite adjacent-tail identity stabilizes at each positive integer after
its valuation cutoff. Continuity of physical coordinate evaluation identifies
the previously constructed Hilbert sum with v_p minus 1/(p^2-1).
Its normalized form is ((p^2-1)v_p-1)/p, the first Meixner polynomial with
geometric parameter p^(-2), as specified in FpOrthonormalBasisResearch20261020.md.
This identification does not replace the target F_p = Nat.log p n by v_p.
The existing square-jump obstruction proves both projection directions are
outside closureWithConstants. The exact energy and signed residual identities
remain those of QPrimePowerInfiniteProjection, with their full residuals.
Higher Meixner completeness and F_2/F_3 legal membership are not asserted.
-/

noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace RiemannResearch.RH.PrimePowerTarget
open ZetaTwoHilbert ZetaTwoProbability QDivisorHilbert QDivisibilityDensity

/-- Each weighted normalized mode is an exact adjacent divisibility-tail difference. -/
theorem primePower_projection_term (p k : ℕ) (hp : p.Prime) :
    inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1)) •
      primePowerFrame p hp (k+1) =
    ((p : ℝ)^2 - 1)⁻¹ •
      ((p : ℝ)^2 • qDivisor (p^(k+1)) - qDivisor (p^k)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hd : 0 ≤ (p : ℝ)^2 - 1 := by nlinarith
  have hc : (1 / ((p : ℝ)^k * Real.sqrt ((p : ℝ)^2-1))) *
      ((p : ℝ)^k * Real.sqrt ((p : ℝ)^2-1))⁻¹ =
      (((p : ℝ)^k)^2 * ((p : ℝ)^2-1))⁻¹ := by
    rw [one_div, ← mul_inv, ← pow_two, mul_pow, Real.sq_sqrt hd]
  rw [qTarget_inner_primePowerFrame_succ]
  unfold primePowerFrame normalizedDivisorWavelet
  change (1 / ((p : ℝ)^k * Real.sqrt ((p : ℝ)^2-1))) •
    ((Real.sqrt (qJordanTwo (p^(k+1))))⁻¹ • divisorWavelet (p^(k+1))) = _
  rw [qJordanTwo_prime_pow p (k+1) hp, valuationWaveletWeight_succ,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs,
    abs_of_pos (pow_pos hp0 _), smul_smul, hc,
    divisorWavelet_prime_pow_succ p k hp]
  simp only [smul_sub, smul_smul]
  congr 1
  · congr 1
    rw [pow_succ]
    field_simp
    ring
  · congr 1
    field_simp

/-- Positive physical coordinates of a single weighted mode in valuation-cutoff form. -/
theorem primePower_projection_term_sequence (p k n : ℕ) (hp : p.Prime)
    (hn : n ≠ 0) :
    qSequence
      (inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1)) •
        primePowerFrame p hp (k+1)) n =
      ((p : ℝ)^2 * (if k+1 ≤ n.factorization p then 1 else 0) -
        (if k ≤ n.factorization p then 1 else 0)) / ((p : ℝ)^2-1) := by
  rw [primePower_projection_term p k hp]
  change qSequenceLinear (_ • _) n = _
  rw [map_smul, map_sub, map_smul]
  change ((p : ℝ)^2-1)⁻¹ *
    ((p : ℝ)^2 * qSequence (qDivisor (p^(k+1))) n -
      qSequence (qDivisor (p^k)) n) = _
  rw [qSequence_qDivisor, qSequence_qDivisor]
  simp only [positiveDivisor, hn, ↓reduceIte, hp.pow_dvd_iff_le_factorization hn]
  ring

/-- At each positive integer the partial sums stabilize beyond its prime valuation. -/
theorem primePower_projection_partial_sequence (p n N : ℕ) (hp : p.Prime)
    (hn : n ≠ 0) (hN : n.factorization p < N) :
    qSequence (∑ k ∈ Finset.range N,
      inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1)) •
        primePowerFrame p hp (k+1)) n =
      (n.factorization p : ℝ) - 1 / ((p : ℝ)^2-1) := by
  let v := n.factorization p
  let f : ℕ → ℝ := fun k =>
    ((p : ℝ)^2 * (if k+1 ≤ v then 1 else 0) -
      (if k ≤ v then 1 else 0)) / ((p : ℝ)^2-1)
  have hd : (p : ℝ)^2-1 ≠ 0 := by
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    nlinarith
  have hsmall (k : ℕ) (hk : k ∈ Finset.range v) : f k = 1 := by
    have hkv := Finset.mem_range.mp hk
    simp [f, hkv, show k ≤ v by omega, hd]
  have hend : f v = -1 / ((p : ℝ)^2-1) := by simp [f]
  have hzero (k : ℕ) (hk : v+1 ≤ k) : f k = 0 := by
    simp [f, show ¬k < v by omega, show ¬k ≤ v by omega]
  have hsum : ∑ k ∈ Finset.range (v+1), f k =
      (v : ℝ) - 1 / ((p : ℝ)^2-1) := by
    rw [Finset.sum_range_succ, hend]
    rw [Finset.sum_congr rfl hsmall]
    simp
    ring
  have hsub : ∑ k ∈ Finset.range (v+1), f k = ∑ k ∈ Finset.range N, f k := by
    apply Finset.sum_subset (Finset.range_mono (by dsimp [v]; omega))
    intro k hk hnot
    exact hzero k (by simpa using hnot)
  change qSequenceLinear (∑ k ∈ Finset.range N, _) n = _
  rw [map_sum]
  simp only [Finset.sum_apply]
  change (∑ k ∈ Finset.range N, qSequence (_) n) = _
  simp_rw [primePower_projection_term_sequence p _ n hp hn]
  change (∑ k ∈ Finset.range N, f k) = _
  rw [← hsub]
  exact hsum

/-- The infinite same-prime projection is exactly the centered prime valuation. -/
theorem primePowerProjection_sequence (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    qSequence (primePowerProjection p hp) n =
      (n.factorization p : ℝ) - 1 / ((p : ℝ)^2-1) := by
  have ht := (SquarefreeRadicalDifference.continuous_qSequence n).tendsto
    (primePowerProjection p hp)
  have hlim := ht.comp (primePowerProjection_tendsto p hp)
  have he : (fun N => qSequence (∑ k ∈ Finset.range N,
      inner ℝ (qTarget p hp.one_lt) (primePowerFrame p hp (k+1)) •
        primePowerFrame p hp (k+1)) n) =ᶠ[Filter.atTop]
        (fun _ => (n.factorization p : ℝ) - 1 / ((p : ℝ)^2-1)) := by
    filter_upwards [Filter.eventually_ge_atTop (n.factorization p + 1)] with N hN
    exact primePower_projection_partial_sequence p n N hp hn (by omega)
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' he.symm)

/-- The normalized projection is the explicit first Meixner valuation polynomial. -/
theorem primePowerProjectionUnit_sequence (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    qSequence (primePowerProjectionUnit p hp) n =
      (((p : ℝ)^2-1) * (n.factorization p : ℝ) - 1) / p := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hd : (p : ℝ)^2-1 ≠ 0 := by nlinarith
  unfold primePowerProjectionUnit
  change qSequenceLinear (_ • _) n = _
  rw [map_smul]
  change _ * qSequence (primePowerProjection p hp) n = _
  rw [primePowerProjection_sequence p n hp hn]
  field_simp


/-- An actual Q-Hilbert representative of the prime valuation.
The floor-log target remains a separate vector. -/
def primeValuationVector (p : ℕ) (hp : p.Prime) : QHilbert :=
  primePowerProjection p hp + (1 / ((p : ℝ)^2-1)) • qOne

/-- All positive physical coordinates are the usual prime valuation. -/
theorem primeValuationVector_sequence (p n : ℕ) (hp : p.Prime) (hn : n ≠ 0) :
    qSequence (primeValuationVector p hp) n = (n.factorization p : ℝ) := by
  unfold primeValuationVector
  change qSequenceLinear (_ + _) n = _
  rw [map_add, map_smul]
  change qSequence (primePowerProjection p hp) n +
    (1 / ((p : ℝ)^2-1)) * qSequence qOne n = _
  rw [primePowerProjection_sequence p n hp hn, qSequence_qOne]
  simp [qOneSequence, hn]

/-- The centered valuation projection is outside the enlarged squarefree legal closure. -/
theorem primePowerProjection_not_mem_closureWithConstants (p : ℕ) (hp : p.Prime) :
    primePowerProjection p hp ∉ closureWithConstants := by
  intro h
  apply primeValuation_not_mem_closureWithConstants p hp (primeValuationVector p hp)
    (fun n hn => primeValuationVector_sequence p n hp (ne_of_gt hn))
  exact closureWithConstants.add_mem h
    (closureWithConstants.smul_mem _ qOne_mem_closureWithConstants)

/-- The normalized first Meixner direction is also outside the enlarged legal closure. -/
theorem primePowerProjectionUnit_not_mem_closureWithConstants (p : ℕ) (hp : p.Prime) :
    primePowerProjectionUnit p hp ∉ closureWithConstants := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hd : (p : ℝ)^2-1 ≠ 0 := by nlinarith
  have he : ((p : ℝ) / ((p : ℝ)^2-1)) • primePowerProjectionUnit p hp =
      primePowerProjection p hp := by
    unfold primePowerProjectionUnit
    rw [smul_smul]
    have hs : ((p : ℝ) / ((p : ℝ)^2-1)) * (((p : ℝ)^2-1) / p) = 1 := by
      field_simp
    rw [hs, one_smul]
  intro h
  apply primePowerProjection_not_mem_closureWithConstants p hp
  rw [← he]
  exact closureWithConstants.smul_mem _ h

/-- The normalized first Meixner direction is orthogonal to the physical constant. -/
theorem primePowerProjectionUnit_inner_qOne (p : ℕ) (hp : p.Prime) :
    inner ℝ qOne (primePowerProjectionUnit p hp) = 0 := by
  rw [primePowerProjectionUnit, real_inner_smul_right, qOne_inner_primePowerProjection,
    mul_zero]

end RiemannResearch.RH.PrimePowerTarget
