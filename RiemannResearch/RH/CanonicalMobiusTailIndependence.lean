/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CanonicalMobiusTailNondegeneracy
import RiemannResearch.RH.CanonicalMobiusTriangular

/-!
# Linear independence of complete canonical Möbius tails

Source: user-provided Pareto affine-exhaustion handoff for the finite canonical
family and its full-tail covariance. The proof combines established finite
periodicity, triangular legal coordinates, and Möbius reciprocal nonvanishing.
Every finite family of distinct positive canonical indices has a positive
definite full-tail covariance at every cutoff. No uniform lower eigenvalue or
asymptotic capacity bound is asserted.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.RH.ArithmeticCumulative

/-- The complete tail restriction is injective on every finite legal space. -/
theorem finiteSpace_eq_zero_of_tailShift_eq_zero (M N : ℕ)
    (f : ThresholdHilbert) (hf : f ∈ finiteSpace M)
    (htail : hilbertTailShift f N = 0) : f = 0 := by
  let q : ℕ := N * (M + 1).factorial
  have hNq : N ≤ q := by
    dsimp [q]
    have hp := Nat.factorial_pos (M + 1)
    nlinarith
  have hdiv : ∀ d : Fin M, d.val + 2 ∣ q := by
    intro d
    have hd : d.val + 2 ∣ (M + 1).factorial :=
      Nat.dvd_factorial (by omega) (by omega)
    exact dvd_mul_of_dvd_right hd N
  apply finiteSpace_eq_zero_of_head_zero M f hf
  intro j hj hjM
  have hperiod := finiteSpace_sequence_add_of_dvd M j q hdiv f hf
  have hN : N ≤ j + q - 1 := by omega
  have hc : f (j + q - 1) = 0 := by
    have h := congrArg (fun x : ThresholdHilbert => x (j + q - 1 - N)) htail
    change f (j + q - 1 - N + N) = 0 at h
    simpa only [Nat.sub_add_cancel hN] using h
  have he : j + q = (j + q - 1) + 1 := by omega
  have hzero : hilbertSequence f (j + q) = 0 := by
    rw [he, hilbertSequence_succ, hc, zero_div]
  rw [hzero] at hperiod
  exact hperiod.symm

theorem finiteSpace_eq_of_tailShift_eq (M N : ℕ)
    (f g : ThresholdHilbert) (hf : f ∈ finiteSpace M) (hg : g ∈ finiteSpace M)
    (htail : hilbertTailShift f N = hilbertTailShift g N) : f = g := by
  apply sub_eq_zero.mp
  apply finiteSpace_eq_zero_of_tailShift_eq_zero M N (f - g)
    ((finiteSpace M).sub_mem hf hg)
  change hilbertTailShiftLinear N (f - g) = 0
  rw [map_sub]
  exact sub_eq_zero.mpr htail

theorem consecutiveResidueHilbert_not_mem_previous (M : ℕ) :
    consecutiveResidueHilbert M ∉ finiteSpace M := by
  intro hm
  have hz := finiteSpace_eq_zero_of_head_zero M (consecutiveResidueHilbert M) hm
    (fun j hj hjM => consecutiveResidueHilbert_head_zero M j hjM)
  have hd := consecutiveResidueHilbert_diagonal M
  rw [hz] at hd
  have hzero : hilbertSequence (0 : ThresholdHilbert) (M + 1) = 0 := by
    change hilbertSequenceLinear 0 (M + 1) = 0
    simp
  rw [hzero] at hd
  have hp : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
  linarith

/-- Every positive canonical vector introduces a genuinely new legal direction. -/
theorem canonicalMobiusHilbert_succ_not_mem_previous (M : ℕ) :
    canonicalMobiusHilbert (M + 1) ∉ finiteSpace M := by
  intro hm
  have hd := (finiteSpace M).sub_mem hm (canonicalMobiusHilbert_mem_finiteSpace M)
  rw [canonicalMobiusHilbert_succ_sub] at hd
  have hi := (finiteSpace M).smul_mem (mobiusReciprocalSum (M + 1))⁻¹ hd
  have hstep : consecutiveResidueHilbert M ∈ finiteSpace M := by
    simpa only [smul_smul,
      inv_mul_cancel₀ (mobiusReciprocalSum_ne_zero (N := M + 1) (by omega)),
      one_smul] using hi
  exact consecutiveResidueHilbert_not_mem_previous M hstep

/-- No combination of older conductors can reproduce the new complete tail. -/
theorem canonicalMobiusHilbert_succ_tail_ne_previous (M N : ℕ)
    (f : ThresholdHilbert) (hf : f ∈ finiteSpace M) :
    hilbertTailShift (canonicalMobiusHilbert (M + 1)) N ≠ hilbertTailShift f N := by
  intro he
  have hfu : f ∈ finiteSpace (M + 1) :=
    RiemannResearch.Analysis.ExhaustiveWalk.walkSpan_mono residueAtom id
      (by omega : M ≤ M + 1) hf
  have hsame := finiteSpace_eq_of_tailShift_eq (M + 1) N
    (canonicalMobiusHilbert (M + 1)) f
    (canonicalMobiusHilbert_mem_finiteSpace (M + 1)) hfu he
  exact canonicalMobiusHilbert_succ_not_mem_previous M (hsame.symm ▸ hf)

/-- In particular every one-step residual denominator is strictly positive. -/
theorem canonicalMobiusHilbert_succ_tail_residual_energy_pos (M N : ℕ)
    (f : ThresholdHilbert) (hf : f ∈ finiteSpace M) :
    0 < ‖hilbertTailShift (canonicalMobiusHilbert (M + 1)) N -
      hilbertTailShift f N‖ ^ 2 := by
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  exact sub_ne_zero.mpr (canonicalMobiusHilbert_succ_tail_ne_previous M N f hf)


/-- Distinct positive canonical indices have no finite coefficient relations. -/
theorem signedMobiusAverage_eq_zero_imp_coeff_zero
    (s : Finset ℕ) (a : ℕ → ℝ) (M : ℕ)
    (hpos : ∀ k ∈ s, 0 < k) (hupper : ∀ k ∈ s, k ≤ M)
    (hz : signedMobiusAverage s a = 0) : ∀ k ∈ s, a k = 0 := by
  classical
  induction M generalizing s with
  | zero =>
    intro k hk
    have hp := hpos k hk
    have hu := hupper k hk
    omega
  | succ M ih =>
    by_cases hs : M + 1 ∈ s
    · have htpos : ∀ k ∈ s.erase (M + 1), 0 < k := by
        intro k hk
        exact hpos k (Finset.mem_of_mem_erase hk)
      have htupper : ∀ k ∈ s.erase (M + 1), k ≤ M := by
        intro k hk
        have hu := hupper k (Finset.mem_of_mem_erase hk)
        have hn := (Finset.mem_erase.mp hk).1
        omega
      have hf := signedMobiusAverage_mem_finiteSpace (s.erase (M + 1)) a M htupper
      have heq : signedMobiusAverage (s.erase (M + 1)) a +
          a (M + 1) • canonicalMobiusHilbert (M + 1) = 0 := by
        change (∑ k ∈ s.erase (M + 1), a k • canonicalMobiusHilbert k) +
          a (M + 1) • canonicalMobiusHilbert (M + 1) = 0
        rw [Finset.sum_erase_add _ _ hs]
        exact hz
      have hcoef : a (M + 1) = 0 := by
        by_contra ha
        have hv : a (M + 1) • canonicalMobiusHilbert (M + 1) ∈ finiteSpace M := by
          have he : a (M + 1) • canonicalMobiusHilbert (M + 1) =
              -signedMobiusAverage (s.erase (M + 1)) a := by
            apply eq_neg_iff_add_eq_zero.mpr
            rwa [add_comm]
          rw [he]
          exact (finiteSpace M).neg_mem hf
        have hi := (finiteSpace M).smul_mem (a (M + 1))⁻¹ hv
        have hmem : canonicalMobiusHilbert (M + 1) ∈ finiteSpace M := by
          simpa only [smul_smul, inv_mul_cancel₀ ha, one_smul] using hi
        exact canonicalMobiusHilbert_succ_not_mem_previous M hmem
      have htz : signedMobiusAverage (s.erase (M + 1)) a = 0 := by
        simpa only [hcoef, zero_smul, add_zero] using heq
      have ht := ih (s.erase (M + 1)) htpos htupper htz
      intro k hk
      by_cases he : k = M + 1
      · simpa only [he] using hcoef
      · exact ht k (Finset.mem_erase.mpr ⟨he, hk⟩)
    · apply ih s hpos _ hz
      intro k hk
      have hu := hupper k hk
      have hn : k ≠ M + 1 := by intro he; exact hs (he ▸ hk)
      omega

/-- The covariance of every finite set of distinct positive canonical indices
is positive definite for every tail cutoff, including cutoff zero. -/
theorem signedMobiusAverage_covariance_pos_of_coeff_ne_zero
    (s : Finset ℕ) (a : ℕ → ℝ) (N M : ℕ)
    (hpos : ∀ k ∈ s, 0 < k) (hupper : ∀ k ∈ s, k ≤ M)
    (ha : ∃ k ∈ s, a k ≠ 0) :
    0 < ∑ k ∈ s, ∑ l ∈ s, a k * a l * canonicalMobiusTailCovariance N k l := by
  rw [← signedMobiusAverage_tail_energy]
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro hz
  have hf := finiteSpace_eq_zero_of_tailShift_eq_zero M N (signedMobiusAverage s a)
    (signedMobiusAverage_mem_finiteSpace s a M hupper) hz
  obtain ⟨k, hk, hka⟩ := ha
  exact hka (signedMobiusAverage_eq_zero_imp_coeff_zero s a M hpos hupper hf k hk)

end RiemannResearch.RH.Pareto.CoefficientStabilization
