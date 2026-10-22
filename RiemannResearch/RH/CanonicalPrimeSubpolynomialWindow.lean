/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CRTSubpolynomialTail
import RiemannResearch.RH.ParetoReciprocalWindow
import RiemannResearch.RH.CRTSquarefreeConverse
import RiemannResearch.RH.CanonicalMobiusFullEnergy

/-!
# Explicit prime Mobius trials and quadratic-window RH criteria

Source: user-requested sufficient CRT tail goal, 13 October 2026.
The canonical trial is exact on its head and has squarefree support at a prime
boundary. Its elementary envelope controls the entire infinite tail after a
quadratic cutoff. The subpolynomial finite-window estimate is a remaining
arithmetic provider, not a proved bound or an unconditional proof of RH.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative ParetoBeurlingMellinObstruction
open RiemannResearch.Analysis.SubpolynomialWindow

private theorem squarefree_normalizedResidue_mem
    (d : ℕ) (hd : 0 < d) (hsq : Squarefree d) :
    normalizedResidueHilbert d hd ∈ squarefreeCRTSpan := by
  by_cases h1 : d = 1
  · subst d
    have hz : normalizedResidueHilbert 1 hd = 0 := by
      apply hilbertSequence_injective
      rw [normalizedResidueHilbert_sequence]
      funext n
      cases n <;> simp [residueFraction, hilbertSequence, Nat.mod_one]
    rw [hz]
    exact squarefreeCRTSpan.zero_mem
  · rw [squarefreeCRTSpan_eq_span]
    exact Submodule.subset_span ⟨⟨d, by omega, hsq⟩, rfl⟩

/-- At a squarefree boundary the canonical Mobius trial uses only squarefree atoms. -/
theorem canonicalMobiusHilbert_mem_squarefreeCRTSpan
    (Y : ℕ) (hY : Squarefree (Y + 1)) :
    canonicalMobiusHilbert Y ∈ squarefreeCRTSpan := by
  unfold canonicalMobiusHilbert
  apply squarefreeCRTSpan.add_mem
  · apply squarefreeCRTSpan.neg_mem
    apply squarefreeCRTSpan.sum_mem
    intro d hd
    by_cases hsq : Squarefree (d : ℕ)
    · exact squarefreeCRTSpan.smul_mem _
        (squarefree_normalizedResidue_mem d (Finset.mem_Icc.mp d.property).1 hsq)
    · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
  · exact squarefreeCRTSpan.smul_mem _
      (squarefree_normalizedResidue_mem (Y + 1) (Nat.succ_pos _) hY)

/-- Concrete finite arithmetic energy; its cutoff is quadratic, not a primorial. -/
def canonicalPrimeWindowEnergy (p : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc p (4 * p ^ 2),
    |1 - canonicalMobiusHead (p - 1) n| ^ 2 / (n : ℝ) ^ 2

theorem canonicalPrimeWindowEnergy_nonneg (p : ℕ) :
    0 ≤ canonicalPrimeWindowEnergy p := by
  unfold canonicalPrimeWindowEnergy
  exact Finset.sum_nonneg (fun _ _ => div_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The already proved amplitude bound controls everything beyond the quadratic window. -/
theorem canonicalPrime_error_le_window_add_one
    (p : ℕ) (hp : 2 ≤ p) :
    ‖hilbertOne - canonicalMobiusHilbert (p - 1)‖ ^ 2 ≤
      canonicalPrimeWindowEnergy p + 1 := by
  have hpred : p - 1 + 1 = p := by omega
  have hR (n : ℕ) : |1 - canonicalMobiusHead (p - 1) n| ≤ 2 * (p : ℝ) := by
    have hb := canonicalMobiusHead_abs_le_two_mul (p - 1) (by omega) n
    have hc : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ p)]
      norm_num
    have ht := abs_add_le (1 : ℝ) (-canonicalMobiusHead (p - 1) n)
    simp only [abs_one, abs_neg, ← sub_eq_add_neg] at ht
    rw [hc] at hb
    linarith
  have hhead (n : ℕ) (hn : 0 < n) (hnM : n ≤ p - 1) :
      1 - canonicalMobiusHead (p - 1) n = 0 := by
    rw [canonicalMobiusHead_exact _ _ hn hnM]
    ring
  have hw := paretoInner_le_reciprocal_window_add_tail
    (fun n => 1 - canonicalMobiusHead (p - 1) n) (p - 1) (4 * p ^ 2) hR hhead
  have htail : (2 * (p : ℝ)) ^ 2 / ((4 * p ^ 2 + 1 : ℕ) : ℝ) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < ((4 * p ^ 2 + 1 : ℕ) : ℝ))).mpr
    push_cast
    nlinarith
  rw [hilbertOne_sub_norm_sq_eq_paretoError, canonicalMobiusHilbert_sequence]
  change paretoInner _ _ ≤ _
  simpa only [hpred, canonicalPrimeWindowEnergy] using
    hw.trans (add_le_add le_rfl htail)

/-- The arithmetic provider is only subpolynomial growth of one explicit finite sum. -/
theorem riemannHypothesis_of_canonical_prime_subpolynomial_window
    (p : ℕ → ℕ) (hp : ∀ j, (p j).Prime)
    (hcofinal : Tendsto p atTop atTop)
    (hsub : Tendsto (fun j => Real.log (1 + canonicalPrimeWindowEnergy (p j)) /
      Real.log (p j : ℝ)) atTop (𝓝 0)) :
    RiemannHypothesis := by
  apply RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mpr
  intro s hs hslt hz
  have hs1 : s ≠ 1 := by intro he; norm_num [he] at hslt
  have hs0 : s ≠ 0 := by intro he; norm_num [he] at hs
  have ha : 0 < 2 * s.re - 1 := by linarith
  have hc : 0 < (2 * s.re - 1) / ‖s‖ ^ 2 :=
    div_pos ha (pow_pos (norm_pos_iff.mpr hs0) 2)
  apply no_positive_power_floor (fun j => (p j : ℝ))
    (fun j => canonicalPrimeWindowEnergy (p j)) 1
    ((2 * s.re - 1) / ‖s‖ ^ 2) (2 * s.re - 1)
    (tendsto_natCast_atTop_atTop.comp hcofinal)
    (fun j => canonicalPrimeWindowEnergy_nonneg _) (by norm_num) hc ha hsub
  apply Eventually.of_forall
  intro j
  have hpred : p j - 1 + 1 = p j := by have := (hp j).two_le; omega
  have hsq : Squarefree (p j - 1 + 1) := by rw [hpred]; exact (hp j).squarefree
  obtain ⟨L, hL, hmem⟩ := canonicalMobiusHilbert_mem_squarefreeCRTSpan (p j - 1) hsq
  obtain ⟨f, hf, hseq, hb, hperiod⟩ := divisorResidueSpan_lift hmem
  have heq : f = canonicalMobiusHilbert (p j - 1) := hilbertSequence_injective hseq
  have hmem' : canonicalMobiusHilbert (p j - 1) ∈ normalizedResidueSpan := by
    rwa [heq] at hf
  have hlo := normalizedResidue_exact_head_residual_power_lower hmem' (p j - 1)
    (canonicalMobiusHilbert_exact (p j - 1)) s hs hs1 hz
  have hcast : ((p j - 1 : ℕ) : ℝ) + 1 = (p j : ℝ) := by exact_mod_cast hpred
  rw [hcast] at hlo
  exact hlo.trans (canonicalPrime_error_le_window_add_one (p j) (hp j).two_le)

/-- One prime with a vanishing-exponent finite budget at each stage suffices. -/
theorem riemannHypothesis_of_canonical_prime_reciprocal_exponents
    (htrial : ∀ j : ℕ, ∃ p : ℕ, p.Prime ∧ j + 2 ≤ p ∧
      canonicalPrimeWindowEnergy p ≤ (p : ℝ) ^ (1 / ((j : ℝ) + 1))) :
    RiemannHypothesis := by
  choose p hp hsize henergy using htrial
  have hcofinal : Tendsto p atTop atTop :=
    tendsto_atTop_mono (fun j => by change j ≤ p j; have := hsize j; omega) tendsto_id
  apply riemannHypothesis_of_canonical_prime_subpolynomial_window p hp hcofinal
  apply relativeLog_tendsto_zero_of_reciprocal_exponent
    (fun j => (p j : ℝ)) (fun j => canonicalPrimeWindowEnergy (p j))
  · intro j
    exact_mod_cast hsize j
  · intro j
    exact canonicalPrimeWindowEnergy_nonneg _
  · exact henergy

end RiemannResearch.RH.Pareto
