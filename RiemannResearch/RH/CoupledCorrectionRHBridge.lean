import RiemannResearch.RH.ArithmeticCumulativeEnergy
import RiemannResearch.RH.ThresholdBoundedInterpolation
import RiemannResearch.RH.ParetoLegalApproximationClosure

/-!
# Full-energy coupled corrections imply the actual Riemann hypothesis

The uniform energy bound is an explicit hypothesis, not an axiom or a theorem
asserting the existence of such corrections. The conclusion is mathlib's
`RiemannHypothesis`, using the existing arithmetic Mellin bridge.
-/

namespace RiemannResearch.RH.ArithmeticCumulative
noncomputable section
open scoped BigOperators
open Pareto

def allPositiveSeeds : Set ℕ := {d | 0 < d}

/-- Full cumulative energy, used on the square-summable domain. -/
def cumulativeEnergy (f : ℕ → ℝ) : ℝ := fullSquaredNorm (cumulative f)

theorem weight_eq_positiveWeight (n : ℕ) : weight n = positiveWeight n := rfl

/-- Legal witnesses are in the summable domain; totalized `tsum` is not a loophole. -/
theorem legal_fullSquaredNorm_summable (A : Set ℕ) (hA : ∀ d ∈ A, 0 < d)
    (F : ℕ → ℝ) (hF : F ∈ legalSeedSpan A) :
    Summable (fun n => weight n * F n ^ 2) := by
  obtain ⟨f, _, hseq⟩ := legalSeedSpan_exists_hilbert A hA hF
  change Summable (fun n => positiveWeight n * F n ^ 2)
  rw [← hseq]
  exact hilbertSequence_square_summable f

theorem residueFraction_mem_legal (d : ℕ) (hd : 0 < d) :
    residueFraction d ∈ legalSeedSpan allPositiveSeeds := by
  have h : Pareto.residue d ∈ legalSeedSpan allPositiveSeeds := by
    simpa only [dilation_one] using
      (dilation_generator_mem allPositiveSeeds (a := d) (m := 1) hd (by norm_num))
  have he : (1 / (d : ℝ)) • Pareto.residue d = residueFraction d := by
    funext n
    simp [residueFraction, Pareto.residue, div_eq_mul_inv, mul_comm]
  rw [← he]
  exact (legalSeedSpan allPositiveSeeds).smul_mem (1 / (d : ℝ)) h

theorem finite_residue_correction_mem (s : Finset ℕ) (t : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d) :
    (fun n => ∑ d ∈ s, t d * residueFraction d n) ∈
      legalSeedSpan allPositiveSeeds := by
  have h : (∑ d ∈ s, t d • residueFraction d) ∈
      legalSeedSpan allPositiveSeeds := by
    apply Submodule.sum_mem
    intro d hd
    exact (legalSeedSpan allPositiveSeeds).smul_mem (t d)
      (residueFraction_mem_legal d (hs d hd))
  have he : (∑ d ∈ s, t d • residueFraction d) =
      (fun n => ∑ d ∈ s, t d * residueFraction d n) := by
    funext n
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [← he]
  exact h

def corrected (R : ℕ → ℝ) (α : ℝ) (s : Finset ℕ) (t : ℕ → ℝ)
    (n : ℕ) : ℝ := R n - α * n - ∑ d ∈ s, t d * residueFraction d n

theorem corrected_mem_legal (R : ℕ → ℝ) (α : ℝ) (s : Finset ℕ) (t : ℕ → ℝ)
    (hbase : (fun n : ℕ => R n - α * n) ∈ legalSeedSpan allPositiveSeeds)
    (hs : ∀ d ∈ s, 0 < d) :
    corrected R α s t ∈ legalSeedSpan allPositiveSeeds := by
  exact (legalSeedSpan allPositiveSeeds).sub_mem hbase
    (finite_residue_correction_mem s t hs)

/-- A bound on full legal energy and exact positive heads implies actual RH. -/
theorem riemannHypothesis_of_bounded_legal_heads (A : Set ℕ)
    (hA : ∀ d ∈ A, 0 < d) (C : ℝ)
    (h : ∀ N : ℕ, ∃ F : ℕ → ℝ, F ∈ legalSeedSpan A ∧
      (∀ n, 0 < n → n ≤ N → F n = 1) ∧ fullSquaredNorm F ≤ C) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_hilbertOne_mem_legalClosure A hA
  apply hilbertLegalClosure_of_bounded_exact_heads A C
  intro N
  obtain ⟨F, hlegal, hhead, hnorm⟩ := h N
  obtain ⟨f, hf, hseq⟩ := legalSeedSpan_exists_hilbert A hA hlegal
  refine ⟨f, hf, ?_, ?_⟩
  · simpa only [hseq] using hhead
  · rw [hilbert_norm_weighted_sq, hseq]
    exact hnorm

/-- The precise distributed correction target from the conversation.
The moment constraint repairs the head; the independent full-energy hypothesis
is the remaining arithmetic input. -/
theorem bounded_coupled_corrections_imply_RH
    (R : ℕ → ℕ → ℝ) (α : ℕ → ℝ) (C : ℝ)
    (hbase : ∀ y, (fun n : ℕ => R y n - α y * n) ∈
      legalSeedSpan allPositiveSeeds)
    (hhead : ∀ y n, 0 < n → n ≤ y → R y n = 1)
    (hcorrections : ∀ y, ∃ (s : Finset ℕ) (t : ℕ → ℝ),
      (∀ d ∈ s, y < d) ∧ (∑ d ∈ s, t d / (d : ℝ) = -α y) ∧
      fullSquaredNorm (corrected (R y) (α y) s t) ≤ C) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_bounded_legal_heads allPositiveSeeds
    (by intro d hd; exact hd) C
  intro y
  obtain ⟨s, t, hs, hbalance, henergy⟩ := hcorrections y
  refine ⟨corrected (R y) (α y) s t,
    corrected_mem_legal (R y) (α y) s t (hbase y)
      (by intro d hd; exact lt_of_le_of_lt (Nat.zero_le y) (hs d hd)),
    ?_, henergy⟩
  intro n hn hny
  exact coupled_head_repair y n s t (R y) (α y) hny
    (hhead y n hn hny) hs hbalance

end
end RiemannResearch.RH.ArithmeticCumulative
