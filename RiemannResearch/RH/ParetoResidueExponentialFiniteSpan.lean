import RiemannResearch.RH.ParetoResidueExponentialLimit

/-!
# Residue exponentials are outside the finite residue span

Source: the user's convolution-exponential legality question, 13 November 2026.
Every finite linear combination of normalized residues is bounded in physical
coordinates, whereas the actual residue exponential is unbounded for every
prime conductor. This concerns the algebraic span; its closure is treated
separately by ParetoPrimeLimitLegality.
-/

noncomputable section
namespace RiemannResearch.RH.Pareto.ConvolutionExponential

open RiemannResearch.NumberTheory.DirichletExponential
open CoefficientStabilization

/-- Finite residue combinations have bounded actual physical coordinates. -/
theorem bounded_physical_sequence_of_mem_atomSpan {f : ThresholdHilbert}
    (hf : f ∈ Submodule.span ℝ (Set.range residueAtom)) :
    ∃ C : ℝ, ∀ n, |hilbertSequence f n| ≤ C := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨i, rfl⟩ := hf
      refine ⟨1, fun n => ?_⟩
      rw [residueAtom, normalizedResidueHilbert_sequence_eq_residueAF]
      exact residueAF_abs_le_one (i + 2) n
  | zero =>
      refine ⟨0, fun n => ?_⟩
      change |hilbertSequenceLinear (0 : ThresholdHilbert) n| ≤ 0
      rw [map_zero]
      simp
  | add f g hf hg ihf ihg =>
      obtain ⟨C, hC⟩ := ihf
      obtain ⟨Cg, hCg⟩ := ihg
      refine ⟨C + Cg, fun n => ?_⟩
      change |hilbertSequenceLinear (f + g) n| ≤ C + Cg
      rw [map_add]
      change |hilbertSequence f n + hilbertSequence g n| ≤ C + Cg
      have hadd : |hilbertSequence f n + hilbertSequence g n| ≤
          |hilbertSequence f n| + |hilbertSequence g n| := by
        simpa only [Real.norm_eq_abs] using
          norm_add_le (hilbertSequence f n) (hilbertSequence g n)
      exact hadd.trans (add_le_add (hC n) (hCg n))
  | smul c f hf ihf =>
      obtain ⟨C, hC⟩ := ihf
      refine ⟨|c| * C, fun n => ?_⟩
      change |hilbertSequenceLinear (c • f) n| ≤ |c| * C
      rw [map_smul]
      change |c * hilbertSequence f n| ≤ |c| * C
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hC n) (abs_nonneg c)

/-- Any actual H realization of the prime residue exponential lies outside
the algebraic residue span. No closed-span nonmembership is asserted. -/
theorem not_mem_atomSpan_of_sequence_eq_residueExp
    {f : ThresholdHilbert} {p : ℕ} (hp : p.Prime)
    (hsequence : hilbertSequence f = convolutionExp (residueAF p)) :
    f ∉ Submodule.span ℝ (Set.range residueAtom) := by
  intro hf
  obtain ⟨C, hC⟩ := bounded_physical_sequence_of_mem_atomSpan hf
  apply residueAF_exp_not_bounded hp
  refine ⟨C, fun n => ?_⟩
  simpa only [hsequence] using hC n

/-- In particular, the explicitly bundled exponential is never a finite
residue combination when its conductor is prime. -/
theorem residueExpHilbert_not_mem_atomSpan {p : ℕ} (hp : p.Prime)
    (h : Summable (fun n => positiveWeight n * convolutionExp (residueAF p) n ^ 2)) :
    residueExpHilbert p h ∉ Submodule.span ℝ (Set.range residueAtom) :=
  not_mem_atomSpan_of_sequence_eq_residueExp hp (residueExpHilbert_sequence p h)

end RiemannResearch.RH.Pareto.ConvolutionExponential
