import RiemannResearch.RH.ThresholdHilbertLegal
import RiemannResearch.RH.ThresholdHilbertMean
import RiemannResearch.RH.ThresholdLegalIntegrability
import RiemannResearch.RH.ParetoApproximationRatio
import RiemannResearch.RH.ThresholdRiemannHypothesis
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Tactic.Linarith

/-!
# Legal Pareto approximation, noise/signal ratios, and actual Hilbert closure

Source: RH_Candid_Assessment_Pareto_Green_CRT_2026-09-07.md, sections 3 and 9.
These are exact equivalences between concrete approximation formulations.
They do not assert an approximating sequence or the classical RH equivalence.
All positive integer dilations remain available in `legalSeedSpan`.
The final corollary connects the ratio approximation property to actual RH
using the proved Mellin separation theorem. It does not assume an RH bridge.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- The full Hilbert distance is exactly the full Pareto squared error.
The zero coordinate carries zero mass and every positive coordinate remains. -/
theorem hilbertOne_sub_norm_sq_eq_paretoError (f : ThresholdHilbert) :
    ‖hilbertOne - f‖ ^ 2 = paretoError (hilbertSequence f) := by
  rw [hilbert_norm_weighted_sq]
  have hseq : hilbertSequence (hilbertOne - f) =
      hilbertSequence hilbertOne - hilbertSequence f :=
    hilbertSequenceLinear.map_sub hilbertOne f
  rw [hseq, hilbertOne_sequence]
  unfold paretoError paretoInner
  apply tsum_congr
  intro k
  by_cases hk : k = 0
  · subst k
    simp [positiveWeight]
  · simp [zeroAnchor, hk, pow_two]

/-- Every finite legal physical sequence is realized by an actual Hilbert
vector; boundedness and the zero convention follow from legal synthesis. -/
theorem legalSeedSpan_exists_hilbert (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    {g : ℕ → ℝ} (hg : g ∈ legalSeedSpan A) :
    ∃ f : ThresholdHilbert, f ∈ hilbertLegalSubspace A ∧ hilbertSequence f = g := by
  obtain ⟨C, hC⟩ := legalSeedSpan_bounded A hA hg
  have hs : Summable (fun k => positiveWeight k * g k ^ 2) := by
    simpa only [pow_two] using weighted_summable_of_bounded (bounded_product hC hC)
  obtain ⟨f, hf⟩ := (hilbertSequence_range g).2
    ⟨legalSeedSpan_zero_value A hg, hs⟩
  refine ⟨f, ?_, hf⟩
  change hilbertSequence f ∈ legalSeedSpan A
  rw [hf]
  exact hg

/-- Arbitrarily small error of finite legal sequences is exactly membership
of the actual target in the legal closure for the weighted Hilbert norm. -/
theorem hilbertOne_mem_legalClosure_iff_paretoError
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) :
    hilbertOne ∈ hilbertLegalClosure A ↔
      ∀ ε : ℝ, 0 < ε → ∃ g : ℕ → ℝ,
        g ∈ legalSeedSpan A ∧ paretoError g < ε := by
  constructor
  · intro h ε hε
    change hilbertOne ∈ closure (hilbertLegalSubspace A : Set ThresholdHilbert) at h
    obtain ⟨f, hf, hdist⟩ := Metric.mem_closure_iff.mp h
      (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
    refine ⟨hilbertSequence f, hf, ?_⟩
    rw [← hilbertOne_sub_norm_sq_eq_paretoError]
    have hn : ‖hilbertOne - f‖ < Real.sqrt ε := by
      simpa only [dist_eq_norm] using hdist
    nlinarith [norm_nonneg (hilbertOne - f), Real.sqrt_pos.mpr hε,
      Real.sq_sqrt (le_of_lt hε)]
  · intro h
    change hilbertOne ∈ closure (hilbertLegalSubspace A : Set ThresholdHilbert)
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨g, hg, herr⟩ := h (ε ^ 2) (sq_pos_of_pos hε)
    obtain ⟨f, hf, hseq⟩ := legalSeedSpan_exists_hilbert A hA hg
    refine ⟨f, hf, ?_⟩
    have hn : ‖hilbertOne - f‖ ^ 2 < ε ^ 2 := by
      rwa [hilbertOne_sub_norm_sq_eq_paretoError, hseq]
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (hilbertOne - f)]

/-- The noise/signal formulation has the same target and the same legal
space. Boundedness of each finite legal sequence is proved internally. -/
theorem hilbertOne_mem_legalClosure_iff_noiseSignalRatio
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a) :
    hilbertOne ∈ hilbertLegalClosure A ↔
      ∀ ε : ℝ, 0 < ε → ∃ g : ℕ → ℝ,
        g ∈ legalSeedSpan A ∧ paretoMean g ≠ 0 ∧ noiseSignalRatio g < ε := by
  rw [hilbertOne_mem_legalClosure_iff_paretoError A hA]
  have hratio := arbitrarily_small_error_iff_noiseSignalRatio
    (fun g => g ∈ legalSeedSpan A)
    (fun g hg c => (legalSeedSpan A).smul_mem c hg)
  constructor
  · intro h ε hε
    have he : ∀ δ : ℝ, 0 < δ → ∃ g C,
        (∀ k, |g k| ≤ C) ∧ g ∈ legalSeedSpan A ∧ paretoError g < δ := by
      intro δ hδ
      obtain ⟨g, hg, herr⟩ := h δ hδ
      obtain ⟨C, hC⟩ := legalSeedSpan_bounded A hA hg
      exact ⟨g, C, hC, hg, herr⟩
    obtain ⟨g, C, hC, hg, hm, herr⟩ := hratio.mp he ε hε
    exact ⟨g, hg, hm, herr⟩
  · intro h ε hε
    have hr : ∀ δ : ℝ, 0 < δ → ∃ g C,
        (∀ k, |g k| ≤ C) ∧ g ∈ legalSeedSpan A ∧
          paretoMean g ≠ 0 ∧ noiseSignalRatio g < δ := by
      intro δ hδ
      obtain ⟨g, hg, hm, herr⟩ := h δ hδ
      obtain ⟨C, hC⟩ := legalSeedSpan_bounded A hA hg
      exact ⟨g, C, hC, hg, hm, herr⟩
    obtain ⟨g, C, hC, hg, herr⟩ := hratio.mpr hr ε hε
    exact ⟨g, hg, herr⟩

/-- For two prime seeds, the approximation class is exactly the sum of
packet spans divisible by either seed. Other prime factors remain unrestricted. -/
theorem hilbertOne_mem_prime_pair_closure_iff_packet_noiseSignalRatio
    (p r : ℕ) (hp : p.Prime) (hr : r.Prime) :
    hilbertOne ∈ hilbertLegalClosure {p, r} ↔
      ∀ ε : ℝ, 0 < ε → ∃ g : ℕ → ℝ,
        g ∈ primePacketSpan p ⊔ primePacketSpan r ∧
          paretoMean g ≠ 0 ∧ noiseSignalRatio g < ε := by
  have hpos : ∀ a ∈ ({p, r} : Set ℕ), 0 < a := by
    intro a ha
    rcases Set.mem_insert_iff.mp ha with ha | ha
    · simpa only [ha] using hp.pos
    · simpa only [Set.mem_singleton_iff.mp ha] using hr.pos
  rw [hilbertOne_mem_legalClosure_iff_noiseSignalRatio {p, r} hpos,
    legalSeedSpan_prime_pair p r hp hr]

/-- Arbitrarily small complete noise/signal ratios among finite legal
syntheses suffice for the actual Riemann hypothesis. The Mellin separation
and closure-to-RH implication are proved dependencies; only the arithmetic
approximation property is an input. No convergence rate is required. -/
theorem riemannHypothesis_of_legal_noiseSignalRatio
    (A : Set ℕ) (hA : ∀ a ∈ A, 0 < a)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ g : ℕ → ℝ,
      g ∈ legalSeedSpan A ∧ paretoMean g ≠ 0 ∧ noiseSignalRatio g < ε) :
    RiemannHypothesis :=
  riemannHypothesis_of_hilbertOne_mem_legalClosure A hA
    ((hilbertOne_mem_legalClosure_iff_noiseSignalRatio A hA).mpr happrox)

end
end RiemannResearch.RH.Pareto
