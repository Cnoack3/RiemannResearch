import RiemannResearch.Analysis.LatePulseDetection
import RiemannResearch.RH.ConditionalPulsePairing
import RiemannResearch.RH.ThreeGeneratorCorrection

set_option autoImplicit false
/-!
# Unconditional strict improvement by three residue generators

Source: user-provided three-generator strict-improvement argument.
The existence of a nonzero correlation is proved for each actual finite
mean-zero legal witness; it is not a premise of the endpoint theorem.
This qualitative result supplies no uniform positive lower bound on the gain.
-/
noncomputable section
open Filter
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.RH.CRTBlock
open RiemannResearch.RH.Pareto RiemannResearch.RH.ArithmeticCumulative
open RiemannResearch.Analysis RiemannResearch.Analysis.Cesaro
open RiemannResearch.Probability.ConditionalIID

/-- Every exact nonempty mean-zero legal head is detected by a late three-generator direction. -/
theorem exists_threeGenerator_correlation_ne_zero (Y : ℕ) (hY : 0 < Y)
    (F : ℕ → ℝ) (hF : F ∈ zeroMeanHeadClass Y) :
    ∃ d : ℕ, Y < d ∧ conditionalMeanInner F (threeGeneratorDirection d) ≠ 0 := by
  obtain ⟨f, _, hseq⟩ := legalSeedSpan_exists_hilbert (Set.Ici 1)
    (by intro a ha; exact ha) hF.1.1
  obtain ⟨Q, hQ, hper, hm⟩ := hF.2
  let g := cesaroOperator f
  have hmoment := cesaroOperator_firstMoment_of_zeroMean f F hseq Q hQ hper hm
  have hsum := cesaroDualTail_summable_of_firstMoment g hmoment
  have hlim := cesaroDualTail_weighted_tendsto_of_firstMoment g hmoment
  have hnonzero : ∃ d : ℕ, Y < d ∧ cesaroDualTail g d ≠ 0 := by
    by_contra h
    push Not at h
    have htail : ∀ t : ℕ, Y < t → cesaro F t = 0 := by
      intro t ht
      have htpos : 0 < t := by omega
      have he := cesaroDualTail_second_difference g t htpos
      rw [h t ht, h (t+1) (by omega), h (t+2) (by omega)] at he
      have hc : conditionalSequence g t = cesaro F t := by
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt htpos)
        simp only [g, conditionalSequence_cesaroOperator, hseq]
      rw [hc] at he
      have hw : 0 < mixtureWeight t / (t : ℝ) := by
        unfold mixtureWeight
        positivity
      exact (mul_eq_zero.mp (by linarith : mixtureWeight t / (t : ℝ) * cesaro F t = 0)).resolve_left
        (ne_of_gt hw)
    have hz := legalSeedSpan_eq_zero_of_cesaro_tail (Set.Ici 1)
      (by intro a ha; exact ha) hF.1.1 Y htail
    have hone := hF.1.2 1 (by omega) hY
    rw [hz] at hone
    norm_num at hone
  obtain ⟨d, hd, hdet⟩ := exists_binary_grouped_ne_zero hsum (cesaroDualTail_zero g)
    hlim Y hnonzero
  have hp : ∃ d : ℕ, Y < d ∧ conditionalMeanInner F (meanPulse d) ≠ 0 := by
    refine ⟨d, hd, ?_⟩
    have he := conditionalPulsePair_eq_grouped g d (by omega)
    rw [show g = cesaroOperator f from rfl, conditionalPulsePair_cesaroOperator, hseq] at he
    exact he.symm ▸ hdet
  obtain ⟨d, hd, hdiff⟩ := exists_ne_double_on_tail_of_tendsto_zero
    (conditionalMeanInner_meanPulse_tendsto_zero F hF.1.1) Y hp
  refine ⟨d, hd, ?_⟩
  have hdpos : 0 < d := by omega
  have hW : threeGeneratorDirection d =
      (fun n => meanPulse d n + (-1 : ℝ)*meanPulse (2*d) n) := by
    funext n
    unfold threeGeneratorDirection
    ring
  rw [hW, conditionalMeanInner_add_mul_right F (meanPulse d) (meanPulse (2*d))
    hF.1.1 (meanPulse_legal d hdpos) (meanPulse_legal (2*d) (by omega)) (-1)]
  simpa only [neg_one_mul, sub_eq_add_neg] using hdiff

/-- An actual finite mean-zero witness always admits a strict three-generator
improvement, preserving every prescribed head value. -/
theorem exists_threeGenerator_strict_improvement (Y : ℕ) (hY : 0 < Y)
    (F : ℕ → ℝ) (hF : F ∈ zeroMeanHeadClass Y) :
    ∃ d : ℕ, Y < d ∧
      let u := -conditionalMeanInner F (threeGeneratorDirection d) /
        conditionalMeanSquare (threeGeneratorDirection d)
      let G := fun n => F n + u*threeGeneratorDirection d n
      G ∈ zeroMeanHeadClass Y ∧
        conditionalMeanSquare G = conditionalMeanSquare F -
          (conditionalMeanInner F (threeGeneratorDirection d))^2 /
            conditionalMeanSquare (threeGeneratorDirection d) ∧
        conditionalMeanSquare G < conditionalMeanSquare F := by
  obtain ⟨d, hd, hi⟩ := exists_threeGenerator_correlation_ne_zero Y hY F hF
  exact ⟨d, hd, threeGenerator_strict_improvement_of_correlation Y d hd F hF hi⟩

end RiemannResearch.RH.CRTBlock
