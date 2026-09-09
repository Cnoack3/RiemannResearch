import RiemannResearch.RH.DilationWaveletClosure
import RiemannResearch.RH.ThresholdHilbertMean
import RiemannResearch.RH.ParetoResidueMoments

/-!
# An actual legal mean-one seed and binary wavelet means

Source: RH_Contracting_Evolution_and_Arithmetic_Repair_2026-09-08.md.
The logarithmic first moment is the previously proved complete infinite
Pareto residue sum. The new normalization is a genuine finite legal vector.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

theorem paretoMean_digit_two (m : ℕ) (hm : 0 < m) :
    paretoMean (digitSequence 2 m) = Real.log 2 / m := by
  have he : digitSequence 2 m = rawPullback m (residue 2) := by
    funext k
    rfl
  rw [he, paretoMean_rawPullback (residue_abs_le 2 · (by norm_num)) m hm,
    paretoMean_residue_two]
  simp [residue]

theorem hilbert_mean_digit_two (m : ℕ) (hm : 0 < m) :
    inner ℝ (digitHilbert 2 m (by norm_num) hm) hilbertOne = Real.log 2 / m := by
  rw [hilbert_inner_one, hilbertSequence_digitHilbert, paretoMean_digit_two m hm]

/-- The weighted wavelet mean is nonzero, despite its zero period mean. -/
theorem hilbert_mean_binary_wavelet (m : ℕ) (hm : 0 < m) :
    inner ℝ (dilationWaveletHilbert 2 m (by norm_num) hm) hilbertOne =
      Real.log 2 / (2 * m) := by
  rw [dilationWaveletHilbert, inner_sub_left, hilbert_mean_digit_two,
    hilbert_mean_digit_two]
  push_cast
  ring

def initialLegalMeanOne : ThresholdHilbert :=
  (1 / Real.log 2) • digitHilbert 2 1 (by norm_num) Nat.zero_lt_one

theorem initialLegalMeanOne_mean : inner ℝ initialLegalMeanOne hilbertOne = 1 := by
  rw [initialLegalMeanOne, real_inner_smul_left, hilbert_mean_digit_two]
  norm_num [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]

theorem initialLegalMeanOne_legal :
    initialLegalMeanOne ∈ hilbertLegalSubspace {2, 3} := by
  apply (hilbertLegalSubspace {2, 3}).smul_mem
  change hilbertSequence (digitHilbert 2 1 (by norm_num) Nat.zero_lt_one) ∈
    legalSeedSpan {2, 3}
  rw [hilbertSequence_digitHilbert, digitSequence_eq_scaled_generator 2 1 Nat.zero_lt_one]
  exact (legalSeedSpan {2, 3}).smul_mem _
    (dilation_generator_mem {2, 3} (by simp) Nat.zero_lt_one)

end
end RiemannResearch.RH.Pareto
