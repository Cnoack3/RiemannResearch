import RiemannResearch.RH.ParetoHiddenNoiseMoments
import RiemannResearch.Analysis.HalfHarmonicLog

/-! Complete logarithmic moment bounds for the actual hidden-noise family.
Source: arithmetic-repair report, §6. The bounds hold for every n ≥ 3. -/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

theorem hiddenNoise_secondMoment_log_bound (n : ℕ) (hn : 3 ≤ n) :
    |paretoInner (hiddenNoise n) (hiddenNoise n) - 2 * Real.log n| ≤ 18 := by
  have hh := RiemannResearch.Analysis.half_harmonic_sub_log_abs_le_one n hn
  have he := hiddenNoise_secondMoment_harmonic_bound n hn
  obtain ⟨hhl, hhu⟩ := abs_le.mp hh
  obtain ⟨hel, heu⟩ := abs_le.mp he
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem hiddenNoise_firstMoment_log_bound (n : ℕ) (hn : 3 ≤ n) :
    |(n : ℝ) * paretoMean (fun k => |hiddenNoise n k|) -
      2 * Real.log n| ≤ 18 := by
  have hh := RiemannResearch.Analysis.half_harmonic_sub_log_abs_le_one n hn
  have he := hiddenNoise_firstMoment_harmonic_bound n hn
  obtain ⟨hhl, hhu⟩ := abs_le.mp hh
  obtain ⟨hel, heu⟩ := abs_le.mp he
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end
end RiemannResearch.RH.Pareto
