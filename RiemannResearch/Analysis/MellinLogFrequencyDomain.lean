import RiemannResearch.Analysis.MellinLogStepContinuity
import RiemannResearch.Analysis.FourierFirstMomentContinuity

/-!
# The frequency-multiplication domain excludes nonzero logarithmic step profiles

Source: user-provided Hilbert--Pólya discussion, September 20, 2026.
The Fourier--Sobolev implication is supplied here by the L1 inverse-Fourier
argument in `FourierFirstMomentContinuity`, and the jump obstruction includes
arbitrary continuous representatives. Thus no continuity provider is assumed.
Mathlib's Fourier normalization uses `2π` in the exponential; replacing the
frequency coordinate by `t/(2π)` does not change whether its product is in L2.
-/

noncomputable section
open MeasureTheory FourierTransform

namespace RiemannResearch.Analysis.MellinLogStep

/-- A square-integrable logarithmic step profile whose Fourier transform is
in the multiplication-by-frequency domain must have zero coefficients. -/
theorem eq_zero_of_profile_frequency_memLp
    (f : ℕ → ℂ) (hf0 : f 0 = 0) (hf2 : MemLp (mellinLogProfile f) 2)
    (hFreq : MemLp (fun t : ℝ => (t : ℂ) *
      (𝓕 (hf2.toLp (mellinLogProfile f)) : Lp ℂ 2 (volume : Measure ℝ)) t) 2) :
    f = 0 := by
  obtain ⟨g, hg, heq⟩ := exists_continuous_ae_eq_of_frequency_memLp
    (hf2.toLp (mellinLogProfile f)) hFreq
  exact eq_zero_of_continuous_ae_eq_profile f hf0 g hg
    (heq.trans hf2.coeFn_toLp)

/-- The concrete Mellin step range in the unitary L2 Fourier model. -/
def logStepFourierRange : Set (Lp ℂ 2 (volume : Measure ℝ)) :=
  {F | ∃ (f : ℕ → ℂ) (hf0 : f 0 = 0) (hf2 : MemLp (mellinLogProfile f) 2),
    F = 𝓕 (hf2.toLp (mellinLogProfile f))}

/-- The standard maximal domain of multiplication by the real frequency. -/
def frequencyMultiplicationDomain : Set (Lp ℂ 2 (volume : Measure ℝ)) :=
  {F | MemLp (fun t : ℝ => (t : ℂ) * F t) 2}

/-- The only vector in the step-Mellin range belonging to the maximal
multiplication-by-frequency domain is zero. This proves the domain obstruction
for the full finite-energy step range, not only finite arithmetic spans. -/
theorem eq_zero_of_mem_range_and_frequency_domain
    {F : Lp ℂ 2 (volume : Measure ℝ)} (hRange : F ∈ logStepFourierRange)
    (hDomain : F ∈ frequencyMultiplicationDomain) : F = 0 := by
  obtain ⟨f, hf0, hf2, rfl⟩ := hRange
  have hf := eq_zero_of_profile_frequency_memLp f hf0 hf2 hDomain
  simp [hf]

end RiemannResearch.Analysis.MellinLogStep
