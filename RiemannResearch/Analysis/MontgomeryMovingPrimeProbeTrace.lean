import RiemannResearch.Analysis.MontgomeryPrimeProbeEnergy

/-! # Moving arithmetic probes and signed actual-zero traces -/

noncomputable section
namespace RiemannResearch.Analysis.MontgomeryPrimeTrace
open Filter MontgomeryPositiveGap
open scoped Topology

/-- Changing from the sine hole to a prime probe with vanishing energy error
preserves the signed comparison along the same width function. -/
theorem movingPrimeProbeTrace_iff_sineHole {q : ℝ → ℝ}
    (he : Tendsto (fun T : ℝ =>
      primeProbeEnergy T (q T) - (q T - sineGapMass (q T))) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => sampledArgumentIncrement T (q T) + primeProbeEnergy T (q T))
        atTop (𝓝 0) ↔
      Tendsto (fun T : ℝ => sampledArgumentIncrement T (q T) + (q T - sineGapMass (q T)))
        atTop (𝓝 0) := by
  constructor
  · intro h
    have h' := h.sub he
    rw [sub_zero] at h'
    apply h'.congr'
    filter_upwards with T
    ring
  · intro h
    have h' := h.add he
    rw [zero_add] at h'
    apply h'.congr'
    filter_upwards with T
    ring

/-- The limit of the arithmetic energy defect shifts the limit required of
the signed increments at a diverging width by precisely its negative. -/
theorem movingPrimeProbeTrace_iff_sampled_limit_of_energyDefect {q : ℝ → ℝ} {δ : ℝ}
    (hq : Tendsto q atTop atTop)
    (he : Tendsto (fun T : ℝ =>
      primeProbeEnergy T (q T) - (q T - sineGapMass (q T))) atTop (𝓝 δ)) :
    Tendsto (fun T : ℝ => sampledArgumentIncrement T (q T) + primeProbeEnergy T (q T))
        atTop (𝓝 0) ↔
      Tendsto (fun T : ℝ => sampledArgumentIncrement T (q T)) atTop (𝓝 (-(1 / 2 + δ))) := by
  have hs : Tendsto (fun T : ℝ => sineGapMass (q T) - q T) atTop (𝓝 (-(1 / 2 : ℝ))) :=
    sineGapMass_sub_id_tendsto_neg_half.comp hq
  have henergy : Tendsto (fun T : ℝ => primeProbeEnergy T (q T)) atTop (𝓝 (1 / 2 + δ)) := by
    have h := he.sub hs
    rw [show δ - (-(1 / 2 : ℝ)) = 1 / 2 + δ by ring] at h
    apply h.congr'
    filter_upwards with T
    ring
  constructor
  · intro h
    simpa only [add_sub_cancel_right, zero_sub] using h.sub henergy
  · intro h
    simpa only [neg_add_cancel] using h.add henergy

/-- At a diverging width with vanishing arithmetic energy error the sampled
right-continuous increments must converge to minus one half. -/
theorem movingPrimeProbeTrace_iff_sampled_neg_half {q : ℝ → ℝ}
    (hq : Tendsto q atTop atTop)
    (he : Tendsto (fun T : ℝ =>
      primeProbeEnergy T (q T) - (q T - sineGapMass (q T))) atTop (𝓝 0)) :
    Tendsto (fun T : ℝ => sampledArgumentIncrement T (q T) + primeProbeEnergy T (q T))
        atTop (𝓝 0) ↔
      Tendsto (fun T : ℝ => sampledArgumentIncrement T (q T)) atTop (𝓝 (-(1 / 2 : ℝ))) := by
  simpa only [add_zero] using movingPrimeProbeTrace_iff_sampled_limit_of_energyDefect hq he

#print axioms movingPrimeProbeTrace_iff_sineHole
#print axioms movingPrimeProbeTrace_iff_sampled_limit_of_energyDefect
#print axioms movingPrimeProbeTrace_iff_sampled_neg_half

end RiemannResearch.Analysis.MontgomeryPrimeTrace
