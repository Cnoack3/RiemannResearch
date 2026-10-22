import RiemannResearch.RH.DyadicFourierZeroDamping

/-!
# Exact signed frequency-tail criterion for zero damping

Source: independently developed continuation of the actual signed Fourier
bridge. This criterion retains the complete complex frequency tail. It is a
necessary and sufficient reformulation, not a provider for vanishing tails.
-/

namespace RiemannResearch.RH.Pareto
open Filter
open scoped BigOperators
noncomputable section

/-- The exact signed remainder after a finite frequency packet. At positive
damping the already proved `HasSum` identifies the full sum with the actual
arithmetic boundary coefficient. -/
def dyadicSignedFourierFrequencyTail (ε : ℝ) (i : ℕ)
    (t : Finset DyadicNonzeroFourierFrequency) : ℂ :=
  (∑' h, dyadicSignedFourierTerm ε i h) -
    ∑ h ∈ t, dyadicSignedFourierTerm ε i h

theorem dyadicSignedFourierFrequencyTail_eq_actual
    {ε : ℝ} (hε : 0 < ε) (i : ℕ)
    (t : Finset DyadicNonzeroFourierFrequency) :
    dyadicSignedFourierFrequencyTail ε i t =
      (dyadicNormalizationBoundaryCoefficient ε i : ℂ) -
        ∑ h ∈ t, dyadicSignedFourierTerm ε i h := by
  rw [dyadicSignedFourierFrequencyTail,
    (dyadicSignedFourierBridge_proved ε hε i).tsum_eq]

/-- Exact signed tail-smallness is necessary and sufficient for the row limit.
The cutoff may depend on the requested accuracy, but not on the damping.
This does not replace the signed tail by its absolute or diagonal energy. -/
theorem dyadicSignedFourierRow_tendsto_zero_iff_signed_tails (i : ℕ) :
    Tendsto (fun ε : ℝ => ∑' h, dyadicSignedFourierTerm ε i h)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : ℂ)) ↔
      ∀ η : ℝ, 0 < η → ∃ t : Finset DyadicNonzeroFourierFrequency,
        ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          ‖dyadicSignedFourierFrequencyTail ε i t‖ < η := by
  constructor
  · intro hlim η hη
    refine ⟨∅, ?_⟩
    have h := (Metric.tendsto_nhds.mp hlim) η hη
    simpa only [dyadicSignedFourierFrequencyTail, Finset.sum_empty,
      sub_zero, dist_zero_right] using h
  · intro htail
    apply Metric.tendsto_nhds.mpr
    intro η hη
    obtain ⟨t, ht⟩ := htail (η / 2) (by linarith)
    have hp : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        ‖∑ h ∈ t, dyadicSignedFourierTerm ε i h‖ < η / 2 := by
      simpa only [dist_zero_right] using
        (Metric.tendsto_nhds.mp (dyadicSignedFourierPacket_tendsto_zero i t))
          (η / 2) (by linarith)
    filter_upwards [ht, hp] with ε hεtail hεpacket
    rw [dist_zero_right]
    have hn := norm_add_le
      (dyadicSignedFourierFrequencyTail ε i t)
      (∑ h ∈ t, dyadicSignedFourierTerm ε i h)
    simp only [dyadicSignedFourierFrequencyTail, sub_add_cancel] at hn
    dsimp only [dyadicSignedFourierFrequencyTail] at hεtail
    linarith

end
end RiemannResearch.RH.Pareto
