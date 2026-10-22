import RiemannResearch.RH.DyadicArithmeticFourierBridge
import RiemannResearch.RH.DyadicNormalizationElementaryBounds
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Zero damping of the actual signed Fourier modes

Source: continuation of the user-provided
`FourierSignedBridgeVerification20260911(2).md`, September 11, 2026.
The actual scalar normalization tends to one. Nonvanishing of zeta on the
line of real part one then gives decay of each nonzero signed mode.
The complete Abel numerator is retained and its uniform bound avoids any
Diophantine assumption about the triadic phase. These results do not justify
passing the limit through an infinite frequency sum or prove uniform energy.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
open Filter RiemannResearch.Analysis
noncomputable section

/-- The original real Dirichlet normalization tends to one from positive damping. -/
theorem dyadicRegularizationNormalization_tendsto_one :
    Tendsto dyadicRegularizationNormalization (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have ht : Tendsto (fun ε : ℝ => ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlo : Tendsto (fun ε : ℝ => 1 - ε * Real.log 3)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa using tendsto_const_nhds.sub (ht.mul_const (Real.log 3))
  have hhi : Tendsto (fun ε : ℝ => 1 + ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa using tendsto_const_nhds.add ht
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
    (eventually_mem_nhdsWithin.mono fun ε hε =>
      (dyadicRegularizationNormalization_elementary_bounds hε).1)
    (eventually_mem_nhdsWithin.mono fun ε hε =>
      (dyadicRegularizationNormalization_elementary_bounds hε).2)

/-- The signed zeta ratio vanishes at each fixed nonzero frequency. -/
theorem dyadicSignedZetaRatio_tendsto_zero (h : DyadicNonzeroFourierFrequency) :
    Tendsto (fun ε : ℝ => dyadicSignedZetaRatio ε h)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  let s : ℂ := 1 - Complex.I * (dyadicLogFrequency h.1 : ℂ)
  have hsre : s.re = 1 := by simp [s]
  have hsone : s ≠ 1 := by
    intro heq
    have him := congrArg Complex.im heq
    have hfreq := dyadicLogFrequency_ne_zero h.2
    simp [s] at him
    exact hfreq him
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by rw [hsre])
  have ht : Tendsto (fun ε : ℝ => (ε : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using Complex.continuous_ofReal.continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0)
  have hs : Tendsto (fun ε : ℝ => 1 + (ε : ℂ) -
      Complex.I * (dyadicLogFrequency h.1 : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds s) := by
    simpa [s] using (tendsto_const_nhds.add ht).sub_const
      (Complex.I * (dyadicLogFrequency h.1 : ℂ))
  have hden := (differentiableAt_riemannZeta hsone).continuousAt.tendsto.comp hs
  have hN : Tendsto (fun ε : ℝ => (dyadicRegularizationNormalization ε : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa only [Function.comp_def, Complex.ofReal_one] using Complex.continuous_ofReal.continuousAt.tendsto.comp
      dyadicRegularizationNormalization_tendsto_one
  simpa [dyadicSignedZetaRatio, s, hz] using
    ((hN.mul_const (riemannZeta s)).div hden hz).sub_const 1

/-- The full signed multiplier is bounded by twice its signed zeta factor. -/
theorem norm_dyadicSignedFourierMultiplier_le {ε : ℝ} (hε : 0 < ε)
    (h : DyadicNonzeroFourierFrequency) :
    ‖dyadicSignedFourierMultiplier ε h‖ ≤ 2 * ‖dyadicSignedZetaRatio ε h‖ := by
  rw [dyadicSignedFourierMultiplier, norm_mul]
  have hb := abelCancellationMultiplier_norm_le_two
    (triadicDampingRatio ε) (dyadicTriadicFourierPhase h.1)
    (triadicDampingRatio_pos ε).le (triadicDampingRatio_lt_one hε)
    (norm_dyadicTriadicFourierPhase h.1)
  nlinarith [norm_nonneg (dyadicSignedZetaRatio ε h)]

/-- Full signed mode decay, with the Abel numerator and denominator intact. -/
theorem dyadicSignedFourierMultiplier_tendsto_zero (h : DyadicNonzeroFourierFrequency) :
    Tendsto (fun ε : ℝ => dyadicSignedFourierMultiplier ε h)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hpos : ∀ᶠ ε : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < ε :=
    eventually_mem_nhdsWithin
  have hlim : Tendsto (fun ε : ℝ => 2 * ‖dyadicSignedZetaRatio ε h‖)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    simpa using (dyadicSignedZetaRatio_tendsto_zero h).norm.const_mul 2
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (hpos.mono fun ε hε => norm_dyadicSignedFourierMultiplier_le hε h) hlim

/-- Every actual signed Fourier term vanishes at fixed coordinate and frequency. -/
theorem dyadicSignedFourierTerm_tendsto_zero (i : ℕ) (h : DyadicNonzeroFourierFrequency) :
    Tendsto (fun ε : ℝ => dyadicSignedFourierTerm ε i h)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  simpa [dyadicSignedFourierTerm] using
    (dyadicSignedFourierMultiplier_tendsto_zero h).const_mul (dyadicTentMellinCoefficient i h.1)

/-- Any fixed finite signed frequency packet vanishes. -/
theorem dyadicSignedFourierPacket_tendsto_zero (i : ℕ)
    (t : Finset DyadicNonzeroFourierFrequency) :
    Tendsto (fun ε : ℝ => ∑ h ∈ t, dyadicSignedFourierTerm ε i h)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  simpa using tendsto_finsetSum t (fun h _ => dyadicSignedFourierTerm_tendsto_zero i h)

/-- Finite boundary and frequency energy vanishes with every cross term retained. -/
theorem dyadicSignedFourierFiniteEnergy_tendsto_zero (s : Finset ℕ)
    (t : Finset DyadicNonzeroFourierFrequency) :
    Tendsto (fun ε : ℝ => ∑ i ∈ s,
      (1 / 4 : ℝ) * ‖∑ h ∈ t, dyadicSignedFourierTerm ε i h‖ ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  simpa using tendsto_finsetSum s (fun i _ =>
    ((dyadicSignedFourierPacket_tendsto_zero i t).norm.pow 2).const_mul (1 / 4 : ℝ))

end
end RiemannResearch.RH.Pareto
