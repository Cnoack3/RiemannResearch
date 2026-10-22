import RiemannResearch.RH.DyadicTentFourierSamples
import RiemannResearch.Analysis.ScalarFourierLimit

/-!
# Infinite signed packets of actual dyadic boundary steps

Source: continuation of the user-provided
`FourierTentContinuationVerification20260910(1).md`.
Absolute summability of packet weights supplies a proved cutoff majorant and
permits the exact finite Fourier identity to pass to an infinite packet.
The final dominated-cutoff theorem keeps its arithmetic limit and majorant
hypotheses explicit. It does not assert the full signed zeta-ratio bridge.
-/

namespace RiemannResearch.Analysis
open scoped BigOperators
noncomputable section

/-- Fourier characters preserve the absolute size of each signed weight. -/
theorem norm_signed_fourier_character (w : ℝ) (h : ℤ) (x : UnitAddCircle) :
    ‖(w : ℂ) * fourier h x‖ = |w| := by
  simp [fourier_apply, Circle.norm_coe]

/-- An absolutely summable signed packet has an absolutely summable phase kernel. -/
theorem summable_signed_fourier_packet {α : Type*} (w : α → ℝ)
    (hw : Summable (fun a => |w a|)) (x : α → UnitAddCircle) (h : ℤ) :
    Summable (fun a => (w a : ℂ) * fourier h (x a)) := by
  exact hw.of_norm_bounded (fun a => (norm_signed_fourier_character (w a) h (x a)).le)

/-- Uniform cutoff domination is proved from total absolute weight. -/
theorem norm_finite_signed_fourier_packet_le {α : Type*} (w : α → ℝ)
    (hw : Summable (fun a => |w a|)) (x : α → UnitAddCircle)
    (s : Finset α) (h : ℤ) :
    ‖∑ a ∈ s, (w a : ℂ) * fourier h (x a)‖ ≤ ∑' a, |w a| := by
  calc
    _ ≤ ∑ a ∈ s, ‖(w a : ℂ) * fourier h (x a)‖ := norm_sum_le _ _
    _ = ∑ a ∈ s, |w a| := by simp only [norm_signed_fourier_character]
    _ ≤ _ := hw.sum_le_tsum s (fun a _ => abs_nonneg _)

/-- The full phase kernel has the same cutoff-independent majorant. -/
theorem norm_tsum_signed_fourier_packet_le {α : Type*} (w : α → ℝ)
    (hw : Summable (fun a => |w a|)) (x : α → UnitAddCircle) (h : ℤ) :
    ‖∑' a, (w a : ℂ) * fourier h (x a)‖ ≤ ∑' a, |w a| := by
  calc
    _ ≤ ∑' a, ‖(w a : ℂ) * fourier h (x a)‖ := norm_tsum_le_tsum_norm (by simpa only [norm_signed_fourier_character] using hw)
    _ = _ := by simp only [norm_signed_fourier_character]

end
end RiemannResearch.Analysis

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
open RiemannResearch.Analysis
noncomputable section

/-- The finite packet identity allows any indexing of positive integer dilations. -/
theorem dyadicBoundaryCoordinate_finite_dilation_packet_hasSum_fourier
    {α : Type*} (i : ℕ) (s : Finset α) (m : α → ℕ)
    (hm : ∀ a, 0 < m a) (w : α → ℝ) :
    HasSum (fun h : ℤ => dyadicTentMellinCoefficient i h *
      ∑ a ∈ s, (w a : ℂ) *
        fourier h ((Real.log (m a : ℝ) / Real.log 2 : ℝ) : UnitAddCircle))
      (∑ a ∈ s, (w a : ℂ) *
        (dyadicBoundaryCoordinate (dyadicProjectedStep (m a) (hm a)) i : ℂ)) := by
  have hs := hasSum_sum (s := s) (fun a _ =>
    HasSum.mul_left (w a : ℂ)
      (dyadicBoundaryCoordinate_step_hasSum_fourier i (m a) (hm a)))
  have hf : (fun h : ℤ => ∑ a ∈ s, (w a : ℂ) *
      (dyadicTentMellinCoefficient i h *
        fourier h ((Real.log (m a : ℝ) / Real.log 2 : ℝ) : UnitAddCircle))) =
      (fun h : ℤ => dyadicTentMellinCoefficient i h *
        ∑ a ∈ s, (w a : ℂ) *
          fourier h ((Real.log (m a : ℝ) / Real.log 2 : ℝ) : UnitAddCircle)) := by
    funext h
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  simpa only [hf] using hs

/-- Exact infinite signed-packet Fourier expansion, with both orders justified
by the product of the two absolute summability bounds. -/
theorem dyadicBoundaryCoordinate_summable_dilation_packet_hasSum_fourier
    {α : Type*} (i : ℕ) (m : α → ℕ) (hm : ∀ a, 0 < m a)
    (w : α → ℝ) (hw : Summable (fun a => |w a|)) :
    HasSum (fun h : ℤ => dyadicTentMellinCoefficient i h *
      ∑' a, (w a : ℂ) *
        fourier h ((Real.log (m a : ℝ) / Real.log 2 : ℝ) : UnitAddCircle))
      (∑' a, (w a : ℂ) *
        (dyadicBoundaryCoordinate (dyadicProjectedStep (m a) (hm a)) i : ℂ)) := by
  let x : α → UnitAddCircle := fun a =>
    ((Real.log (m a : ℝ) / Real.log 2 : ℝ) : UnitAddCircle)
  let f : α → ℤ → ℂ := fun a h =>
    (w a : ℂ) * (dyadicTentMellinCoefficient i h * fourier h (x a))
  have hmajor := hw.mul_of_nonneg (summable_norm_dyadicTentMellinCoefficient i)
    (fun a => abs_nonneg _) (fun h => norm_nonneg _)
  have hf : Summable (Function.uncurry f) := by
    apply hmajor.of_norm_bounded
    intro p
    simp [f, Function.uncurry, fourier_apply, Circle.norm_coe]
  have hrow := summable_norm_dyadicTentMellinCoefficient_mul_of_bounded i
    (fun h => ∑' a, (w a : ℂ) * fourier h (x a)) (∑' a, |w a|)
    (norm_tsum_signed_fourier_packet_le w hw x)
  apply hrow.of_norm.hasSum_iff.mpr
  calc
    _ = ∑' h, ∑' a, f a h := by
      apply tsum_congr
      intro h
      rw [← tsum_mul_left]
      apply tsum_congr
      intro a
      dsimp [f]
      ring
    _ = ∑' a, ∑' h, f a h := hf.tsum_comm
    _ = _ := by
      apply tsum_congr
      intro a
      exact (HasSum.mul_left (w a : ℂ)
        (dyadicBoundaryCoordinate_step_hasSum_fourier i (m a) (hm a))).tsum_eq

/-- Concrete instantiation of scalar Tannery with the actual finite signed
packet identity. The only remaining hypotheses concern cutoff domination,
individual arithmetic kernel limits, and the physical coordinate limit. -/
theorem dyadicBoundaryCoordinate_hasSum_fourier_of_dominated_packets
    (i : ℕ) (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ)
    (d : ℤ → ℂ) (B : ℤ → ℝ) (a : ℂ)
    (hB : Summable (fun h => ‖dyadicTentMellinCoefficient i h‖ * B h))
    (hD : ∀ n h, ‖∑ m ∈ s n, (w n m : ℂ) *
      fourier h ((Real.log ((m+1:ℕ):ℝ) / Real.log 2 : ℝ) : UnitAddCircle)‖ ≤ B h)
    (hd : ∀ h, Filter.Tendsto (fun n => ∑ m ∈ s n, (w n m : ℂ) *
      fourier h ((Real.log ((m+1:ℕ):ℝ) / Real.log 2 : ℝ) : UnitAddCircle))
      Filter.atTop (nhds (d h)))
    (ha : Filter.Tendsto (fun n => ∑ m ∈ s n, (w n m : ℂ) *
      (dyadicBoundaryCoordinate (dyadicProjectedStep (m+1) (by positivity)) i : ℂ))
      Filter.atTop (nhds a)) :
    HasSum (fun h => dyadicTentMellinCoefficient i h * d h) a := by
  apply hasSum_fourier_kernel_limit_of_actual_approximation
    (dyadicTentMellinCoefficient i) _ d B hB hD hd _ a _ ha
  intro n
  exact (dyadicBoundaryCoordinate_finite_signed_packet_hasSum_fourier i (s n) (w n)).tsum_eq.symm

end
end RiemannResearch.RH.Pareto
