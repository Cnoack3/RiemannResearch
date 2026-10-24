import RiemannResearch.Analysis.WeightedCoordinateEnergy
import RiemannResearch.Analysis.NonnegativeErrorConvergence
import Mathlib.Analysis.Normed.Group.Continuity

/-!
# The common bounded-set topology of positive admissible observation weights

Source: weighted coordinate domination and Tannery's theorem, sixth transfer
program, 24 October 2026. Vanishing energy forces every observed coordinate
to vanish without any boundedness premise. The converse needs only eventual
boundedness of the complete physical error, along an arbitrary filter.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.Analysis.WeightedCoordinateTopology
open WeightedCoordinateEnergy NonnegativeErrorConvergence
variable {H α ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {l : Filter α}

/-- No boundedness hypothesis is required in this direction. -/
theorem coordinates_tendsto_of_energy_zero
    (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ) (hw : ∀ j, 0 < w j)
    (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2)) (F : α → H) (x : H)
    (he : Tendsto (fun i => observationEnergy w ℓ (F i - x)) l (𝓝 0)) :
    ∀ j, Tendsto (fun i => ℓ j (F i)) l (𝓝 (ℓ j x)) := by
  intro j
  have hdiv : Tendsto (fun i => observationEnergy w ℓ (F i - x) / w j) l (𝓝 0) := by
    simpa only [zero_div] using he.div_const (w j)
  have hsq : Tendsto (fun i => (ℓ j (F i - x)) ^ 2) l (𝓝 0) := by
    apply squeeze_zero (fun i => sq_nonneg _) _ hdiv
    intro i
    apply (le_div_iff₀ (hw j)).mpr
    simpa only [mul_comm] using
      observation_summand_le w ℓ (fun j => (hw j).le) hs (F i - x) j
  have hn : Tendsto (fun i => ‖ℓ j (F i - x)‖) l (𝓝 0) := by
    apply (norm_zero_iff_square (l := l) (fun i => ℓ j (F i - x))).mpr
    simpa only [Real.norm_eq_abs, sq_abs] using hsq
  have hzero := tendsto_zero_iff_norm_tendsto_zero.mpr hn
  have hadd := hzero.add_const (ℓ j x)
  simpa only [map_sub, sub_add_cancel, zero_add] using hadd

/-- On an eventually bounded physical family, the complete weighted metric
vanishes exactly when every coordinate error does. -/
theorem energy_zero_iff_coordinates
    (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ) (hw : ∀ j, 0 < w j)
    (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2)) (F : α → H) (x : H)
    (B : ℝ) (hbound : ∀ᶠ i in l, ‖F i - x‖ ^ 2 ≤ B) :
    Tendsto (fun i => observationEnergy w ℓ (F i - x)) l (𝓝 0) ↔
      ∀ j, Tendsto (fun i => ℓ j (F i)) l (𝓝 (ℓ j x)) := by
  constructor
  · exact coordinates_tendsto_of_energy_zero w ℓ hw hs F x
  · intro hc
    have hd (j : ι) : Tendsto (fun i => ℓ j (F i - x)) l (𝓝 (ℓ j 0)) := by
      simpa only [map_sub, sub_self, map_zero] using (hc j).sub_const (ℓ j x)
    have he := observationEnergy_tendsto w ℓ (fun j => (hw j).le) hs
      (fun i => F i - x) 0 hd B hbound
    simpa only [observationEnergy, map_zero, zero_pow (by decide : 2 ≠ 0), mul_zero,
      tsum_zero] using he

/-- The bounded-set convergence notion is independent of the positive
admissible weights, without comparison constants between the two weight arrays. -/
theorem positive_weights_same_bounded_topology
    (w u : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 < w j) (hu : ∀ j, 0 < u j)
    (hsw : Summable (fun j => w j * ‖ℓ j‖ ^ 2))
    (hsu : Summable (fun j => u j * ‖ℓ j‖ ^ 2))
    (F : α → H) (x : H) (B : ℝ) (hbound : ∀ᶠ i in l, ‖F i - x‖ ^ 2 ≤ B) :
    Tendsto (fun i => observationEnergy w ℓ (F i - x)) l (𝓝 0) ↔
      Tendsto (fun i => observationEnergy u ℓ (F i - x)) l (𝓝 0) :=
  (energy_zero_iff_coordinates w ℓ hw hsw F x B hbound).trans
    (energy_zero_iff_coordinates u ℓ hu hsu F x B hbound).symm

end RiemannResearch.Analysis.WeightedCoordinateTopology
