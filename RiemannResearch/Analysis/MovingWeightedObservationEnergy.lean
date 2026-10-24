import RiemannResearch.Analysis.WeightedCoordinateEnergy
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Signed moving observation weights with one complete summable majorant

Source: exact splitting and dominated convergence, sixth transfer program,
24 October 2026. Finite-stage weights may be signed. The limiting positive
weights, rather than positivity of every approximating row, determine the
limiting kernel. Every signed change of weight and state remains in the
exact identity.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.MovingWeightedObservationEnergy
open WeightedCoordinateEnergy
variable {H α ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem signed_observation_summable (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hs : Summable (fun j => |w j| * ‖ℓ j‖ ^ 2)) (x : H) :
    Summable (fun j => w j * (ℓ j x) ^ 2) := by
  apply (hs.mul_right (‖x‖ ^ 2)).of_norm_bounded
  intro j
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (ℓ j x))]
  exact observation_summand_bound (fun j => |w j|) ℓ (fun j => abs_nonneg _) x j

/-- Exact full signed decomposition of simultaneous weight and state changes. -/
theorem weight_state_difference_exact (u w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hu : Summable (fun j => |u j| * ‖ℓ j‖ ^ 2))
    (hw : Summable (fun j => |w j| * ‖ℓ j‖ ^ 2)) (x y : H) :
    observationEnergy u ℓ x - observationEnergy w ℓ y =
      (∑' j, (u j - w j) * (ℓ j x) ^ 2) +
      ∑' j, w j * ((ℓ j x) ^ 2 - (ℓ j y) ^ 2) := by
  have hux := signed_observation_summable u ℓ hu x
  have hwx := signed_observation_summable w ℓ hw x
  have hwy := signed_observation_summable w ℓ hw y
  have h₁ : (∑' j, (u j - w j) * (ℓ j x) ^ 2) =
      observationEnergy u ℓ x - observationEnergy w ℓ x := by
    unfold observationEnergy
    rw [← hux.tsum_sub hwx]
    apply tsum_congr
    intro j
    ring
  have h₂ : (∑' j, w j * ((ℓ j x) ^ 2 - (ℓ j y) ^ 2)) =
      observationEnergy w ℓ x - observationEnergy w ℓ y := by
    unfold observationEnergy
    rw [← hwx.tsum_sub hwy]
    apply tsum_congr
    intro j
    ring
  rw [h₁, h₂]
  ring

theorem moving_energy_tendsto {l : Filter α}
    (W : α → ι → ℝ) (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hweight : ∀ j, Tendsto (fun i => W i j) l (𝓝 (w j)))
    (a : ι → ℝ) (ha : ∀ j, 0 ≤ a j) (hs : Summable a)
    (hdom : ∀ᶠ i in l, ∀ j, |W i j| * ‖ℓ j‖ ^ 2 ≤ a j)
    (F : α → H) (x : H)
    (hcoord : ∀ j, Tendsto (fun i => ℓ j (F i)) l (𝓝 (ℓ j x)))
    (B : ℝ) (hbound : ∀ᶠ i in l, ‖F i‖ ^ 2 ≤ B) :
    Tendsto (fun i => observationEnergy (W i) ℓ (F i)) l (𝓝 (observationEnergy w ℓ x)) := by
  apply tendsto_tsum_of_dominated_convergence (hs.mul_right B)
  · intro j
    exact (hweight j).mul ((hcoord j).pow 2)
  · filter_upwards [hdom, hbound] with i hi hb j
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (ℓ j (F i)))]
    exact (observation_summand_bound (fun j => |W i j|) ℓ
      (fun j => abs_nonneg _) (F i) j).trans
      (mul_le_mul (hi j) hb (sq_nonneg _) (ha j))

/-- Admissibility of the positive limiting weights is derived from the
same eventual majorant; it need not be supplied separately. -/
theorem limit_moment_summable {l : Filter α} [NeBot l]
    (W : α → ι → ℝ) (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hweight : ∀ j, Tendsto (fun i => W i j) l (𝓝 (w j)))
    (hw : ∀ j, 0 ≤ w j) (a : ι → ℝ) (hs : Summable a)
    (hdom : ∀ᶠ i in l, ∀ j, |W i j| * ‖ℓ j‖ ^ 2 ≤ a j) :
    Summable (fun j => w j * ‖ℓ j‖ ^ 2) := by
  apply Summable.of_nonneg_of_le (fun j => mul_nonneg (hw j) (sq_nonneg _)) _ hs
  intro j
  have ht := ((hweight j).abs).mul_const (‖ℓ j‖ ^ 2)
  have h := le_of_tendsto ht (hdom.mono (fun i hi => hi j))
  simpa only [abs_of_nonneg (hw j)] using h

end RiemannResearch.Analysis.MovingWeightedObservationEnergy
