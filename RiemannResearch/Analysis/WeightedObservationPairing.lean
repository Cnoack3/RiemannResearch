import RiemannResearch.Analysis.WeightedCoordinateEnergy
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Full signed pairing of admissible weighted observations

Source: standard polarization and finite Cauchy--Schwarz, developed for
Ramanujan conductor observations, sixth transfer program, 24 October 2026.
The complete signed mixed series is retained before any absolute-value
estimate. No orthogonality of the observation functionals is required.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.WeightedObservationPairing
open WeightedCoordinateEnergy
variable {H ι : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

def pairing (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ) (x y : H) : ℝ :=
  ∑' j, w j * (ℓ j x) * (ℓ j y)

theorem pairing_summable (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2)) (x y : H) :
    Summable (fun j => w j * (ℓ j x) * (ℓ j y)) := by
  have h := ((observation_summable w ℓ hw hs (x + y)).sub
    (observation_summable w ℓ hw hs (x - y))).mul_left (1 / 4 : ℝ)
  apply h.congr
  intro j
  simp only [map_add, map_sub]
  ring

theorem pairing_symm (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ) (x y : H) :
    pairing w ℓ x y = pairing w ℓ y x := by
  apply tsum_congr
  intro j
  ring

theorem pairing_self (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ) (x : H) :
    pairing w ℓ x x = observationEnergy w ℓ x := by
  apply tsum_congr
  intro j
  ring

theorem energy_add_exact (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2)) (x y : H) :
    observationEnergy w ℓ (x + y) = observationEnergy w ℓ x +
      observationEnergy w ℓ y + 2 * pairing w ℓ x y := by
  have hx := observation_summable w ℓ hw hs x
  have hy := observation_summable w ℓ hw hs y
  have hp := pairing_summable w ℓ hw hs x y
  unfold observationEnergy pairing
  calc
    _ = ∑' j, ((w j * (ℓ j x) ^ 2 + w j * (ℓ j y) ^ 2) +
      2 * (w j * (ℓ j x) * (ℓ j y))) := by
        apply tsum_congr
        intro j
        simp only [map_add]
        ring
    _ = _ := by rw [(hx.add hy).tsum_add (hp.mul_left 2), hx.tsum_add hy, tsum_mul_left]

theorem energy_sub_exact (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2)) (x y : H) :
    observationEnergy w ℓ (x - y) = observationEnergy w ℓ x +
      observationEnergy w ℓ y - 2 * pairing w ℓ x y := by
  have hx := observation_summable w ℓ hw hs x
  have hy := observation_summable w ℓ hw hs y
  have hp := pairing_summable w ℓ hw hs x y
  unfold observationEnergy pairing
  calc
    _ = ∑' j, ((w j * (ℓ j x) ^ 2 + w j * (ℓ j y) ^ 2) -
      2 * (w j * (ℓ j x) * (ℓ j y))) := by
        apply tsum_congr
        intro j
        simp only [map_sub]
        ring
    _ = _ := by rw [(hx.add hy).tsum_sub (hp.mul_left 2), hx.tsum_add hy, tsum_mul_left]

theorem pairing_polarization (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2)) (x y : H) :
    4 * pairing w ℓ x y = observationEnergy w ℓ (x + y) - observationEnergy w ℓ (x - y) := by
  rw [energy_add_exact w ℓ hw hs, energy_sub_exact w ℓ hw hs]
  ring

/-- Sharp Cauchy--Schwarz for the complete signed observation pairing. -/
theorem pairing_sq_le (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2)) (x y : H) :
    (pairing w ℓ x y) ^ 2 ≤ observationEnergy w ℓ x * observationEnergy w ℓ y := by
  classical
  have hp := (pairing_summable w ℓ hw hs x y).hasSum
  have hx := (observation_summable w ℓ hw hs x).hasSum
  have hy := (observation_summable w ℓ hw hs y).hasSum
  change Tendsto (fun A : Finset ι => ∑ j ∈ A, w j * (ℓ j x) * (ℓ j y))
    atTop (𝓝 (pairing w ℓ x y)) at hp
  change Tendsto (fun A : Finset ι => ∑ j ∈ A, w j * (ℓ j x) ^ 2)
    atTop (𝓝 (observationEnergy w ℓ x)) at hx
  change Tendsto (fun A : Finset ι => ∑ j ∈ A, w j * (ℓ j y) ^ 2)
    atTop (𝓝 (observationEnergy w ℓ y)) at hy
  apply le_of_tendsto_of_tendsto' (hp.pow 2) (hx.mul hy)
  intro A
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul A
    (fun j _ => mul_nonneg (hw j) (sq_nonneg _))
    (fun j _ => mul_nonneg (hw j) (sq_nonneg _))
  intro j hj
  exact le_of_eq (by ring)

/-- The full interpolation law includes its exact curvature, with arbitrary real parameter. -/
theorem energy_affine_exact (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2))
    (x y : H) (t : ℝ) :
    observationEnergy w ℓ ((1 - t) • x + t • y) =
      (1 - t) * observationEnergy w ℓ x + t * observationEnergy w ℓ y -
        t * (1 - t) * observationEnergy w ℓ (x - y) := by
  have hx := observation_summable w ℓ hw hs x
  have hy := observation_summable w ℓ hw hs y
  have hd := observation_summable w ℓ hw hs (x - y)
  unfold observationEnergy
  rw [← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left,
    ← (hx.mul_left (1 - t)).tsum_add (hy.mul_left t),
    ← ((hx.mul_left (1 - t)).add (hy.mul_left t)).tsum_sub (hd.mul_left (t * (1 - t)))]
  apply tsum_congr
  intro j
  simp only [map_add, map_sub, map_smul, smul_eq_mul]
  ring

/-- Signed pairing is zero against every vector exactly on the energy kernel. -/
theorem pairing_annihilates_iff (w : ι → ℝ) (ℓ : ι → H →L[ℝ] ℝ)
    (hw : ∀ j, 0 ≤ w j) (hs : Summable (fun j => w j * ‖ℓ j‖ ^ 2)) (x : H) :
    (∀ y, pairing w ℓ x y = 0) ↔ observationEnergy w ℓ x = 0 := by
  constructor
  · intro h
    simpa only [pairing_self] using h x
  · intro h y
    have hp := pairing_sq_le w ℓ hw hs x y
    rw [h, zero_mul] at hp
    exact sq_eq_zero_iff.mp (le_antisymm hp (sq_nonneg _))

end RiemannResearch.Analysis.WeightedObservationPairing
