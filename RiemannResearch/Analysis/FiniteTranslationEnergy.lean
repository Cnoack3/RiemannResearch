import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact signed finite-translation energy

Source: user-supplied `v_prime_side_factorization_A_F_audited.pdf`,
Theorem 11.7 and Track F4. The source supplies the signed-square strategy.
The results apply to arbitrary finite nonnegative weights and norm-preserving
maps, without a spectral or RH hypothesis. The cosine results concern the
actual finite multiplier symbol; no Fourier operator realization is assumed.
-/

noncomputable section
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.FiniteTranslationEnergy

variable {ι H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Exact identity before taking any inequality. Linearity of the maps is
unnecessary: preservation of the norm of the tested vector suffices. -/
theorem signed_energy_identity (s : Finset ι) (c : ι → ℝ)
    (U : ι → H → H) (x : H)
    (hU : ∀ i ∈ s, ‖U i x‖ = ‖x‖) :
    -2 * (∑ i ∈ s, c i * (inner ℂ x (U i x)).re) =
      (∑ i ∈ s, c i * ‖x - U i x‖ ^ 2) -
        2 * (∑ i ∈ s, c i) * ‖x‖ ^ 2 := by
  have hi (i : ι) (hi : i ∈ s) :
      -2 * (c i * (inner ℂ x (U i x)).re) =
        c i * ‖x - U i x‖ ^ 2 - 2 * c i * ‖x‖ ^ 2 := by
    have h := norm_sub_sq (𝕜 := ℂ) x (U i x)
    rw [hU i hi] at h
    simp only [RCLike.re_to_complex] at h
    rw [h]
    ring
  calc
    _ = ∑ i ∈ s, (-2 * (c i * (inner ℂ x (U i x)).re)) := by
      rw [Finset.mul_sum]
    _ = ∑ i ∈ s, (c i * ‖x - U i x‖ ^ 2 - 2 * c i * ‖x‖ ^ 2) :=
      Finset.sum_congr rfl hi
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]

theorem signed_energy_lower_bound (s : Finset ι) (c : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (U : ι → H → H) (x : H)
    (hU : ∀ i ∈ s, ‖U i x‖ = ‖x‖) :
    -2 * (∑ i ∈ s, c i) * ‖x‖ ^ 2 ≤
      -2 * (∑ i ∈ s, c i * (inner ℂ x (U i x)).re) := by
  rw [signed_energy_identity s c U x hU]
  have hp : 0 ≤ ∑ i ∈ s, c i * ‖x - U i x‖ ^ 2 :=
    Finset.sum_nonneg fun i hi => mul_nonneg (hc i hi) (sq_nonneg _)
  linarith


/-- Polar rank-two sector as an exact difference of two squares. -/
theorem polar_signed_identity (z w : ℂ) :
    2 * (inner ℂ z w).re = (‖z + w‖ ^ 2 - ‖z - w‖ ^ 2) / 2 := by
  have hp := norm_add_sq (𝕜 := ℂ) z w
  have hm := norm_sub_sq (𝕜 := ℂ) z w
  simp only [RCLike.re_to_complex] at hp hm
  linarith

/-- Finite-cutoff Krein identity including both polar and archimedean
sectors. The values `ap` and `am` can be the positive and negative gamma
integrals; no sign or analytic convergence is hidden in this algebraic identity. -/
theorem completed_signed_identity (s : Finset ι) (c : ι → ℝ)
    (U : ι → H → H) (x : H) (hU : ∀ i ∈ s, ‖U i x‖ = ‖x‖)
    (z w : ℂ) (ap am : ℝ) :
    2 * (inner ℂ z w).re + ap - am -
        2 * (∑ i ∈ s, c i * (inner ℂ x (U i x)).re) =
      ‖z + w‖ ^ 2 / 2 + ap + (∑ i ∈ s, c i * ‖x - U i x‖ ^ 2) -
        (‖z - w‖ ^ 2 / 2 + am + 2 * (∑ i ∈ s, c i) * ‖x‖ ^ 2) := by
  have ht := signed_energy_identity s c U x hU
  have hp := polar_signed_identity z w
  linarith

/-- The exact Fourier symbol of a finite signed translation sum. -/
def cosineSymbol (s : Finset ι) (c a : ι → ℝ) (t : ℝ) : ℝ :=
  -2 * ∑ i ∈ s, c i * Real.cos (t * a i)

@[simp] theorem cosineSymbol_zero (s : Finset ι) (c a : ι → ℝ) :
    cosineSymbol s c a 0 = -2 * ∑ i ∈ s, c i := by
  simp [cosineSymbol]

theorem cosineSymbol_lower_bound (s : Finset ι) (c a : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (t : ℝ) :
    -2 * (∑ i ∈ s, c i) ≤ cosineSymbol s c a t := by
  have h : (∑ i ∈ s, c i * Real.cos (t * a i)) ≤ ∑ i ∈ s, c i := by
    apply Finset.sum_le_sum
    intro i hi
    simpa using mul_le_mul_of_nonneg_left (Real.cos_le_one (t * a i)) (hc i hi)
  unfold cosineSymbol
  linarith

/-- The scalar correction is sharp at every finite cutoff, not merely
asymptotically: its least possible value is twice the total weight. -/
theorem scalar_repair_iff (s : Finset ι) (c a : ι → ℝ)
    (hc : ∀ i ∈ s, 0 ≤ c i) (b : ℝ) :
    (∀ t, 0 ≤ cosineSymbol s c a t + b) ↔ 2 * (∑ i ∈ s, c i) ≤ b := by
  constructor
  · intro h
    have h0 := h 0
    simp only [cosineSymbol_zero] at h0
    linarith
  · intro h t
    have hl := cosineSymbol_lower_bound s c a hc t
    linarith

/-- Any nonconstant pointwise repair also pays the full deficit at zero. -/
theorem repair_at_zero (s : Finset ι) (c a : ι → ℝ)
    (b : ℝ → ℝ) (h : ∀ t, 0 ≤ cosineSymbol s c a t + b t) :
    2 * (∑ i ∈ s, c i) ≤ b 0 := by
  have h0 := h 0
  simp only [cosineSymbol_zero] at h0
  linarith

/-- Pointwise convergence of quadratic values and their signed errors is
enough to preserve positivity. No operator convergence is needed here. -/
theorem nonneg_of_approximate_squares {q e : ℕ → ℝ} {L : ℝ}
    (hq : Filter.Tendsto q Filter.atTop (𝓝 L))
    (he : Filter.Tendsto e Filter.atTop (𝓝 0))
    (hqe : ∀ n, e n ≤ q n) : 0 ≤ L := by
  have h : (0 : ℝ) - L ≤ 0 :=
    le_of_tendsto (he.sub hq) (Filter.Eventually.of_forall fun n => sub_nonpos.mpr (hqe n))
  linarith

end RiemannResearch.Analysis.FiniteTranslationEnergy
