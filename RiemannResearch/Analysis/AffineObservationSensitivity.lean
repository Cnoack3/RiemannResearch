import RiemannResearch.Analysis.MultipleAffineObservationProjection
import RiemannResearch.Analysis.FiniteGramSignalStability
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Sharp sensitivity and strict convexity of affine observation optimizers

Source: user-requested fifth Ramanujan dual continuation, 24 October 2026.
The actual inverse observation-Gram metric measures target perturbations
exactly. The full interpolation identity gives strict convexity of the
minimum squared error and preserves the complete curvature remainder.
-/

noncomputable section
namespace RiemannResearch.Analysis.AffineObservationSensitivity
open FiniteHilbertConstraints FiniteGramCapacity FiniteGramSignalStability
open MultipleAffineObservationProjection

variable {ι H : Type*} [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem affineCandidate_sub (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    {v : ι → H} (hv : LinearIndependent ℝ v) (f : H) (t s : ι → ℝ) :
    affineCandidate K hv f t - affineCandidate K hv f s = minimumVector hv (t - s) := by
  have hd : affineMismatch K v f t - affineMismatch K v f s = t - s := by
    funext i
    simp only [Pi.sub_apply, affineMismatch]
    ring
  have h := minimumVector_sub hv (affineMismatch K v f t) (affineMismatch K v f s)
  rw [hd] at h
  unfold affineCandidate
  rw [h]
  abel

/-- This is an exact isometry from the inverse observation-Gram metric. -/
theorem affineCandidate_distance (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    {v : ι → H} (hv : LinearIndependent ℝ v) (f : H) (t s : ι → ℝ) :
    ‖affineCandidate K hv f t - affineCandidate K hv f s‖ ^ 2 = capacity hv (t - s) := by
  rw [affineCandidate_sub, capacity_eq_norm_sq]

theorem affineCandidate_affine (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    {v : ι → H} (hv : LinearIndependent ℝ v) (f : H) (t s : ι → ℝ) (θ : ℝ) :
    affineCandidate K hv f ((1 - θ) • t + θ • s) =
      (1 - θ) • affineCandidate K hv f t + θ • affineCandidate K hv f s := by
  have hd : affineMismatch K v f ((1 - θ) • t + θ • s) =
      (1 - θ) • affineMismatch K v f t + θ • affineMismatch K v f s := by
    funext i
    simp only [affineMismatch, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  unfold affineCandidate
  rw [hd]
  change K.starProjection f + sourceLinear hv
      ((1 - θ) • affineMismatch K v f t + θ • affineMismatch K v f s) =
    (1 - θ) • (K.starProjection f + sourceLinear hv (affineMismatch K v f t)) +
      θ • (K.starProjection f + sourceLinear hv (affineMismatch K v f s))
  rw [map_add, map_smul, map_smul]
  module

theorem norm_affine_exact (x y : H) (θ : ℝ) :
    ‖(1 - θ) • x + θ • y‖ ^ 2 =
      (1 - θ) * ‖x‖ ^ 2 + θ * ‖y‖ ^ 2 - θ * (1 - θ) * ‖x - y‖ ^ 2 := by
  rw [norm_add_sq_real]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_left, inner_smul_right, norm_sub_sq_real]
  ring

/-- The entire curvature term is the actual inverse-Gram displacement cost. -/
theorem affine_error_interpolation (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    {v : ι → H} (hv : LinearIndependent ℝ v) (f : H) (t s : ι → ℝ) (θ : ℝ) :
    ‖f - affineCandidate K hv f ((1 - θ) • t + θ • s)‖ ^ 2 =
      (1 - θ) * ‖f - affineCandidate K hv f t‖ ^ 2 +
        θ * ‖f - affineCandidate K hv f s‖ ^ 2 - θ * (1 - θ) * capacity hv (t - s) := by
  rw [affineCandidate_affine]
  have he : f - ((1 - θ) • affineCandidate K hv f t + θ • affineCandidate K hv f s) =
      (1 - θ) • (f - affineCandidate K hv f t) + θ • (f - affineCandidate K hv f s) := by module
  have hd : (f - affineCandidate K hv f t) - (f - affineCandidate K hv f s) =
      affineCandidate K hv f s - affineCandidate K hv f t := by abel
  rw [he, norm_affine_exact, hd,
    norm_sub_rev (affineCandidate K hv f s) (affineCandidate K hv f t), affineCandidate_distance]

theorem affine_error_strict_convex (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    {v : ι → H} (hv : LinearIndependent ℝ v) (f : H) (t s : ι → ℝ)
    (hts : t ≠ s) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ < 1) :
    ‖f - affineCandidate K hv f ((1 - θ) • t + θ • s)‖ ^ 2 <
      (1 - θ) * ‖f - affineCandidate K hv f t‖ ^ 2 + θ * ‖f - affineCandidate K hv f s‖ ^ 2 := by
  rw [affine_error_interpolation]
  have hp := mul_pos (mul_pos hθ (sub_pos.mpr hθ1)) (capacity_pos hv (t - s) (sub_ne_zero.mpr hts))
  linarith

/-- No ambient or diagonal replacement of the inverse-metric target radius. -/
theorem affine_error_radius (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    {v : ι → H} (hv : LinearIndependent ℝ v) (f : H) (t s : ι → ℝ) :
    |‖f - affineCandidate K hv f t‖ - ‖f - affineCandidate K hv f s‖| ≤
      ‖minimumVector hv (t - s)‖ := by
  have h := abs_norm_sub_norm_le (f - affineCandidate K hv f t) (f - affineCandidate K hv f s)
  have he : (f - affineCandidate K hv f t) - (f - affineCandidate K hv f s) =
      -(affineCandidate K hv f t - affineCandidate K hv f s) := by abel
  rwa [he, norm_neg, affineCandidate_sub] at h

end RiemannResearch.Analysis.AffineObservationSensitivity
