import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-!
# Exact minimum energy with one prescribed signal
Source: user-requested Ramanujan dual continuation, 23 October 2026.
Orthogonal projection gives a unique mean-one minimum with its full squared
remainder. Nested normalized projections satisfy an exact reciprocal-energy
distance formula. No finite-dimensional or arithmetic assumption is needed.
-/
noncomputable section
namespace RiemannResearch.Analysis.ProjectionMeanOne
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (K : Submodule ℝ H) [K.HasOrthogonalProjection]

def normalized (x : H) : H := (‖K.starProjection x‖ ^ 2)⁻¹ • K.starProjection x

theorem pairing (x f : H) (hf : f ∈ K) :
    inner ℝ x f = inner ℝ (K.starProjection x) f := by
  have h := Submodule.inner_right_of_mem_orthogonal hf
    (Submodule.sub_starProjection_mem_orthogonal (K := K) x)
  rw [inner_sub_right] at h
  have hx := real_inner_comm x f
  have hp := real_inner_comm (K.starProjection x) f
  linarith

theorem normalized_mem (x : H) : normalized K x ∈ K :=
  K.smul_mem _ (K.starProjection_apply_mem x)

theorem normalized_signal (x : H) (hx : K.starProjection x ≠ 0) :
    inner ℝ x (normalized K x) = 1 := by
  have hn : ‖K.starProjection x‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  rw [normalized, real_inner_smul_right,
    pairing K x _ (K.starProjection_apply_mem x), real_inner_self_eq_norm_sq,
    inv_mul_cancel₀ hn]

theorem normalized_energy (x : H) (hx : K.starProjection x ≠ 0) :
    ‖normalized K x‖ ^ 2 = (‖K.starProjection x‖ ^ 2)⁻¹ := by
  have hn : ‖K.starProjection x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  rw [normalized, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  field_simp

theorem completion (x f : H) (hx : K.starProjection x ≠ 0)
    (hf : f ∈ K) (hm : inner ℝ x f = 1) :
    ‖f‖ ^ 2 = (‖K.starProjection x‖ ^ 2)⁻¹ +
      ‖f - normalized K x‖ ^ 2 := by
  have hi : inner ℝ f (normalized K x) = (‖K.starProjection x‖ ^ 2)⁻¹ := by
    rw [normalized, real_inner_smul_right, real_inner_comm,
      ← pairing K x f hf, hm, mul_one]
  rw [norm_sub_sq_real, normalized_energy K x hx, hi]
  ring

theorem unique (x f : H) (hx : K.starProjection x ≠ 0)
    (hf : f ∈ K) (hm : inner ℝ x f = 1) :
    ‖f‖ ^ 2 = (‖K.starProjection x‖ ^ 2)⁻¹ ↔ f = normalized K x := by
  rw [completion K x f hx hf hm]
  simp only [add_eq_left, sq_eq_zero_iff, norm_eq_zero, sub_eq_zero]

theorem nested_distance (L : Submodule ℝ H) [L.HasOrthogonalProjection]
    (hKL : K ≤ L) (x : H) (hK : K.starProjection x ≠ 0)
    (hL : L.starProjection x ≠ 0) :
    ‖normalized K x - normalized L x‖ ^ 2 =
      (‖K.starProjection x‖ ^ 2)⁻¹ - (‖L.starProjection x‖ ^ 2)⁻¹ := by
  have h := completion L x (normalized K x) hL
    (hKL (normalized_mem K x)) (normalized_signal K x hK)
  rw [normalized_energy K x hK] at h
  linarith
end RiemannResearch.Analysis.ProjectionMeanOne
