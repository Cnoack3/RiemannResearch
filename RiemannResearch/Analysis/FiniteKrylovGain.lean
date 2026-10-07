import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Finite two-direction Krylov gain

Finite Schur completion for the actual signed source moments. These algebraic
lemmas neither supply nor assume the arithmetic gain-divergence provider.
The Hilbert lemmas expose the source spectral variance and the positive centered
third moment. The actual operator and arithmetic adapters remain explicit.
-/

noncomputable section

open scoped InnerProductSpace

namespace RiemannResearch.Analysis.FiniteKrylovGain

/-- Gain of a finite two-direction legal trial, before optimization. -/
def twoDirectionGain (a b d0 d1 d2 x y : ℝ) : ℝ :=
  2 * (a * x + b * y) - (d0 * x ^ 2 + 2 * d1 * x * y + d2 * y ^ 2)

/-- First Schur completion, retaining the signed second source. -/
theorem two_direction_schur_completion
    (a b d0 d1 d2 x y : ℝ) (hd0 : d0 ≠ 0) :
    twoDirectionGain a b d0 d1 d2 x y =
      a ^ 2 / d0 + 2 * (b - d1 * a / d0) * y -
        (d2 - d1 ^ 2 / d0) * y ^ 2 -
        d0 * (x + (d1 * y - a) / d0) ^ 2 := by
  unfold twoDirectionGain
  field_simp [hd0]
  <;> ring

/-- Scalar ray completion used for the remaining Schur direction. -/
theorem scalar_ray_completion (r s y : ℝ) (hs : s ≠ 0) :
    2 * r * y - s * y ^ 2 = r ^ 2 / s - s * (y - r / s) ^ 2 := by
  field_simp [hs]
  <;> ring

/-- Full exact completion of the two-direction finite trial. -/
theorem two_direction_full_completion
    (a b d0 d1 d2 x y : ℝ) (hd0 : d0 ≠ 0)
    (hs : d2 - d1 ^ 2 / d0 ≠ 0) :
    twoDirectionGain a b d0 d1 d2 x y =
      a ^ 2 / d0 + (b - d1 * a / d0) ^ 2 / (d2 - d1 ^ 2 / d0) -
        d0 * (x + (d1 * y - a) / d0) ^ 2 -
        (d2 - d1 ^ 2 / d0) *
          (y - (b - d1 * a / d0) / (d2 - d1 ^ 2 / d0)) ^ 2 := by
  have hsecond := scalar_ray_completion (b - d1 * a / d0)
    (d2 - d1 ^ 2 / d0) y hs
  rw [two_direction_schur_completion a b d0 d1 d2 x y hd0]
  linarith [hsecond]

/-- Positivity of the two actual Schur denominators gives a finite upper bound
on every coefficient choice, without an operator inverse. -/
theorem two_direction_gain_le_optimal
    (a b d0 d1 d2 x y : ℝ) (hd0 : 0 < d0)
    (hs : 0 < d2 - d1 ^ 2 / d0) :
    twoDirectionGain a b d0 d1 d2 x y ≤
      a ^ 2 / d0 + (b - d1 * a / d0) ^ 2 / (d2 - d1 ^ 2 / d0) := by
  rw [two_direction_full_completion a b d0 d1 d2 x y
    (ne_of_gt hd0) (ne_of_gt hs)]
  have hfirst : 0 ≤ d0 * (x + (d1 * y - a) / d0) ^ 2 :=
    mul_nonneg hd0.le (sq_nonneg _)
  have hsecond : 0 ≤ (d2 - d1 ^ 2 / d0) *
      (y - (b - d1 * a / d0) / (d2 - d1 ^ 2 / d0)) ^ 2 :=
    mul_nonneg hs.le (sq_nonneg _)
  linarith

/-- The explicit Schur coefficients attain the finite optimum. -/
theorem two_direction_optimal_coefficients
    (a b d0 d1 d2 : ℝ) (hd0 : d0 ≠ 0)
    (hs : d2 - d1 ^ 2 / d0 ≠ 0) :
    twoDirectionGain a b d0 d1 d2
      ((a - d1 * ((b - d1 * a / d0) / (d2 - d1 ^ 2 / d0))) / d0)
      ((b - d1 * a / d0) / (d2 - d1 ^ 2 / d0)) =
      a ^ 2 / d0 + (b - d1 * a / d0) ^ 2 / (d2 - d1 ^ 2 / d0) := by
  rw [two_direction_full_completion a b d0 d1 d2 _ _ hd0 hs]
  have hfirst :
      (a - d1 * ((b - d1 * a / d0) / (d2 - d1 ^ 2 / d0))) / d0 +
      (d1 * ((b - d1 * a / d0) / (d2 - d1 ^ 2 / d0)) - a) / d0 = 0 := by
    ring
  rw [hfirst]
  simp

/-- The second Schur source is exactly the source-moment variance. -/
theorem moment_schur_source (a b c : ℝ) (hab : a - b ≠ 0) :
    b - (b - c) * a / (a - b) = (a * c - b ^ 2) / (a - b) := by
  field_simp [hab]
  <;> ring

/-- Finite moment determinant and the second Schur denominator. -/
theorem moment_schur_denominator (a b c d : ℝ) (hab : a - b ≠ 0) :
    c - d - (b - c) ^ 2 / (a - b) =
      ((a - b) * (c - d) - (b - c) ^ 2) / (a - b) := by
  field_simp [hab]
  <;> ring

/-- Positivity of the moment determinant discharges the divided Schur gap. -/
theorem moment_schur_denominator_pos (a b c d : ℝ)
    (hab : 0 < a - b)
    (hdet : 0 < (a - b) * (c - d) - (b - c) ^ 2) :
    0 < c - d - (b - c) ^ 2 / (a - b) := by
  rw [moment_schur_denominator a b c d (ne_of_gt hab)]
  exact div_pos hdet hab

/-- Exact extra variance square beyond the already optimized first ray. -/
theorem moment_two_direction_gain_bonus (a b c d : ℝ)
    (hab : a - b ≠ 0)
    (hdet : (a - b) * (c - d) - (b - c) ^ 2 ≠ 0) :
    a ^ 2 / (a - b) +
      (b - (b - c) * a / (a - b)) ^ 2 /
        (c - d - (b - c) ^ 2 / (a - b)) =
    a ^ 2 / (a - b) +
      (a * c - b ^ 2) ^ 2 /
        ((a - b) * ((a - b) * (c - d) - (b - c) ^ 2)) := by
  rw [moment_schur_source a b c hab,
    moment_schur_denominator a b c d hab]
  field_simp [hab, hdet]
  <;> ring

/-- The retained variance square can only strengthen the optimal-ray gain. -/
theorem moment_two_direction_bonus_nonneg (p a b c d : ℝ)
    (hp : 0 ≤ p) (hab : 0 < a - b)
    (hdet : 0 < (a - b) * (c - d) - (b - c) ^ 2) :
    p * (a ^ 2 / (a - b)) ≤
      p * (a ^ 2 / (a - b) + (a * c - b ^ 2) ^ 2 /
        ((a - b) * ((a - b) * (c - d) - (b - c) ^ 2))) := by
  apply mul_le_mul_of_nonneg_left _ hp
  exact le_add_of_nonneg_right (div_nonneg (sq_nonneg _)
    (mul_pos hab hdet).le)

section HilbertMoments

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Squared norm of a real scalar multiple. -/
theorem real_smul_norm_sq (t : ℝ) (u : H) :
    ‖t • u‖ ^ 2 = t ^ 2 * ‖u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  ring

/-- The scalar quadratic is the literal gain of any two legal Hilbert
directions, preserving the mixed inner product and source signs. -/
theorem two_direction_hilbert_gain (r u v : H) (x y : ℝ) :
    ‖r‖ ^ 2 - ‖r - (x • u + y • v)‖ ^ 2 =
      twoDirectionGain ⟪r, u⟫_ℝ ⟪r, v⟫_ℝ
        (‖u‖ ^ 2) ⟪u, v⟫_ℝ (‖v‖ ^ 2) x y := by
  unfold twoDirectionGain
  rw [norm_sub_sq_real, inner_add_right,
    real_inner_smul_right, real_inner_smul_right,
    norm_add_sq_real, real_smul_norm_sq, real_smul_norm_sq,
    real_inner_smul_left, real_inner_smul_right]
  ring

/-- Adapter for the common physical dilation factor in the finite moment
quadratic. The assumptions are the actual norm/source pair identities. -/
theorem scaled_two_direction_hilbert_gain
    (r u v : H) (p a b d0 d1 d2 x y : ℝ)
    (hsourceu : ⟪r, u⟫_ℝ = p * a)
    (hsourcev : ⟪r, v⟫_ℝ = p * b)
    (hnormu : ‖u‖ ^ 2 = p * d0)
    (hinner : ⟪u, v⟫_ℝ = p * d1)
    (hnormv : ‖v‖ ^ 2 = p * d2) :
    ‖r‖ ^ 2 - ‖r - (x • u + y • v)‖ ^ 2 =
      p * twoDirectionGain a b d0 d1 d2 x y := by
  rw [two_direction_hilbert_gain, hsourceu, hsourcev, hnormu, hinner, hnormv]
  unfold twoDirectionGain
  ring

/-- Every two-direction trial retains the complete actual optimizer correction
square. No condition on the magnitude of the arithmetic sources is used. -/
theorem scaled_two_direction_optimizer_gain
    (r u v rnew correction : H) (p a b d0 d1 d2 x y : ℝ)
    (hsourceu : ⟪r, u⟫_ℝ = p * a)
    (hsourcev : ⟪r, v⟫_ℝ = p * b)
    (hnormu : ‖u‖ ^ 2 = p * d0)
    (hinner : ⟪u, v⟫_ℝ = p * d1)
    (hnormv : ‖v‖ ^ 2 = p * d2)
    (htrial : r - (x • u + y • v) = rnew + correction)
    (horth : ⟪rnew, correction⟫_ℝ = 0) :
    ‖r‖ ^ 2 - ‖rnew‖ ^ 2 =
      p * twoDirectionGain a b d0 d1 d2 x y + ‖correction‖ ^ 2 := by
  have hsplit : ‖r - (x • u + y • v)‖ ^ 2 =
      ‖rnew‖ ^ 2 + ‖correction‖ ^ 2 := by
    rw [htrial, norm_add_sq_real, horth]
    ring
  have hgain := scaled_two_direction_hilbert_gain r u v p a b d0 d1 d2 x y
    hsourceu hsourcev hnormu hinner hnormv
  linarith

/-- Actual centered source variance, with no coordinatewise absolute values. -/
theorem centered_source_variance_identity (w kw : H) (hw : 0 < ‖w‖ ^ 2) :
    ‖w‖ ^ 2 * ‖kw - (⟪w, kw⟫_ℝ / ‖w‖ ^ 2) • w‖ ^ 2 =
      ‖w‖ ^ 2 * ‖kw‖ ^ 2 - ⟪w, kw⟫_ℝ ^ 2 := by
  have hwnorm : ‖w‖ ≠ 0 := by
    intro hz
    have hzero : ‖w‖ ^ 2 = 0 := by rw [hz]; ring
    linarith
  rw [norm_sub_sq_real, real_inner_smul_right, real_smul_norm_sq,
    real_inner_comm kw w]
  field_simp [hwnorm, ne_of_gt hw]
  <;> ring

/-- The moment numerator is a genuine nonnegative Hilbert square. -/
theorem source_moment_variance_nonneg (w kw : H) (hw : 0 < ‖w‖ ^ 2) :
    0 ≤ ‖w‖ ^ 2 * ‖kw‖ ^ 2 - ⟪w, kw⟫_ℝ ^ 2 := by
  rw [← centered_source_variance_identity w kw hw]
  exact mul_nonneg (sq_nonneg _) (sq_nonneg _)

/-- The centered third moment remains an exact compression quadratic form. -/
theorem centered_third_moment_identity (K : H →ₗ[ℝ] H) (w : H) (t : ℝ)
    (hsymm : ∀ x y, ⟪K x, y⟫_ℝ = ⟪x, K y⟫_ℝ) :
    ⟪K w - t • w, K (K w - t • w)⟫_ℝ =
      ⟪K w, K (K w)⟫_ℝ - 2 * t * ‖K w‖ ^ 2 +
        t ^ 2 * ⟪w, K w⟫_ℝ := by
  simp only [map_sub, map_smul, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  rw [← hsymm w (K w), real_inner_self_eq_norm_sq]
  ring

/-- Positivity of the actual compression retains a second positive term after
the optimized ray, beyond its spectral variance. -/
theorem centered_third_moment_nonneg (K : H →ₗ[ℝ] H) (w : H) (t : ℝ)
    (hsymm : ∀ x y, ⟪K x, y⟫_ℝ = ⟪x, K y⟫_ℝ)
    (hpositive : ∀ x, 0 ≤ ⟪x, K x⟫_ℝ) :
    0 ≤ ⟪K w, K (K w)⟫_ℝ - 2 * t * ‖K w‖ ^ 2 +
      t ^ 2 * ⟪w, K w⟫_ℝ := by
  rw [← centered_third_moment_identity K w t hsymm]
  exact hpositive _

end HilbertMoments

end RiemannResearch.Analysis.FiniteKrylovGain
