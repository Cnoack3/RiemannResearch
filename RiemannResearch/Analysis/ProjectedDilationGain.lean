import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Exact gain from a projected dilation direction

Source: user-provided CRT and Four Improvements continuation, 6–7 October 2026.
The extensions retain complete signed identities and correction squares.


Updated 2026-10-07: source-reviewed proof draft; not compiled.
The Lean service returned Session terminated. The new optimal-ray completion
retains its positive line-search bonus and the optimizer correction square.

Let `r` be the old optimizer residual, `q` the proposed dilated head residual,
and `v` its orthogonal projection onto the old legal space. The hypotheses
`inner r v = 0` and `inner (q - v) v = 0` encode exactly the two orthogonalities
used here. No CRT mixing, independence, or arithmetic smallness is assumed.

The general identity retains the signed source pairing, the trial cost, the
positive projection square, and, in the final identity, the entire additional
optimizer correction square.
-/

noncomputable section

open scoped InnerProductSpace

namespace RiemannResearch.Analysis.ProjectedDilationGain

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Removing an orthogonal projection subtracts its exact squared norm. -/
theorem projected_norm_sq (q v : H)
    (hprojection : ⟪q - v, v⟫_ℝ = 0) :
    ‖q - v‖ ^ 2 = ‖q‖ ^ 2 - ‖v‖ ^ 2 := by
  have hcross : ⟪q, v⟫_ℝ = ‖v‖ ^ 2 := by
    rw [inner_sub_left, real_inner_self_eq_norm_sq] at hprojection
    linarith
  rw [norm_sub_sq_real, hcross]
  ring

/-- A real scalar multiplies squared norm by its square, including negative scalars. -/
theorem real_smul_norm_sq (t : ℝ) (u : H) :
    ‖t • u‖ ^ 2 = t ^ 2 * ‖u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq,
    real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  ring

/-- Exact signed gain for any real trial coefficient. -/
theorem projected_trial_gain (r q v : H) (t : ℝ)
    (hresidual : ⟪r, v⟫_ℝ = 0)
    (hprojection : ⟪q - v, v⟫_ℝ = 0) :
    ‖r‖ ^ 2 - ‖r - t • (q - v)‖ ^ 2 =
      2 * t * ⟪r, q⟫_ℝ - t ^ 2 * ‖q‖ ^ 2 + t ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_sub_sq_real, real_inner_smul_right, inner_sub_right,
    hresidual, real_smul_norm_sq, projected_norm_sq q v hprojection]
  ring

/-- The coefficient-one identity displays the source, trial cost, and projection square. -/
theorem projected_unit_trial_gain (r q v : H)
    (hresidual : ⟪r, v⟫_ℝ = 0)
    (hprojection : ⟪q - v, v⟫_ℝ = 0) :
    ‖r‖ ^ 2 - ‖r - (q - v)‖ ^ 2 =
      2 * ⟪r, q⟫_ℝ - ‖q‖ ^ 2 + ‖v‖ ^ 2 := by
  simpa using projected_trial_gain r q v 1 hresidual hprojection

/-- Dilation-compatible source and norm identities yield an exact positive gain. -/
theorem projected_dilation_gain (r q v : H) (p A : ℝ)
    (hp : 0 < p)
    (hnorm : ‖q‖ ^ 2 = A / p)
    (hsource : ⟪r, q⟫_ℝ = A)
    (hresidual : ⟪r, v⟫_ℝ = 0)
    (hprojection : ⟪q - v, v⟫_ℝ = 0) :
    ‖r‖ ^ 2 - ‖r - p • (q - v)‖ ^ 2 =
      p * A + p ^ 2 * ‖v‖ ^ 2 := by
  have hscaled : p * ‖q‖ ^ 2 = A := by
    simpa [mul_comm] using (eq_div_iff (ne_of_gt hp)).mp hnorm
  have hcost : p ^ 2 * ‖q‖ ^ 2 = p * A := by
    calc
      p ^ 2 * ‖q‖ ^ 2 = p * (p * ‖q‖ ^ 2) := by ring
      _ = p * A := by rw [hscaled]
  rw [projected_trial_gain r q v p hresidual hprojection, hsource, hcost]
  ring

/-- Retaining the projection square strengthens the basic dilation lower bound. -/
theorem projected_dilation_gain_ge (r q v : H) (p A : ℝ)
    (hp : 0 < p)
    (hnorm : ‖q‖ ^ 2 = A / p)
    (hsource : ⟪r, q⟫_ℝ = A)
    (hresidual : ⟪r, v⟫_ℝ = 0)
    (hprojection : ⟪q - v, v⟫_ℝ = 0) :
    p * A ≤ ‖r‖ ^ 2 - ‖r - p • (q - v)‖ ^ 2 := by
  rw [projected_dilation_gain r q v p A hp hnorm hsource hresidual hprojection]
  exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg p) (sq_nonneg ‖v‖))

/-- With nonnegative source energy, the proposed trial cannot increase the error. -/
theorem projected_dilation_error_le (r q v : H) (p A : ℝ)
    (hp : 0 < p) (hA : 0 ≤ A)
    (hnorm : ‖q‖ ^ 2 = A / p)
    (hsource : ⟪r, q⟫_ℝ = A)
    (hresidual : ⟪r, v⟫_ℝ = 0)
    (hprojection : ⟪q - v, v⟫_ℝ = 0) :
    ‖r - p • (q - v)‖ ^ 2 ≤ ‖r‖ ^ 2 := by
  have hgain := projected_dilation_gain_ge r q v p A hp hnorm hsource
    hresidual hprojection
  have hnonneg : 0 ≤ p * A := mul_nonneg (le_of_lt hp) hA
  linarith

/-- Orthogonal optimization contributes the full correction square. -/
theorem projected_optimizer_gain (r q v rnew correction : H) (t : ℝ)
    (hresidual : ⟪r, v⟫_ℝ = 0)
    (hprojection : ⟪q - v, v⟫_ℝ = 0)
    (htrial : r - t • (q - v) = rnew + correction)
    (hcorrection : ⟪rnew, correction⟫_ℝ = 0) :
    ‖r‖ ^ 2 - ‖rnew‖ ^ 2 =
      2 * t * ⟪r, q⟫_ℝ - t ^ 2 * ‖q‖ ^ 2 +
        t ^ 2 * ‖v‖ ^ 2 + ‖correction‖ ^ 2 := by
  have hsplit : ‖r - t • (q - v)‖ ^ 2 =
      ‖rnew‖ ^ 2 + ‖correction‖ ^ 2 := by
    rw [htrial, norm_add_sq_real, hcorrection]
    ring
  calc
    ‖r‖ ^ 2 - ‖rnew‖ ^ 2 =
        (‖r‖ ^ 2 - ‖r - t • (q - v)‖ ^ 2) + ‖correction‖ ^ 2 := by
          linarith [hsplit]
    _ = _ := by
      rw [projected_trial_gain r q v t hresidual hprojection]

/-- The prime-dilation gain plus both nonnegative geometric squares. -/
theorem projected_dilation_optimizer_gain (r q v rnew correction : H) (p A : ℝ)
    (hp : 0 < p)
    (hnorm : ‖q‖ ^ 2 = A / p)
    (hsource : ⟪r, q⟫_ℝ = A)
    (hresidual : ⟪r, v⟫_ℝ = 0)
    (hprojection : ⟪q - v, v⟫_ℝ = 0)
    (htrial : r - p • (q - v) = rnew + correction)
    (hcorrection : ⟪rnew, correction⟫_ℝ = 0) :
    ‖r‖ ^ 2 - ‖rnew‖ ^ 2 =
      p * A + p ^ 2 * ‖v‖ ^ 2 + ‖correction‖ ^ 2 := by
  have hsplit : ‖r - p • (q - v)‖ ^ 2 =
      ‖rnew‖ ^ 2 + ‖correction‖ ^ 2 := by
    rw [htrial, norm_add_sq_real, hcorrection]
    ring
  have hgain := projected_dilation_gain r q v p A hp hnorm hsource
    hresidual hprojection
  linarith

/-- Exact completion of the signed trial gain on a nonzero legal ray. -/
theorem ray_trial_completion (r u : H) (t : ℝ) (hu : 0 < ‖u‖ ^ 2) :
    ‖r‖ ^ 2 - ‖r - t • u‖ ^ 2 =
      ⟪r, u⟫_ℝ ^ 2 / ‖u‖ ^ 2 -
        ‖u‖ ^ 2 * (t - ⟪r, u⟫_ℝ / ‖u‖ ^ 2) ^ 2 := by
  have hnorm : ‖u‖ ≠ 0 := by
    intro hz
    apply (ne_of_gt hu)
    rw [hz]
    ring
  rw [norm_sub_sq_real, real_inner_smul_right, real_smul_norm_sq]
  field_simp [hnorm]
  <;> ring

/-- Optimal line search preserves the complete signed source pairing. -/
theorem ray_optimal_gain (r u : H) (hu : 0 < ‖u‖ ^ 2) :
    ‖r‖ ^ 2 - ‖r - (⟪r, u⟫_ℝ / ‖u‖ ^ 2) • u‖ ^ 2 =
      ⟪r, u⟫_ℝ ^ 2 / ‖u‖ ^ 2 := by
  have h := ray_trial_completion r u (⟪r, u⟫_ℝ / ‖u‖ ^ 2) hu
  have hz : ⟪r, u⟫_ℝ / ‖u‖ ^ 2 - ⟪r, u⟫_ℝ / ‖u‖ ^ 2 = 0 := sub_self _
  rw [hz, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero] at h
  exact h

/-- The optimal ray is at least as good as every real coefficient. -/
theorem ray_optimal_error_le (r u : H) (t : ℝ) (hu : 0 < ‖u‖ ^ 2) :
    ‖r - (⟪r, u⟫_ℝ / ‖u‖ ^ 2) • u‖ ^ 2 ≤ ‖r - t • u‖ ^ 2 := by
  have htrial := ray_trial_completion r u t hu
  have hopt := ray_optimal_gain r u hu
  have hnonneg := mul_nonneg hu.le (sq_nonneg (t - ⟪r, u⟫_ℝ / ‖u‖ ^ 2))
  linarith

/-- The exact algebraic bonus over the canonical dilation coefficient. -/
theorem normalized_ray_bonus (p A B N : ℝ) (hN : 0 < N)
    (hsource : A = p * (N + B)) :
    A ^ 2 / N = p * A + p ^ 2 * B + p ^ 2 * B ^ 2 / N := by
  rw [hsource]
  field_simp [ne_of_gt hN]
  <;> ring

/-- Optimal line search adds an explicit positive projection bonus to the
canonical dilation trial. The remaining optimizer correction is retained. -/
theorem projected_dilation_ray_optimizer_gain
    (r q v rnew correction : H) (p A : ℝ)
    (hp : 0 < p) (hu : 0 < ‖q - v‖ ^ 2)
    (hnorm : ‖q‖ ^ 2 = A / p)
    (hsource : ⟪r, q⟫_ℝ = A)
    (hresidual : ⟪r, v⟫_ℝ = 0)
    (hprojection : ⟪q - v, v⟫_ℝ = 0)
    (htrial : r - (A / ‖q - v‖ ^ 2) • (q - v) = rnew + correction)
    (hcorrection : ⟪rnew, correction⟫_ℝ = 0) :
    ‖r‖ ^ 2 - ‖rnew‖ ^ 2 = p * A + p ^ 2 * ‖v‖ ^ 2 +
      p ^ 2 * (‖v‖ ^ 2) ^ 2 / ‖q - v‖ ^ 2 + ‖correction‖ ^ 2 := by
  have hsource' : ⟪r, q - v⟫_ℝ = A := by
    rw [inner_sub_right, hsource, hresidual, sub_zero]
  have hscaled : p * ‖q‖ ^ 2 = A := by
    simpa [mul_comm] using (eq_div_iff (ne_of_gt hp)).mp hnorm
  have hnormproj := projected_norm_sq q v hprojection
  have hrelation : A = p * (‖q - v‖ ^ 2 + ‖v‖ ^ 2) := by
    rw [hnormproj]
    nlinarith [hscaled]
  have hgain := ray_optimal_gain r (q - v) hu
  rw [hsource'] at hgain
  have hsplit : ‖r - (A / ‖q - v‖ ^ 2) • (q - v)‖ ^ 2 =
      ‖rnew‖ ^ 2 + ‖correction‖ ^ 2 := by
    rw [htrial, norm_add_sq_real, hcorrection]
    ring
  have hbonus := normalized_ray_bonus p A (‖v‖ ^ 2) (‖q - v‖ ^ 2) hu hrelation
  linarith

/-- A nonzero complete source automatically gives a nonzero projected direction.
This discharges the line-search denominator hypothesis without a spectral gap. -/
theorem projected_direction_norm_sq_pos (r q v : H) (A : ℝ)
    (hA : 0 < A) (hsource : ⟪r, q⟫_ℝ = A)
    (hresidual : ⟪r, v⟫_ℝ = 0) :
    0 < ‖q - v‖ ^ 2 := by
  have hsource' : ⟪r, q - v⟫_ℝ = A := by
    rw [inner_sub_right, hsource, hresidual, sub_zero]
  by_contra hnot
  have hsq : ‖q - v‖ ^ 2 = 0 := le_antisymm (le_of_not_gt hnot) (sq_nonneg _)
  have hnorm : ‖q - v‖ = 0 := by nlinarith [norm_nonneg (q - v)]
  have hz : q - v = 0 := norm_eq_zero.mp hnorm
  rw [hz, inner_zero_right] at hsource'
  linarith

/-- The complete signed source controls degeneracy of its own legal ray.
Only the source direction is bounded; no uniform operator gap is asserted. -/
theorem ray_source_square_le_energy (r u : H) (hu : 0 < ‖u‖ ^ 2) :
    ⟪r, u⟫_ℝ ^ 2 ≤ ‖r‖ ^ 2 * ‖u‖ ^ 2 := by
  have hgain := ray_optimal_gain r u hu
  have hratio : ⟪r, u⟫_ℝ ^ 2 / ‖u‖ ^ 2 ≤ ‖r‖ ^ 2 := by
    linarith [sq_nonneg ‖r - (⟪r, u⟫_ℝ / ‖u‖ ^ 2) • u‖]
  exact (div_le_iff₀ hu).mp hratio

/-- Exact source-weighted conditioning bound for a projected dilation. -/
theorem projected_dilation_source_square_le_energy
    (r q v : H) (p A : ℝ)
    (hA : 0 < A)
    (hnorm : ‖q‖ ^ 2 = A / p) (hsource : ⟪r, q⟫_ℝ = A)
    (hresidual : ⟪r, v⟫_ℝ = 0)
    (hprojection : ⟪q - v, v⟫_ℝ = 0) :
    A ^ 2 ≤ ‖r‖ ^ 2 * (A / p - ‖v‖ ^ 2) := by
  have hu := projected_direction_norm_sq_pos r q v A hA hsource hresidual
  have hbound := ray_source_square_le_energy r (q - v) hu
  rw [inner_sub_right, hsource, hresidual, sub_zero,
    projected_norm_sq q v hprojection, hnorm] at hbound
  exact hbound

omit [InnerProductSpace ℝ H] in
/-- Source nonnegativity follows from the physical norm scaling identity. -/
theorem dilation_source_nonneg (q : H) (p A : ℝ) (hp : 0 < p)
    (hnorm : ‖q‖ ^ 2 = A / p) : 0 ≤ A := by
  have hscaled : p * ‖q‖ ^ 2 = A := by
    simpa [mul_comm] using (eq_div_iff (ne_of_gt hp)).mp hnorm
  rw [← hscaled]
  exact mul_nonneg hp.le (sq_nonneg _)

/-- Physical scaling alone supplies the nonnegative source needed for the
canonical trial to decrease the error. -/
theorem projected_dilation_error_le_of_scaling (r q v : H) (p A : ℝ)
    (hp : 0 < p) (hnorm : ‖q‖ ^ 2 = A / p)
    (hsource : ⟪r, q⟫_ℝ = A) (hresidual : ⟪r, v⟫_ℝ = 0)
    (hprojection : ⟪q - v, v⟫_ℝ = 0) :
    ‖r - p • (q - v)‖ ^ 2 ≤ ‖r‖ ^ 2 := by
  exact projected_dilation_error_le r q v p A hp
    (dilation_source_nonneg q p A hp hnorm) hnorm hsource hresidual hprojection

/-- The extra projection makes the optimal coefficient at least the physical
dilation coefficient. This compares the two actual legal trials. -/
theorem projected_dilation_optimal_coefficient_ge (q v : H) (p A : ℝ)
    (hp : 0 < p) (hu : 0 < ‖q - v‖ ^ 2)
    (hnorm : ‖q‖ ^ 2 = A / p)
    (hprojection : ⟪q - v, v⟫_ℝ = 0) :
    p ≤ A / ‖q - v‖ ^ 2 := by
  have hscaled : p * ‖q‖ ^ 2 = A := by
    simpa [mul_comm] using (eq_div_iff (ne_of_gt hp)).mp hnorm
  apply (le_div_iff₀ hu).mpr
  rw [projected_norm_sq q v hprojection]
  nlinarith [mul_nonneg hp.le (sq_nonneg ‖v‖)]

end RiemannResearch.Analysis.ProjectedDilationGain
