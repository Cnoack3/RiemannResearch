import RiemannResearch.Analysis.CriticalCutoffGrowth

/-!
# Sharpness of the scalar critical-cutoff profile loss

Source: an explicit exponential model derived for the hypotheses of
`Analysis/CriticalCutoffEndpoint`, whose RH consumer is the projected-dual mass
obstruction. It satisfies those scalar assumptions and has normalized endpoint
mass exactly one. These functions are not asserted to be arithmetic projected
dual masses or errors. No arithmetic endpoint asymptotic is concluded.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.Analysis

private theorem sharp_model_exp_cancel (t : ℝ) :
    Real.exp (2 * t) ^ 2 * Real.exp (-4 * t) = 1 := by
  rw [pow_two, ← Real.exp_add, ← Real.exp_add]
  have he : (2 * t + 2 * t) + -4 * t = 0 := by ring
  rw [he, Real.exp_zero]

/-- The squared profile normalization is exactly one in the scalar model. -/
theorem critical_cutoff_sharp_model_normalization (t : ℝ) (ht : 0 < t) :
    t ^ 2 * (Real.exp (-4 * t) * (Real.exp (2 * t) / t) ^ 2) = 1 := by
  calc
    _ = Real.exp (2 * t) ^ 2 * Real.exp (-4 * t) := by
      field_simp [ht.ne']
    _ = 1 := sharp_model_exp_cancel t

/-- The fourth-power error estimate holds with equality, with a=4 and C=16. -/
theorem critical_cutoff_sharp_model_error (t : ℝ) (ht : 0 < t) :
    (2 / Real.sqrt t) ^ 4 =
      16 * (Real.exp (2 * t) / t) ^ 2 * Real.exp (-4 * t) := by
  have hs4 : (Real.sqrt t) ^ 4 = t ^ 2 := by
    calc
      _ = ((Real.sqrt t) ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt ht.le]
  have hmass : (Real.exp (2 * t) / t) ^ 2 * Real.exp (-4 * t) = 1 / t ^ 2 := by
    rw [div_pow]
    calc
      _ = (Real.exp (2 * t) ^ 2 * Real.exp (-4 * t)) / t ^ 2 := by ring
      _ = _ := by rw [sharp_model_exp_cancel t]
  calc
    _ = 16 / t ^ 2 := by rw [div_pow, hs4]; norm_num
    _ = 16 * ((Real.exp (2 * t) / t) ^ 2 * Real.exp (-4 * t)) := by rw [hmass]; ring
    _ = _ := by ring

/-- The literal cutoff holds at every positive R for the scalar model.
The proof uses the head for R≥t/4 and the tail for R<t/4. -/
theorem critical_cutoff_sharp_model_cutoff (t : ℝ) (ht : 1 ≤ t)
    (R : ℝ) (hR : 0 < R) :
    1 ≤ (2 / Real.sqrt t) * Real.sqrt R +
      2 * (Real.exp (2 * t) / t) * Real.exp (-R / 2) := by
  have ht0 : 0 < t := by linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hhead0 : 0 ≤ (2 / Real.sqrt t) * Real.sqrt R := by positivity
  have htail0 : 0 ≤ 2 * (Real.exp (2 * t) / t) * Real.exp (-R / 2) := by positivity
  by_cases hcase : t ≤ 4 * R
  · have hs : Real.sqrt t ≤ 2 * Real.sqrt R := by
      nlinarith [Real.sq_sqrt ht0.le, Real.sq_sqrt hR.le,
        Real.sqrt_nonneg t, Real.sqrt_nonneg R]
    have hhead : 1 ≤ (2 / Real.sqrt t) * Real.sqrt R := by
      rw [div_mul_eq_mul_div]
      exact (le_div_iff₀ hst).mpr (by simpa only [one_mul] using hs)
    linarith
  · have hsmall : 4 * R < t := lt_of_not_ge hcase
    have hexp : t / 2 ≤ Real.exp (2 * t - R / 2) := by
      calc
        _ ≤ (2 * t - R / 2) + 1 := by linarith
        _ ≤ _ := Real.add_one_le_exp _
    have hid : 2 * (Real.exp (2 * t) / t) * Real.exp (-R / 2) =
        2 * Real.exp (2 * t - R / 2) / t := by
      rw [show 2 * t - R / 2 = 2 * t + (-R / 2) by ring, Real.exp_add]
      ring
    have htail : 1 ≤ 2 * (Real.exp (2 * t) / t) * Real.exp (-R / 2) := by
      rw [hid]
      exact (le_div_iff₀ ht0).mpr (by nlinarith only [hexp])
    linarith

/-- A=4, C=16, D=0, L=1 satisfy the scalar assumptions while the endpoint
profile-normalized mass stays exactly one. This is not a model of the actual
arithmetic projected duals. -/
theorem critical_cutoff_quadratic_loss_sharp_model (t : ℝ) (ht : 1 ≤ t) :
    0 ≤ Real.exp (2 * t) / t ∧ 0 ≤ 2 / Real.sqrt t ∧
    (2 / Real.sqrt t) ^ 4 = 16 * (Real.exp (2 * t) / t) ^ 2 * Real.exp (-4 * t) ∧
    t ^ 2 * (Real.exp (-4 * t) * (Real.exp (2 * t) / t) ^ 2) = 1 ∧
    ∀ R : ℝ, 0 < R → 1 ≤ (2 / Real.sqrt t) * Real.sqrt R +
      2 * (0 + Real.exp (2 * t) / t) * Real.exp (-R / 2) := by
  have ht0 : 0 < t := by linarith
  refine ⟨by positivity, by positivity, critical_cutoff_sharp_model_error t ht0,
    critical_cutoff_sharp_model_normalization t ht0, ?_⟩
  intro R hR
  simpa only [zero_add] using critical_cutoff_sharp_model_cutoff t ht R hR

end RiemannResearch.Analysis
