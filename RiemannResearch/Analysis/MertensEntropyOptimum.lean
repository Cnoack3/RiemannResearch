/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.MertensExponentialEntropy

/-!
# Optimal constant when lowering an exponential Mertens rate

Source: the user-supplied Mertens displacement archive motivates the entropy
loss in the complete energy estimate. Translating the tangent inequality
for the exponential to its equality point gives the optimal constant.
-/
noncomputable section

namespace RiemannResearch.Analysis

/-- For fixed rates, the multiplicative constant is attained over real u. -/
theorem exponential_entropy_rate_isGreatest (b c : ℝ) (hb : 0 < b) (hcb : c < b) :
    IsGreatest (Set.range fun u : ℝ => (1 + b * u) * Real.exp (-(b-c) * u))
      ((b / (b-c)) * Real.exp (-(c/b))) := by
  have hgap : 0 < b-c := sub_pos.mpr hcb
  constructor
  · refine ⟨c/(b*(b-c)), ?_⟩
    have hlin : 1 + b * (c / (b * (b - c))) = b / (b-c) := by
      field_simp [hb.ne', hgap.ne'] <;> ring
    have he : -(b-c) * (c/(b*(b-c))) = -(c/b) := by
      field_simp [hb.ne', hgap.ne'] <;> ring
    change (1 + b * (c / (b * (b - c)))) * Real.exp (-(b - c) * (c / (b * (b - c)))) = _
    rw [hlin, he]
  · rintro _ ⟨u, rfl⟩
    let t := (b-c)*u-c/b
    have hid : 1 + b*u = (b/(b-c))*(t+1) := by
      dsimp [t]
      field_simp [hb.ne', hgap.ne'] <;> ring
    have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp t) (div_nonneg hb.le hgap.le)
    calc
      (1+b*u)*Real.exp (-(b-c)*u) = ((b/(b-c))*(t+1))*Real.exp (-(b-c)*u) := by rw [← hid]
      _ ≤ ((b/(b-c))*Real.exp t)*Real.exp (-(b-c)*u) :=
        mul_le_mul_of_nonneg_right hh (Real.exp_pos _).le
      _ = _ := by
        rw [mul_assoc, ← Real.exp_add]
        have he : t + -(b-c)*u = -(c/b) := by dsimp [t]; ring
        rw [he]

/-- The optimal scalar constant in the original entropy normalization. -/
theorem exponential_entropy_le_optimal_rate (b c u : ℝ) (hb : 0 < b) (hcb : c < b) :
    Real.exp (-b*u)*(1 + Real.log (1/Real.exp (-b*u))) ≤
      ((b/(b-c))*Real.exp (-(c/b))) * Real.exp (-c*u) := by
  have hh := (exponential_entropy_rate_isGreatest b c hb hcb).2 (Set.mem_range_self u)
  have hmul := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-c*u)).le
  have hex : -(b-c)*u + -c*u = -b*u := by ring
  rw [mul_assoc, ← Real.exp_add, hex] at hmul
  have hlog : Real.log (1 / Real.exp (-b * u)) = b * u := by
    rw [one_div, Real.log_inv, Real.log_exp]
    ring
  rw [hlog, mul_comm (Real.exp (-b * u))]
  exact hmul

end RiemannResearch.Analysis
