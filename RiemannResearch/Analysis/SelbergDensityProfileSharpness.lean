/-
Copyright (c) 2026 RiemannResearch contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Sharpness of the Selberg–Ingham interpolation with two numerical inputs

At parameter t ≥ 1, put an atom of mass exp(t−8t²/7) at mark t², and
the remaining probability at zero. L = exp(2t²/21+t/2) is the model's
logarithmic height. The subcritical Selberg and three-logarithm Ingham
bounds both hold. This model tests the information in those two estimates.
-/

noncomputable section
open Filter Real
open scoped Topology
namespace RiemannResearch.Analysis.SelbergDensityProfileSharpness

def logHeight (t : ℝ) : ℝ := Real.exp ((2/21)*t^2+t/2)
def atomMass (t : ℝ) : ℝ := Real.exp (-(8/7)*t^2+t)

theorem atomMass_mem_Icc {t : ℝ} (ht : 1 ≤ t) : atomMass t ∈ Set.Icc 0 1 := by
  refine ⟨(Real.exp_pos _).le,Real.exp_le_one_iff.mpr ?_⟩
  nlinarith only [mul_nonneg (sub_nonneg.mpr ht) (show 0 ≤ t by linarith)]

/-- For each strict Selberg slope the constant is independent of the model height. -/
theorem subcritical_profile {a t : ℝ} (ha : a < 8/7) :
    atomMass t ≤ Real.exp (1/(4*(8/7-a))) * Real.exp (-a*t^2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hδ : 0 < 8/7-a := sub_pos.mpr ha
  have hd : 0 < 4*(8/7-a) := by positivity
  have hsq : t-(8/7-a)*t^2 ≤ 1/(4*(8/7-a)) := by
    apply (le_div_iff₀ hd).mpr
    nlinarith only [sq_nonneg (2*(8/7-a)*t-1)]
  linarith only [hsq]

/-- The larger-slope, two-extra-logarithm envelope is attained exactly. -/
theorem three_log_profile (t : ℝ) :
    atomMass t = logHeight t ^ (2:ℝ) * Real.exp (-(4/3)*t^2) := by
  unfold atomMass logHeight
  rw [← Real.exp_mul, ← Real.exp_add]
  congr 1
  ring

/-- Ratio to a candidate slope b with e extra powers of log height. -/
theorem profile_ratio (b e t : ℝ) :
    atomMass t * Real.exp (b*t^2) / logHeight t ^ e =
      Real.exp ((b-8/7-(2/21)*e)*t^2+(1-e/2)*t) := by
  unfold atomMass logHeight
  rw [← Real.exp_mul,← Real.exp_add,← Real.exp_sub]
  congr 1
  ring

/-- The entire lower interpolation edge fails for this family, up to the
three-logarithm endpoint. The edge's endpoint at slope 8/7 also fails. -/
theorem no_uniform_edge {b e : ℝ} (he : e ≤ (21/2)*(b-8/7)) (he₂ : e < 2) :
    Tendsto (fun t : ℝ => atomMass t * Real.exp (b*t^2) / logHeight t ^ e) atTop atTop := by
  have hc : 0 < 1-e/2 := by linarith
  have hmain := Real.tendsto_exp_atTop.comp (Filter.tendsto_id.const_mul_atTop hc)
  apply tendsto_atTop_mono _ hmain
  intro t
  rw [profile_ratio]
  apply Real.exp_le_exp.mpr
  have hquad : 0 ≤ (b-8/7-(2/21)*e)*t^2 := mul_nonneg (by linarith only [he]) (sq_nonneg t)
  change (1-e/2)*t ≤ _
  linarith only [hquad]

theorem clean_endpoint_fails :
    Tendsto (fun t : ℝ => atomMass t * Real.exp ((8/7)*t^2)) atTop atTop := by
  simpa using (no_uniform_edge (b := (8/7:ℝ)) (e := 0) (by norm_num) (by norm_num))

/-- Every subcritical exponential mark from the exceptional atom tends to
zero, a stronger microscopic conclusion than fixed-order moment collapse. -/
theorem strict_tilt_tendsto_zero {a : ℝ} (ha : a < 8/7) :
    Tendsto (fun t : ℝ => atomMass t * Real.exp (a*t^2)) atTop (nhds 0) := by
  have hδ : 0 < 8/7-a := sub_pos.mpr ha
  have hexp : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  apply squeeze_zero' _ _ hexp
  · exact Eventually.of_forall fun t => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (2/(8/7-a)), eventually_ge_atTop (0:ℝ)] with t ht ht₀
    unfold atomMass
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have htwo := (div_le_iff₀ hδ).mp ht
    nlinarith only [mul_nonneg (sub_nonneg.mpr htwo) ht₀]

end RiemannResearch.Analysis.SelbergDensityProfileSharpness
