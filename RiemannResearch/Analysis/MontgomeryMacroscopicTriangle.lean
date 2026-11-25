import RiemannResearch.Analysis.MontgomeryMacroscopicGap
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Physical triangular energy at macroscopic widths

Integrating the actual positive-gap law gives the physical triangular window
energy, with the complete equal-ordinate atom retained in the exact formula.
The oriented off-diagonal energy has a uniform cubic profile on the entire
macroscopic width interval.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroWindowVariance ActualZeroCollisionCertificate

/-- Physical triangular energy, including its entire equal-ordinate atom,
equals the primitive of the normalized macroscopic positive-gap count. -/
theorem macroscopicPhysicalTriangle_eq {T c : ℝ} (hT : 1 < T) (hc : 0 ≤ c) :
    actualPhysicalTriangleEnergy T (c*T) / (unfoldedCutoff T)^2 =
      c * ((actualCollision T : ℝ) / (unfoldedCutoff T)^2) +
        2 * ∫ x in (0 : ℝ)..c, positiveGapMass T (x * unfoldedCutoff T) / unfoldedCutoff T := by
  let D := unfoldedCutoff T
  let L := Real.log T / (2*Real.pi)
  have hl : 0 < L := div_pos (Real.log_pos hT) (by positivity)
  have hd : 0 < D := div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  have hwidth : c*D/L = c*T := by
    dsimp [D,L,unfoldedCutoff]
    field_simp [(Real.log_pos hT).ne',Real.pi_ne_zero] <;> ring
  have htriangle := physicalTriangle_eq_collision_add_positive_gaps hT (mul_nonneg hc hd.le)
  change actualPhysicalTriangleEnergy T (c*D/L) = c*D*((actualCollision T : ℝ)/D) +
    2 * (∫ u in (0 : ℝ)..c*D, positiveGapMass T u) at htriangle
  rw [hwidth] at htriangle
  change actualPhysicalTriangleEnergy T (c*T)/D^2 = c*((actualCollision T : ℝ)/D^2) +
    2 * (∫ x in (0 : ℝ)..c, positiveGapMass T (x*D)/D)
  rw [htriangle,intervalIntegral.integral_div,
    intervalIntegral.integral_comp_mul_right (positiveGapMass T) hd.ne',zero_mul,smul_eq_mul]
  field_simp [hd.ne'] <;> ring

private theorem twice_integral_macroscopic_model (c : ℝ) :
    2 * (∫ x in (0 : ℝ)..c, x - x^2/2) = c^2-c^3/3 := by
  have hp : Continuous (fun x : ℝ => x^2/2) := by fun_prop
  rw [intervalIntegral.integral_sub (f := fun x : ℝ => x) (g := fun x : ℝ => x^2/2)
    (a := (0:ℝ)) (b := c) (μ := volume) (continuous_id.intervalIntegrable _ _) (hp.intervalIntegrable _ _),
    intervalIntegral.integral_div,integral_pow,integral_id]
  norm_num
  <;> ring

/-- The oriented off-diagonal part of the physical energy has the uniform
limit c² - c³/3 throughout the entire unit interval of fractional widths. -/
theorem eventually_macroscopicOffDiagonalTriangle_uniform {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ c ∈ Icc (0:ℝ) 1,
      |actualPhysicalTriangleEnergy T (c*T) / (unfoldedCutoff T)^2 -
        c * ((actualCollision T : ℝ)/(unfoldedCutoff T)^2) - (c^2-c^3/3)| ≤ ε := by
  filter_upwards [eventually_macroscopic_gap_uniform (show 0 < ε/2 by linarith),
    eventually_gt_atTop (1:ℝ)] with T hgap hT c hc
  let D := unfoldedCutoff T
  let F := fun x : ℝ => positiveGapMass T (x*D) /D
  let M := fun x : ℝ => x-x^2/2
  have hd : 0 < D := div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  have hm : Monotone F := fun a b hab => div_le_div_of_nonneg_right
    (positiveGapMass_mono hT (mul_le_mul_of_nonneg_right hab hd.le)) hd.le
  have hM : Continuous M := by dsimp [M]; fun_prop
  have hI : |∫ x in (0 : ℝ)..c, F x-M x| ≤ ε/2 := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := c)
      (f := fun x => F x-M x) (C := ε/2) (by
        intro x hx
        rw [uIoc_of_le hc.1] at hx
        simpa only [Real.norm_eq_abs] using hgap x ⟨hx.1.le,hx.2.trans hc.2⟩)
    rw [Real.norm_eq_abs,sub_zero,abs_of_nonneg hc.1] at h
    have hle := mul_le_mul_of_nonneg_left hc.2 (show 0 ≤ ε/2 by positivity)
    exact h.trans (by simpa only [mul_one] using hle)
  rw [macroscopicPhysicalTriangle_eq hT hc.1,add_sub_cancel_left,← twice_integral_macroscopic_model]
  change |2*(∫ x in (0:ℝ)..c, F x) - 2*(∫ x in (0:ℝ)..c, M x)| ≤ ε
  rw [← mul_sub, ← intervalIntegral.integral_sub hm.intervalIntegrable (hM.intervalIntegrable _ _),
    abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith only [hI]

/-- Any vanishing bound on the complete normalized collision atom upgrades
the cubic profile to the entire physical triangle. -/
theorem eventually_macroscopicPhysicalTriangle_uniform_of_collision
    (hcollision : Tendsto (fun T : ℝ => (actualCollision T : ℝ)/(unfoldedCutoff T)^2)
      atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ c ∈ Icc (0:ℝ) 1,
      |actualPhysicalTriangleEnergy T (c*T) / (unfoldedCutoff T)^2 - (c^2-c^3/3)| ≤ ε := by
  filter_upwards [eventually_macroscopicOffDiagonalTriangle_uniform (half_pos hε),
    hcollision.eventually_lt_const (half_pos hε)] with T hT hd c hc
  let a := (actualCollision T : ℝ)/(unfoldedCutoff T)^2
  have ha : 0 ≤ a := div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have h₀ : 0 ≤ c*a := mul_nonneg hc.1 ha
  have h₁ : c*a ≤ ε/2 := (mul_le_mul_of_nonneg_right hc.2 ha).trans
    (by simpa only [one_mul] using hd.le)
  have hcT := abs_le.mp (hT c hc)
  apply abs_le.mpr
  constructor <;> linarith only [hcT.1,hcT.2,h₀,h₁]

end RiemannResearch.Analysis.MontgomeryPositiveGap

namespace RiemannResearch.Analysis.MontgomeryPositiveGap

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.eventually_macroscopicOffDiagonalTriangle_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eventually_macroscopicOffDiagonalTriangle_uniform

end RiemannResearch.Analysis.MontgomeryPositiveGap
