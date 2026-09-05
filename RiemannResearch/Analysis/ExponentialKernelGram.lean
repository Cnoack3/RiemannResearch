/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exponential kernel Gram integral

For positive rate, the Volterra feature has an integrable pair product whose
integral is exp (-rate * |x-y|)/(2*rate). Finite sums therefore have a square
integral Gram formula and are nonnegative, without any condition on the points
or coefficients. This is finite-configuration positivity, not yet the analogous
quadratic form for an arbitrary L2 function.

Source: user-provided RH_Local_to_Global_Trace_Attack_Plan_2026-09-05,
Section on exponential Gram factorization, supplies the integral representation.
RH consumer: ScrewArchimedeanPositivity.
-/

namespace RiemannResearch.Analysis
open MeasureTheory Set
open scoped BigOperators
noncomputable section

def exponentialVolterraFeature (α x z : ℝ) : ℝ :=
  (Iic x).indicator (fun z => Real.exp (-α*(x-z))) z

theorem exponentialVolterraFeature_mul (α x y z : ℝ) :
    exponentialVolterraFeature α x z * exponentialVolterraFeature α y z =
      (Iic (min x y)).indicator
        (fun z => Real.exp (-α*(x+y))*Real.exp ((2*α)*z)) z := by
  by_cases hx : z ≤ x <;> by_cases hy : z ≤ y
  · simp only [exponentialVolterraFeature, Set.mem_Iic, Set.indicator_apply,
      hx, hy, le_min hx hy, ↓reduceIte]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  · simp [exponentialVolterraFeature, hx, hy]
  · simp [exponentialVolterraFeature, hx, hy]
  · simp [exponentialVolterraFeature, hx, hy]

theorem integrable_exponentialVolterraFeature_mul {α : ℝ} (hα : 0 < α) (x y : ℝ) :
    Integrable (fun z => exponentialVolterraFeature α x z * exponentialVolterraFeature α y z) := by
  simp_rw [exponentialVolterraFeature_mul]
  have hi : IntegrableOn (fun z => Real.exp (-α*(x+y))*Real.exp ((2*α)*z))
      (Iic (min x y)) := (integrableOn_exp_mul_Iic (by positivity : 0 < 2*α)
        (min x y)).const_mul (Real.exp (-α*(x+y)))
  exact hi.integrable_indicator measurableSet_Iic

theorem integral_exponentialVolterraFeature_mul {α : ℝ} (hα : 0 < α) (x y : ℝ) :
    (∫ z, exponentialVolterraFeature α x z * exponentialVolterraFeature α y z) =
      Real.exp (-α*|x-y|)/(2*α) := by
  simp_rw [exponentialVolterraFeature_mul]
  rw [integral_indicator measurableSet_Iic, integral_const_mul,
    integral_exp_mul_Iic (by positivity : 0 < 2*α), ← mul_div_assoc, ← Real.exp_add]
  have he : -α*(x+y) + 2*α*min x y = -α*|x-y| := by
    rcases le_total x y with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
      ring
  rw [he]

theorem exponentialKernel_finite_gram {ι : Type*} [Fintype ι]
    {α : ℝ} (hα : 0 < α) (x c : ι → ℝ) :
    (∑ i, ∑ j, c i * Real.exp (-α*|x i-x j|) * c j) =
      2*α * (∫ z, (∑ i, c i * exponentialVolterraFeature α (x i) z)^2) := by
  have he (z : ℝ) : (∑ i, c i * exponentialVolterraFeature α (x i) z)^2 =
      ∑ i, ∑ j, c i * (exponentialVolterraFeature α (x i) z *
        exponentialVolterraFeature α (x j) z) * c j := by
    rw [pow_two, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hij (i j : ι) : Integrable (fun z => c i *
      (exponentialVolterraFeature α (x i) z * exponentialVolterraFeature α (x j) z) * c j) :=
    ((integrable_exponentialVolterraFeature_mul hα (x i) (x j)).const_mul (c i)).mul_const (c j)
  simp_rw [he]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hij i j))]
  simp_rw [integral_finsetSum Finset.univ (fun j _ => hij _ j),
    integral_mul_const, integral_const_mul, integral_exponentialVolterraFeature_mul hα]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  field_simp

theorem exponentialKernel_finite_nonneg {ι : Type*} [Fintype ι]
    {α : ℝ} (hα : 0 < α) (x c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * Real.exp (-α*|x i-x j|) * c j := by
  rw [exponentialKernel_finite_gram hα]
  exact mul_nonneg (by positivity) (integral_nonneg (fun z => sq_nonneg _))

theorem exponentialVolterraFeature_nonneg (α x z : ℝ) :
    0 ≤ exponentialVolterraFeature α x z := by
  unfold exponentialVolterraFeature
  exact indicator_nonneg (fun _ _ => Real.exp_nonneg _) z

@[fun_prop]
theorem measurable_exponentialVolterraFeature (α : ℝ) :
    Measurable (Function.uncurry (exponentialVolterraFeature α)) := by
  change Measurable (fun p : ℝ × ℝ =>
    if p.2 ∈ Iic p.1 then Real.exp (-α * (p.1 - p.2)) else 0)
  apply Measurable.ite
  · simpa only [mem_Iic] using measurableSet_le measurable_snd measurable_fst
  · fun_prop
  · fun_prop

/-- Absolute integrability of the three-variable Volterra product. The proof
uses the sharp feature-product integral and the L1 product majorant
`|u x| * |u y| / (2 * α)`. -/
theorem integrable_exponentialVolterraFeature_triple
    {α : ℝ} (hα : 0 < α) (u : ℝ → ℝ) (hu : Integrable u)
    (humeas : Measurable u) :
    Integrable (fun p : (ℝ × ℝ) × ℝ =>
      (u p.1.1 * exponentialVolterraFeature α p.1.1 p.2) *
        (u p.1.2 * exponentialVolterraFeature α p.1.2 p.2)) := by
  rw [Measure.volume_eq_prod (ℝ × ℝ) ℝ, Measure.volume_eq_prod ℝ ℝ]
  let F : (ℝ × ℝ) × ℝ → ℝ := fun p =>
    (u p.1.1 * exponentialVolterraFeature α p.1.1 p.2) *
      (u p.1.2 * exponentialVolterraFeature α p.1.2 p.2)
  have hFmeas : Measurable F := by
    unfold F
    fun_prop
  apply (integrable_prod_iff hFmeas.aestronglyMeasurable).2
  constructor
  · filter_upwards with xy
    have h := integrable_exponentialVolterraFeature_mul hα xy.1 xy.2
    have hc := h.const_mul (u xy.1 * u xy.2)
    simpa only [F, mul_assoc, mul_left_comm, mul_comm] using hc
  · have hnorm (xy : ℝ × ℝ) :
        (∫ z, ‖F (xy, z)‖) =
          |u xy.1| * |u xy.2| *
            (Real.exp (-α * |xy.1 - xy.2|) / (2 * α)) := by
      have hp (z : ℝ) :
          ‖F (xy, z)‖ =
            (|u xy.1| * |u xy.2|) *
              (exponentialVolterraFeature α xy.1 z *
                exponentialVolterraFeature α xy.2 z) := by
        unfold F
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
          abs_of_nonneg (exponentialVolterraFeature_nonneg α xy.1 z),
          abs_of_nonneg (exponentialVolterraFeature_nonneg α xy.2 z)]
        ring
      simp_rw [hp, integral_const_mul,
        integral_exponentialVolterraFeature_mul hα]
    simp_rw [hnorm]
    have hsep : Integrable (fun xy : ℝ × ℝ => |u xy.1| * |u xy.2|)
        (volume.prod volume) :=
      hu.norm.mul_prod hu.norm
    have hmajor :
        Integrable (fun xy : ℝ × ℝ =>
          (1 / (2 * α)) * (|u xy.1| * |u xy.2|)) (volume.prod volume) :=
      hsep.const_mul (1 / (2 * α))
    apply hmajor.mono'
    · have hm := ((humeas.comp measurable_fst).norm.mul
            (humeas.comp measurable_snd).norm).mul
            (by fun_prop : Measurable (fun xy : ℝ × ℝ =>
              Real.exp (-α * |xy.1 - xy.2|) / (2 * α)))
      change AEStronglyMeasurable
        (((fun xy : ℝ × ℝ => |u xy.1|) * (fun xy => |u xy.2|)) *
          (fun xy => Real.exp (-α * |xy.1 - xy.2|) / (2 * α)))
        (volume.prod volume)
      simpa only [Function.comp_apply, Real.norm_eq_abs] using
        hm.aestronglyMeasurable
    · filter_upwards with xy
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · rw [mul_comm (1 / (2 * α))]
        apply mul_le_mul_of_nonneg_left
        · exact div_le_div_of_nonneg_right
            (Real.exp_le_one_iff.mpr
              (mul_nonpos_of_nonpos_of_nonneg
                (neg_nonpos.mpr (le_of_lt hα)) (abs_nonneg _)))
            (le_of_lt (mul_pos (by norm_num) hα))
        · positivity
      · positivity

/-- The exact integrated Gram identity for the exponential kernel. Unlike the
finite-configuration theorem above, this statement applies to every measurable
integrable real test. -/
theorem exponentialKernel_integral_gram
    {α : ℝ} (hα : 0 < α) (u : ℝ → ℝ) (hu : Integrable u)
    (humeas : Measurable u) :
    (∫ x, u x * (∫ y, Real.exp (-α * |x - y|) * u y)) =
      2 * α * (∫ z, (∫ x,
        u x * exponentialVolterraFeature α x z) ^ 2) := by
  let F : (ℝ × ℝ) × ℝ → ℝ := fun p =>
    (u p.1.1 * exponentialVolterraFeature α p.1.1 p.2) *
      (u p.1.2 * exponentialVolterraFeature α p.1.2 p.2)
  let K : ℝ × ℝ → ℝ := fun p =>
    u p.1 * Real.exp (-α * |p.1 - p.2|) * u p.2
  have hF : Integrable F :=
    integrable_exponentialVolterraFeature_triple hα u hu humeas
  have hFprod : Integrable F ((volume.prod volume).prod volume) := by
    simpa only [← Measure.volume_eq_prod] using hF
  have hz (xy : ℝ × ℝ) :
      (∫ z, F (xy, z)) = K xy / (2 * α) := by
    have hp (z : ℝ) :
        F (xy, z) = (u xy.1 * u xy.2) *
          (exponentialVolterraFeature α xy.1 z *
            exponentialVolterraFeature α xy.2 z) := by
      unfold F
      ring
    simp_rw [hp, integral_const_mul,
      integral_exponentialVolterraFeature_mul hα]
    unfold K
    field_simp
  have hK : Integrable K (volume.prod volume) := by
    have hi := hFprod.integral_prod_left
    have hidiv : Integrable (fun xy : ℝ × ℝ => K xy / (2 * α))
        (volume.prod volume) := by
      simpa only [hz] using hi
    have hc := hidiv.const_mul (2 * α)
    convert hc using 1
    funext xy
    field_simp
  have hswap :
      (∫ xy : ℝ × ℝ, ∫ z, F (xy, z)) =
        ∫ z, ∫ xy : ℝ × ℝ, F (xy, z) := by
    have hleft := integral_prod F hFprod
    have hright := integral_prod_symm F hFprod
    simpa only [← Measure.volume_eq_prod] using hleft.symm.trans hright
  have hxy (z : ℝ) :
      (∫ xy : ℝ × ℝ, F (xy, z)) =
        (∫ x, u x * exponentialVolterraFeature α x z) ^ 2 := by
    have h := integral_prod_mul (μ := volume) (ν := volume)
      (fun x => u x * exponentialVolterraFeature α x z)
      (fun y => u y * exponentialVolterraFeature α y z)
    rw [Measure.volume_eq_prod ℝ ℝ]
    simpa only [F, pow_two] using h
  have hinner (x : ℝ) :
      (∫ y, K (x, y)) =
        u x * (∫ y, Real.exp (-α * |x - y|) * u y) := by
    have h := integral_const_mul (μ := volume) (u x)
      (fun y : ℝ => Real.exp (-α * |x - y|) * u y)
    simpa only [K, mul_assoc] using h
  have hscale :
      (∫ xy : ℝ × ℝ, K xy) =
        2 * α * (∫ xy : ℝ × ℝ, K xy / (2 * α)) := by
    have heq : (fun xy : ℝ × ℝ => K xy / (2 * α)) =
        fun xy => (1 / (2 * α)) * K xy := by
      funext xy
      ring
    rw [heq, integral_const_mul]
    field_simp
  calc
    (∫ x, u x * (∫ y, Real.exp (-α * |x - y|) * u y)) =
        ∫ xy : ℝ × ℝ, K xy := by
      rw [Measure.volume_eq_prod ℝ ℝ]
      calc
        _ = ∫ x, ∫ y, K (x, y) := by simp_rw [hinner]
        _ = _ := (integral_prod K hK).symm
    _ = 2 * α * (∫ xy : ℝ × ℝ, ∫ z, F (xy, z)) := by
      rw [hscale]
      simp_rw [hz]
    _ = 2 * α * (∫ z, ∫ xy : ℝ × ℝ, F (xy, z)) := by
      rw [hswap]
    _ = _ := by simp_rw [hxy]

/-- The exponential convolution kernel is nonnegative on every measurable
integrable real test. -/
theorem exponentialKernel_integral_nonneg
    {α : ℝ} (hα : 0 < α) (u : ℝ → ℝ) (hu : Integrable u)
    (humeas : Measurable u) :
    0 ≤ ∫ x, u x * (∫ y, Real.exp (-α * |x - y|) * u y) := by
  rw [exponentialKernel_integral_gram hα u hu humeas]
  exact mul_nonneg (by positivity) (integral_nonneg (fun z => sq_nonneg _))

end
end RiemannResearch.Analysis
