import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Reciprocal and conjugation symmetries for the Pareto Mellin convention

Source: user-provided argument. The transform convention here is
`M f s = integral_(0,infinity) f(x) x^(-s-1) dx`, namely `mellin f (-s)`.
The reciprocal change of variables and multiplication rule are Mathlib's
`mellin_comp_inv` and `mellin_cpow_smul`. Bochner integral equalities below use
Mathlib's totalized integral; convergence is not asserted merely by an equality.
-/

noncomputable section
open MeasureTheory Set

namespace RiemannResearch.Analysis.ReciprocalMellin

/-- Reciprocal reflection for the measure `dx / x^2`. -/
def reflect (f : ℝ → ℂ) (x : ℝ) : ℂ := (x : ℂ) * f x⁻¹

def conjugate (f : ℝ → ℂ) (x : ℝ) : ℂ := (starRingEnd ℂ) (f x)

theorem reflect_add (f g : ℝ → ℂ) : reflect (f + g) = reflect f + reflect g := by
  funext x
  simp [reflect, mul_add]

theorem reflect_smul (c : ℂ) (f : ℝ → ℂ) : reflect (c • f) = c • reflect f := by
  funext x
  simp only [reflect, Pi.smul_apply, smul_eq_mul]
  ring

theorem conjugate_add (f g : ℝ → ℂ) :
    conjugate (f + g) = conjugate f + conjugate g := by
  funext x
  simp [conjugate]

theorem conjugate_smul (c : ℂ) (f : ℝ → ℂ) :
    conjugate (c • f) = (starRingEnd ℂ) c • conjugate f := by
  funext x
  simp [conjugate, smul_eq_mul]

theorem measurable_reflect {f : ℝ → ℂ} (hf : Measurable f) :
    Measurable (reflect f) :=
  Complex.continuous_ofReal.measurable.mul (hf.comp measurable_inv)

theorem measurable_conjugate {f : ℝ → ℂ} (hf : Measurable f) :
    Measurable (conjugate f) :=
  Complex.continuous_conj.measurable.comp hf

/-- The sign convention used by the Pareto RH construction. -/
def transform (f : ℝ → ℂ) (s : ℂ) : ℂ := mellin f (-s)

theorem transform_eq_integral (f : ℝ → ℂ) (s : ℂ) :
    transform f s = ∫ x in Ioi (0 : ℝ), f x * (x : ℂ) ^ (-s - 1) := by
  simp only [transform, mellin, smul_eq_mul, mul_comm]

theorem reflect_reflect (f : ℝ → ℂ) {x : ℝ} (hx : x ≠ 0) :
    reflect (reflect f) x = f x := by
  simp only [reflect, inv_inv, Complex.ofReal_inv]
  rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hx), one_mul]

theorem conjugate_conjugate (f : ℝ → ℂ) : conjugate (conjugate f) = f := by
  funext x
  simp [conjugate]

theorem reflect_conjugate (f : ℝ → ℂ) :
    reflect (conjugate f) = conjugate (reflect f) := by
  funext x
  simp [reflect, conjugate]

theorem transform_reflect (f : ℝ → ℂ) (s : ℂ) :
    transform (reflect f) s = transform f (1 - s) := by
  have h := mellin_cpow_smul (fun x => f x⁻¹) (-s) (1 : ℂ)
  simp only [Complex.cpow_one, smul_eq_mul] at h
  change mellin (fun x => (x : ℂ) * f x⁻¹) (-s) = mellin f (-(1 - s))
  rw [h, mellin_comp_inv]
  congr 1
  ring

theorem transform_conjugate (f : ℝ → ℂ) (s : ℂ) :
    transform (conjugate f) s = (starRingEnd ℂ) (transform f ((starRingEnd ℂ) s)) := by
  rw [transform_eq_integral, transform_eq_integral, ← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hxarg : (x : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact ne_of_lt Real.pi_pos
  have hpow : (starRingEnd ℂ) ((x : ℂ) ^ (-((starRingEnd ℂ) s) - 1)) =
      (x : ℂ) ^ (-s - 1) := by
    simpa using (Complex.cpow_conj (x : ℂ) (-((starRingEnd ℂ) s) - 1) hxarg).symm
  simp only [conjugate, map_mul]
  rw [hpow]

theorem mellinConvergent_comp_inv (f : ℝ → ℂ) (s : ℂ) :
    MellinConvergent (fun x => f x⁻¹) s ↔ MellinConvergent f (-s) := by
  simpa [Real.rpow_neg_one, div_neg] using (MellinConvergent.comp_rpow (f := f) (s := s)
    (a := (-1 : ℝ)) (by norm_num))

/-- The reflected transform converges exactly at the reflected parameter. -/
theorem transform_convergent_reflect (f : ℝ → ℂ) (s : ℂ) :
    MellinConvergent (reflect f) (-s) ↔ MellinConvergent f (-(1 - s)) := by
  have h := MellinConvergent.cpow_smul (f := fun x => f x⁻¹) (s := -s) (a := (1 : ℂ))
  simp only [Complex.cpow_one, smul_eq_mul] at h
  change MellinConvergent (fun x => (x : ℂ) * f x⁻¹) (-s) ↔ _
  rw [h, mellinConvergent_comp_inv]
  have hs : -(-s + 1) = -(1 - s) := by ring
  rw [hs]

def criticalPoint (t : ℝ) : ℂ := (1 / 2 : ℂ) + (t : ℂ) * Complex.I

theorem criticalPoint_conj (t : ℝ) :
    (starRingEnd ℂ) (criticalPoint t) = criticalPoint (-t) := by
  norm_num [criticalPoint, Complex.conj_ofNat]

theorem criticalPoint_one_sub (t : ℝ) :
    1 - criticalPoint t = criticalPoint (-t) := by
  simp only [criticalPoint, Complex.ofReal_neg]
  ring

theorem transform_reflect_critical (f : ℝ → ℂ) (t : ℝ) :
    transform (reflect f) (criticalPoint t) = transform f (criticalPoint (-t)) := by
  rw [transform_reflect, criticalPoint_one_sub]

/-- Real-valued features already have Hermitian reflection on the critical line. -/
theorem transform_critical_neg_of_real (f : ℝ → ℂ)
    (hf : ∀ x, (starRingEnd ℂ) (f x) = f x) (t : ℝ) :
    transform f (criticalPoint (-t)) =
      (starRingEnd ℂ) (transform f (criticalPoint t)) := by
  have hcf : conjugate f = f := by funext x; exact hf x
  have h := transform_conjugate f (criticalPoint (-t))
  simpa only [hcf, criticalPoint_conj, neg_neg] using h

/-- Reciprocal reflection moves positive support above 1 to support below 1. -/
theorem reflect_vanishes_above_one (f : ℝ → ℂ)
    (hf : ∀ x, 0 < x → x < 1 → f x = 0) {x : ℝ} (hx : 1 < x) :
    reflect f x = 0 := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hi : x⁻¹ < 1 := (inv_lt_one₀ hx0).2 hx
  simp [reflect, hf x⁻¹ (inv_pos.mpr hx0) hi]

/-- The reverse support statement. -/
theorem reflect_vanishes_below_one (f : ℝ → ℂ)
    (hf : ∀ x, 1 < x → f x = 0) {x : ℝ} (hx0 : 0 < x) (hx : x < 1) :
    reflect f x = 0 := by
  have hi : 1 < x⁻¹ := (one_lt_inv₀ hx0).2 hx
  simp [reflect, hf x⁻¹ hi]

/-- The exact positive-axis statement avoids any convention at the null point 0. -/
theorem reflect_reflect_on_positive (f : ℝ → ℂ) :
    EqOn (reflect (reflect f)) f (Ioi 0) := by
  intro x hx
  exact reflect_reflect f (ne_of_gt hx)

/-- The weighted sesquilinear pairing on the positive axis. -/
def pairing (f g : ℝ → ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), (starRingEnd ℂ) (f x) * g x / (x : ℂ) ^ (2 : ℕ)

/-- The two copies are orthogonal; their possible overlap at 1 has measure zero. -/
theorem pairing_reflect_eq_zero (f g : ℝ → ℂ)
    (hf : ∀ x, 0 < x → x < 1 → f x = 0)
    (hg : ∀ x, 0 < x → x < 1 → g x = 0) :
    pairing f (reflect g) = 0 := by
  unfold pairing
  apply setIntegral_eq_zero_of_ae_eq_zero
  filter_upwards [volume.ae_ne (1 : ℝ)] with x hx1
  intro hx0
  rcases lt_or_gt_of_ne hx1 with hlt | hgt
  · simp [hf x hx0 hlt]
  · simp [reflect_vanishes_above_one g hg hgt]

def magnitudeSquared (f : ℝ → ℂ) (x : ℝ) : ℂ := (‖f x‖ ^ 2 : ℝ)

theorem magnitudeSquared_reflect (f : ℝ → ℂ) :
    magnitudeSquared (reflect f) =
      fun x : ℝ => (x : ℂ) ^ (2 : ℂ) • magnitudeSquared f x⁻¹ := by
  funext x
  change ((‖(x : ℂ) * f x⁻¹‖ ^ 2 : ℝ) : ℂ) =
    (x : ℂ) ^ (2 : ℂ) * ((‖f x⁻¹‖ ^ 2 : ℝ) : ℂ)
  rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.cpow_ofNat]

/-- Complexified weighted energy is unchanged by reflection. -/
theorem transform_magnitudeSquared_reflect (f : ℝ → ℂ) :
    transform (magnitudeSquared (reflect f)) 1 = transform (magnitudeSquared f) 1 := by
  rw [magnitudeSquared_reflect, transform, mellin_cpow_smul, mellin_comp_inv]
  norm_num [transform]

/-- The finite-energy condition is genuinely preserved, independent of totalization. -/
theorem magnitudeSquared_reflect_convergent (f : ℝ → ℂ) :
    MellinConvergent (magnitudeSquared (reflect f)) (-1) ↔
      MellinConvergent (magnitudeSquared f) (-1) := by
  rw [magnitudeSquared_reflect, MellinConvergent.cpow_smul,
    mellinConvergent_comp_inv]
  norm_num

/-- The real Pareto energy on the full positive axis. -/
def energy (f : ℝ → ℂ) : ℝ := ∫ x in Ioi (0 : ℝ), ‖f x‖ ^ 2 / x ^ 2

theorem energy_integrable_iff_mellinConvergent (f : ℝ → ℂ) :
    IntegrableOn (fun x => ‖f x‖ ^ 2 / x ^ 2) (Ioi (0 : ℝ)) ↔
      MellinConvergent (magnitudeSquared f) (-1) := by
  unfold MellinConvergent
  have hfun : (fun x : ℝ => (x : ℂ) ^ ((-1 : ℂ) - 1) • magnitudeSquared f x) =
      fun x => ((‖f x‖ ^ 2 / x ^ 2 : ℝ) : ℂ) := by
    funext x
    rw [show (-1 : ℂ) - 1 = -(2 : ℂ) by norm_num,
      Complex.cpow_neg]
    simp only [magnitudeSquared, Complex.cpow_ofNat, Complex.ofReal_div,
      Complex.ofReal_pow, smul_eq_mul]
    rw [div_eq_mul_inv]
    exact mul_comm _ _
  rw [hfun]
  constructor
  · intro h
    exact h.ofReal
  · intro h
    change Integrable (fun x : ℝ => ‖f x‖ ^ 2 / x ^ 2)
      (volume.restrict (Ioi 0))
    exact h.re.congr (Filter.Eventually.of_forall fun x => rfl)

theorem energy_integrable_reflect_iff (f : ℝ → ℂ) :
    IntegrableOn (fun x => ‖reflect f x‖ ^ 2 / x ^ 2) (Ioi (0 : ℝ)) ↔
      IntegrableOn (fun x => ‖f x‖ ^ 2 / x ^ 2) (Ioi (0 : ℝ)) := by
  rw [energy_integrable_iff_mellinConvergent, magnitudeSquared_reflect_convergent,
    ← energy_integrable_iff_mellinConvergent]

theorem energy_integrable_conjugate_iff (f : ℝ → ℂ) :
    IntegrableOn (fun x => ‖conjugate f x‖ ^ 2 / x ^ 2) (Ioi (0 : ℝ)) ↔
      IntegrableOn (fun x => ‖f x‖ ^ 2 / x ^ 2) (Ioi (0 : ℝ)) := by
  simp [conjugate]

theorem transform_magnitudeSquared_eq_energy (f : ℝ → ℂ) :
    transform (magnitudeSquared f) 1 = (energy f : ℂ) := by
  rw [transform_eq_integral]
  calc
    _ = ∫ x in Ioi (0 : ℝ), ((‖f x‖ ^ 2 / x ^ 2 : ℝ) : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only [magnitudeSquared]
      rw [show -(1 : ℂ) - 1 = -(2 : ℂ) by norm_num,
        Complex.cpow_neg]
      simp only [Complex.cpow_ofNat, Complex.ofReal_div, Complex.ofReal_pow]
      simp only [div_eq_mul_inv]
    _ = _ := integral_complex_ofReal

/-- Reflection preserves the actual weighted square-norm integral. -/
theorem energy_reflect (f : ℝ → ℂ) : energy (reflect f) = energy f := by
  apply Complex.ofReal_injective
  rw [← transform_magnitudeSquared_eq_energy, ← transform_magnitudeSquared_eq_energy,
    transform_magnitudeSquared_reflect]

theorem energy_conjugate (f : ℝ → ℂ) : energy (conjugate f) = energy f := by
  simp [energy, conjugate]

end RiemannResearch.Analysis.ReciprocalMellin
