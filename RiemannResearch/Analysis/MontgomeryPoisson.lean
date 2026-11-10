/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # Bilateral exponential transform for Montgomery's Cauchy kernel

Source: Montgomery (1973), https://websites.umich.edu/~hlm/paircor1.pdf,
and the Poisson bridge in the user-provided Montgomery handoff, Section 4.
The proof splits the integral into two half-lines using Mathlib's improper
exponential integrals. Complex horizontal shifts are allowed exactly in
|Re z| < a. No RH or density hypothesis is used.
-/

noncomputable section
open MeasureTheory Set
namespace RiemannResearch.Analysis.MontgomeryPoisson

def feature (a : ℝ) (z : ℂ) (s : ℝ) : ℂ :=
  Complex.exp ((-(a * |s|) : ℝ) + (s : ℂ) * z)

theorem feature_nonneg (a : ℝ) (z : ℂ) {s : ℝ} (hs : 0 ≤ s) :
    feature a z s = Complex.exp ((z - a) * (s : ℂ)) := by
  unfold feature
  rw [abs_of_nonneg hs]
  congr 1
  push_cast
  ring

theorem feature_nonpos (a : ℝ) (z : ℂ) {s : ℝ} (hs : s ≤ 0) :
    feature a z s = Complex.exp ((z + a) * (s : ℂ)) := by
  unfold feature
  rw [abs_of_nonpos hs]
  congr 1
  push_cast
  ring

theorem feature_integrableOn_Iic (a : ℝ) (z : ℂ) (hz : -a < z.re) :
    IntegrableOn (feature a z) (Iic 0) := by
  have h : 0 < (z + (a : ℂ)).re := by simpa using (show 0 < z.re + a by linarith)
  refine (integrableOn_exp_mul_complex_Iic h 0).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Iic] with s hs
  exact (feature_nonpos a z hs).symm

theorem feature_integrableOn_Ioi (a : ℝ) (z : ℂ) (hz : z.re < a) :
    IntegrableOn (feature a z) (Ioi 0) := by
  have h : (z - (a : ℂ)).re < 0 := by simpa using (show z.re - a < 0 by linarith)
  refine (integrableOn_exp_mul_complex_Ioi h 0).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact (feature_nonneg a z hs.le).symm

theorem integrable_feature (a : ℝ) (z : ℂ) (hz : |z.re| < a) :
    Integrable (feature a z) := by
  have hl := feature_integrableOn_Iic a z (abs_lt.mp hz).1
  have hr := feature_integrableOn_Ioi a z (abs_lt.mp hz).2
  simpa only [Iic_union_Ioi, integrableOn_univ] using hl.union hr

theorem integral_feature (a : ℝ) (z : ℂ) (hz : |z.re| < a) :
    (∫ s : ℝ, feature a z s) = 2 * a / ((a : ℂ)^2-z^2) := by
  have hl := feature_integrableOn_Iic a z (abs_lt.mp hz).1
  have hr := feature_integrableOn_Ioi a z (abs_lt.mp hz).2
  have hp : 0 < (z + (a : ℂ)).re := by
    simp only [Complex.add_re, Complex.ofReal_re]; linarith [(abs_lt.mp hz).1]
  have hm : (z - (a : ℂ)).re < 0 := by
    simp only [Complex.sub_re, Complex.ofReal_re]; linarith [(abs_lt.mp hz).2]
  have il : (∫ s : ℝ in Iic 0, feature a z s) = 1 / (z+a) := by
    calc
      _ = ∫ s : ℝ in Iic 0, Complex.exp ((z+a)*(s : ℂ)) :=
        setIntegral_congr_fun measurableSet_Iic (fun s hs => feature_nonpos a z hs)
      _ = _ := by rw [integral_exp_mul_complex_Iic hp]; simp
  have ir : (∫ s : ℝ in Ioi 0, feature a z s) = -1 / (z-a) := by
    calc
      _ = ∫ s : ℝ in Ioi 0, Complex.exp ((z-a)*(s : ℂ)) :=
        setIntegral_congr_fun measurableSet_Ioi (fun s hs => feature_nonneg a z hs.le)
      _ = _ := by rw [integral_exp_mul_complex_Ioi hm]; simp
  rw [← intervalIntegral.integral_Iic_add_Ioi hl hr, il, ir]
  have hp0 : z + (a : ℂ) ≠ 0 := fun h => by simpa [h] using hp
  have hm0 : z - (a : ℂ) ≠ 0 := fun h => by simpa [h] using hm
  have hden : (a : ℂ)^2-z^2 ≠ 0 := by
    intro h
    have hh : (z+a)*(z-a) = (0 : ℂ) := by
      calc
        _ = -((a : ℂ)^2-z^2) := by ring
        _ = 0 := by rw [h]; simp
    rcases mul_eq_zero.mp hh with hh | hh
    · exact hp0 hh
    · exact hm0 hh
  field_simp [hp0, hm0, hden]
  <;> ring

theorem integral_cauchy (d : ℝ) :
    (∫ s : ℝ, feature 2 ((d : ℂ)*Complex.I) s) = ((4/(4+d^2) : ℝ) : ℂ) := by
  have hz : |((d : ℂ)*Complex.I).re| < (2 : ℝ) := by simp
  rw [integral_feature 2 _ hz]
  push_cast
  simp only [mul_pow, Complex.I_sq]
  ring

end RiemannResearch.Analysis.MontgomeryPoisson
