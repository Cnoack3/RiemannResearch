/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteSpectralDoubleLog
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Complete-source moment contrasts and upper budgets

Source: user-provided complete-source double-log budget task, 7 October 2026.
The identities retain every source weight and eigenvalue. The cap is an
explicit finite hypothesis; the actual conductor application discharges it.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteSpectralBudget
variable {ι : Type* }

theorem doubleLog_le_self {x : ℝ} (hx : 0 ≤ x) : doubleLog x ≤ x := by
  have hlog := Real.log_nonneg (by linarith : 1 ≤ 1 + x)
  have h₁ := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + x)
  have h₂ := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + Real.log (1 + x))
  unfold doubleLog
  linarith

/-- Complete correction-weighted double-log moment. -/
def correctionDoubleLog (s : Finset ι) (w lam : ι → ℝ) : ℝ :=
  ∑ i ∈ s, (w i * lam i / (1+lam i)) * doubleLog (lam i)

/-- The exact remaining source term, including zero and large eigenvalues. -/
def doubleLogRemainder (s : Finset ι) (w lam : ι → ℝ) : ℝ :=
  ∑ i ∈ s, w i * doubleLog (lam i) / (1+lam i)

/-- Positive contrast below a complete-spectrum cap. No source is screened. -/
def doubleLogCapContrast (s : Finset ι) (w lam : ι → ℝ) (L : ℝ) : ℝ :=
  ∑ i ∈ s, (w i * lam i / (1+lam i)) *
    (doubleLog L - doubleLog (lam i))

/-- Exact division of the literal source into correction and remainder. -/
theorem moment_eq_correctionDoubleLog_add_remainder
    (s : Finset ι) (w lam : ι → ℝ) (hlam : ∀ i ∈ s, 0 ≤ lam i) :
    moment s w lam doubleLog =
      correctionDoubleLog s w lam + doubleLogRemainder s w lam := by
  unfold moment correctionDoubleLog doubleLogRemainder
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hd : 1+lam i ≠ 0 := ne_of_gt (by linarith [hlam i hi])
  field_simp [hd]
  ring

/-- The whole signed contrast is retained before the upper estimate. -/
theorem moment_eq_cap_correction_sub_contrast_add_remainder
    (s : Finset ι) (w lam : ι → ℝ) (L : ℝ)
    (hlam : ∀ i ∈ s, 0 ≤ lam i) :
    moment s w lam doubleLog =
      doubleLog L * correction s w lam -
        doubleLogCapContrast s w lam L + doubleLogRemainder s w lam := by
  rw [moment_eq_correctionDoubleLog_add_remainder s w lam hlam]
  unfold correctionDoubleLog correction doubleLogCapContrast
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem doubleLogRemainder_nonneg
    (s : Finset ι) (w lam : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam : ∀ i ∈ s, 0 ≤ lam i) :
    0 ≤ doubleLogRemainder s w lam := by
  apply Finset.sum_nonneg
  intro i hi
  exact div_nonneg (mul_nonneg (hw i hi) (doubleLog_nonneg (hlam i hi)))
    (by linarith [hlam i hi])

theorem doubleLogCapContrast_nonneg
    (s : Finset ι) (w lam : ι → ℝ) (L : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam : ∀ i ∈ s, 0 ≤ lam i)
    (hcap : ∀ i ∈ s, lam i ≤ L) :
    0 ≤ doubleLogCapContrast s w lam L := by
  apply Finset.sum_nonneg
  intro i hi
  exact mul_nonneg
    (div_nonneg (mul_nonneg (hw i hi) (hlam i hi)) (by linarith [hlam i hi]))
    (sub_nonneg.mpr (doubleLog_mono_nonneg (hlam i hi) (hcap i hi)))

/-- A cap-independent remainder bound, useful after division by a diverging
outer-log scale. -/
theorem doubleLogRemainder_le_correction
    (s : Finset ι) (w lam : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam : ∀ i ∈ s, 0 ≤ lam i) :
    doubleLogRemainder s w lam ≤ correction s w lam := by
  unfold doubleLogRemainder correction
  apply Finset.sum_le_sum
  intro i hi
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (doubleLog_le_self (hlam i hi)) (hw i hi))
    (by linarith [hlam i hi])

/-- The sharper remainder estimate keeps the full optimizer-tail square. -/
theorem doubleLogRemainder_le_cap_optimizerTail
    (s : Finset ι) (w lam : ι → ℝ) (L : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam : ∀ i ∈ s, 0 ≤ lam i)
    (hcap : ∀ i ∈ s, lam i ≤ L) :
    doubleLogRemainder s w lam ≤ (1+doubleLog L)*optimizerTail s w lam := by
  unfold doubleLogRemainder optimizerTail
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  have hpos : 0 < 1+lam i := by linarith [hlam i hi]
  have hid : w i * doubleLog (lam i)/(1+lam i) =
      w i * ((1+lam i)*doubleLog (lam i))/(1+lam i)^2 := by
    field_simp [ne_of_gt hpos]
  rw [hid]
  have h₁ := doubleLog_le_self (hlam i hi)
  have h₂ := mul_le_mul_of_nonneg_left
    (doubleLog_mono_nonneg (hlam i hi) (hcap i hi)) (hlam i hi)
  have hb : (1+lam i)*doubleLog (lam i) ≤ (1+doubleLog L)*lam i := by
    nlinarith only [h₁,h₂]
  have hm := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hb (hw i hi)) (sq_nonneg (1+lam i))
  convert hm using 1
  ring

/-- An unconditional complete-source upper bound with correction, rather
than total source mass, as its leading coefficient. -/
theorem doubleLog_moment_le_cap_correction_add_remainder
    (s : Finset ι) (w lam : ι → ℝ) (L : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam : ∀ i ∈ s, 0 ≤ lam i)
    (hcap : ∀ i ∈ s, lam i ≤ L) :
    moment s w lam doubleLog ≤ doubleLog L * correction s w lam +
      doubleLogRemainder s w lam := by
  rw [moment_eq_cap_correction_sub_contrast_add_remainder s w lam L hlam]
  linarith [doubleLogCapContrast_nonneg s w lam L hw hlam hcap]

theorem doubleLog_moment_le_cap_correction_add_tail
    (s : Finset ι) (w lam : ι → ℝ) (L : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam : ∀ i ∈ s, 0 ≤ lam i)
    (hcap : ∀ i ∈ s, lam i ≤ L) :
    moment s w lam doubleLog ≤ doubleLog L * correction s w lam +
      (1 + doubleLog L) * optimizerTail s w lam :=
  (doubleLog_moment_le_cap_correction_add_remainder s w lam L hw hlam hcap).trans
    (add_le_add le_rfl (doubleLogRemainder_le_cap_optimizerTail s w lam L hw hlam hcap))

/-- Exact scalar deficit needed for a strict feedback budget. The complete
positive remainder is present; no tightness assumption is substituted. -/
theorem doubleLog_feedback_iff_cap_contrast
    (s : Finset ι) (w lam : ι → ℝ) (L D E theta : ℝ)
    (hlam : ∀ i ∈ s, 0 ≤ lam i) (hD : 0 < D) :
    moment s w lam doubleLog / D ≤ E + theta * correction s w lam ↔
      (doubleLog L - theta * D) * correction s w lam +
        doubleLogRemainder s w lam - D * E ≤ doubleLogCapContrast s w lam L := by
  rw [div_le_iff₀ hD,
    moment_eq_cap_correction_sub_contrast_add_remainder s w lam L hlam]
  constructor <;> intro h <;> nlinarith only [h]


/-- A sharp scalar logarithm bound, obtained from exp r >= 1+r and
an exact nonnegative sixth-degree polynomial at r = sqrt x / 6. -/
theorem _root_.Real.log_one_add_le_sqrt {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ Real.sqrt x := by
  let r : ℝ := Real.sqrt x / 6
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have he : (6 : ℝ) * r = Real.sqrt x := by dsimp [r]; ring
  have hpoly : 1 + (6 * r) ^ 2 ≤ (1 + r) ^ 6 := by
    have hn : 0 ≤ r * (20 * (r - 21 / 40) ^ 2 + 39 / 80 +
        15 * r ^ 3 + 6 * r ^ 4 + r ^ 5) := by positivity
    nlinarith only [hn]
  have hbase : 1 + r ≤ Real.exp r := by linarith [Real.add_one_le_exp r]
  have hpow : (1 + r) ^ 6 ≤ (Real.exp r) ^ 6 :=
    pow_le_pow_left₀ (by positivity : 0 ≤ 1 + r) hbase 6
  have hexp : (Real.exp r) ^ 6 = Real.exp (Real.sqrt x) := by
    simpa [he] using (Real.exp_nat_mul r 6).symm
  have hbound : 1 + x ≤ Real.exp (Real.sqrt x) := by
    calc
      1 + x = 1 + (6 * r) ^ 2 := by rw [he, Real.sq_sqrt hx]
      _ ≤ (1 + r) ^ 6 := hpoly
      _ ≤ (Real.exp r) ^ 6 := hpow
      _ = _ := hexp
  exact (Real.log_le_iff_le_exp (by positivity : 0 < 1 + x)).mpr hbound

theorem doubleLog_sq_le_self {x : ℝ} (hx : 0 ≤ x) : (doubleLog x) ^ 2 ≤ x := by
  have hlog := Real.log_nonneg (by linarith : 1 ≤ 1 + x)
  have h₁ := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + Real.log (1 + x))
  have hp : doubleLog x ≤ Real.sqrt x := by
    dsimp [doubleLog]
    linarith [Real.log_one_add_le_sqrt hx]
  have hsq := (sq_le_sq₀ (doubleLog_nonneg hx) (Real.sqrt_nonneg x)).mpr hp
  simpa only [Real.sq_sqrt hx] using hsq

/-- Weighted Cauchy--Schwarz uses the complete total source and physical
optimizer-tail square, independently of any eigenvalue cap. -/
theorem doubleLogRemainder_sq_le_mass_mul_optimizerTail
    (s : Finset ι) (w lam : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam : ∀ i ∈ s, 0 ≤ lam i) :
    (doubleLogRemainder s w lam) ^ 2 ≤ mass s w * optimizerTail s w lam := by
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (r := fun i => w i * doubleLog (lam i) / (1 + lam i))
    (f := w) (g := fun i => w i * lam i / (1 + lam i) ^ 2)
    hw (by intro i hi; exact div_nonneg (mul_nonneg (hw i hi) (hlam i hi)) (sq_nonneg _))
    (by
      intro i hi
      rw [div_pow, mul_pow]
      calc
        _ ≤ w i ^ 2 * lam i / (1 + lam i) ^ 2 :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left (doubleLog_sq_le_self (hlam i hi)) (sq_nonneg _))
            (sq_nonneg _)
        _ = w i * (w i * lam i / (1 + lam i) ^ 2) := by ring)

/-- The source remainder is quantitatively vanishing whenever source mass
is bounded and the literal complete optimizer tail tends to zero. -/
theorem doubleLogRemainder_le_sqrt_mass_tail
    (s : Finset ι) (w lam : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam : ∀ i ∈ s, 0 ≤ lam i) :
    doubleLogRemainder s w lam ≤ Real.sqrt (mass s w * optimizerTail s w lam) := by
  have hsq := doubleLogRemainder_sq_le_mass_mul_optimizerTail s w lam hw hlam
  have hnonneg : 0 ≤ mass s w * optimizerTail s w lam := by
    exact mul_nonneg (Finset.sum_nonneg hw) (optimizerTail_nonneg s w lam hw hlam)
  have hs := Real.sq_sqrt hnonneg
  have hr := doubleLogRemainder_nonneg s w lam hw hlam
  nlinarith [Real.sqrt_nonneg (mass s w * optimizerTail s w lam)]

/-- Finite outer-log Jensen proved by the exact tangent cancellation.
This is an unconditional upper estimate, not an arithmetic mean provider. -/
theorem sum_mul_log_one_add_le_log_average
    (s : Finset ι) (t a : ι → ℝ)
    (ht : ∀ i ∈ s, 0 ≤ t i) (ha : ∀ i ∈ s, 0 ≤ a i)
    (hT : 0 < ∑ i ∈ s, t i) :
    (∑ i ∈ s, t i * Real.log (1 + a i)) ≤
      (∑ i ∈ s, t i) *
        Real.log (1 + (∑ i ∈ s, t i * a i) / (∑ i ∈ s, t i)) := by
  let T : ℝ := ∑ i ∈ s, t i
  let A : ℝ := ∑ i ∈ s, t i * a i
  let u : ℝ := A / T
  have hT' : 0 < T := hT
  have hA : 0 ≤ A :=
    Finset.sum_nonneg (fun i hi => mul_nonneg (ht i hi) (ha i hi))
  have hu : 0 ≤ u := div_nonneg hA (le_of_lt hT')
  have h1u : 0 < 1 + u := by linarith
  have hTu : T * u = A := by
    dsimp [u]
    field_simp [ne_of_gt hT']
  have htangent : ∀ i ∈ s,
      Real.log (1 + a i) ≤ Real.log (1 + u) + (a i - u) / (1 + u) := by
    intro i hi
    have h1a : 0 < 1 + a i := by linarith [ha i hi]
    have hlog := Real.log_le_sub_one_of_pos (div_pos h1a h1u)
    rw [Real.log_div (ne_of_gt h1a) (ne_of_gt h1u)] at hlog
    have hratio : (1 + a i) / (1 + u) - 1 = (a i - u) / (1 + u) := by
      field_simp [ne_of_gt h1u]
      ring
    rw [hratio] at hlog
    linarith
  change (∑ i ∈ s, t i * Real.log (1 + a i)) ≤ T * Real.log (1 + u)
  calc
    _ ≤ ∑ i ∈ s, t i * (Real.log (1 + u) + (a i - u) / (1 + u)) :=
      Finset.sum_le_sum (fun i hi =>
        mul_le_mul_of_nonneg_left (htangent i hi) (ht i hi))
    _ = ∑ i ∈ s, (t i * Real.log (1 + u) +
        (t i * a i - t i * u) / (1 + u)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = T * Real.log (1 + u) + (A - T * u) / (1 + u) := by
      simp only [div_eq_mul_inv, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, ← Finset.sum_mul]
      rfl
    _ = T * Real.log (1 + u) := by
      rw [hTu, sub_self, zero_div, add_zero]

/-- The complete correction-weighted first logarithmic moment. -/
def correctionLogMoment (s : Finset ι) (w lam : ι → ℝ) : ℝ :=
  ∑ i ∈ s, (w i * lam i / (1 + lam i)) * Real.log (1 + lam i)

/-- A more arithmetic upper bound than the maximum eigenvalue cap.
Its source-weighted mean is literal and retains every conductor interaction. -/
theorem doubleLog_moment_le_correction_log_mean_add_remainder
    (s : Finset ι) (w lam : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hlam : ∀ i ∈ s, 0 ≤ lam i)
    (hT : 0 < correction s w lam) :
    moment s w lam doubleLog ≤ correction s w lam *
      Real.log (1 + correctionLogMoment s w lam / correction s w lam) +
        doubleLogRemainder s w lam := by
  rw [moment_eq_correctionDoubleLog_add_remainder s w lam hlam]
  refine add_le_add ?_ le_rfl
  exact sum_mul_log_one_add_le_log_average s
    (fun i => w i * lam i / (1 + lam i))
    (fun i => Real.log (1 + lam i))
    (by
      intro i hi
      exact div_nonneg (mul_nonneg (hw i hi) (hlam i hi))
        (by linarith [hlam i hi]))
    (by intro i hi; exact Real.log_nonneg (by linarith [hlam i hi])) hT

end RiemannResearch.Analysis.FiniteSpectralBudget
