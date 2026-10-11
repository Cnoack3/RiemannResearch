import RiemannResearch.Analysis.OrdinateCollisionCertificate
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Exact triangular Fourier energy identity

For any finite family of real ordinates, counted by occurrence labels,
the triangular average of the squared Fourier amplitude equals the finite
sinc-squared pair sum. Repeated ordinates and identical occurrences are retained.
Every identity is finite and unconditional.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Set

namespace RiemannResearch.Analysis.OrdinateCollisionCertificate

theorem half_integral_one_sub_div {R : ℝ} (hR : R ≠ 0) :
    (∫ u in (0 : ℝ)..R, (1 - u / R)) = R / 2 := by
  have hint : IntervalIntegrable (fun u : ℝ => 1 - u / R) volume 0 R :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun u : ℝ => u - u ^ 2 / (2 * R)) (1 - x / R) x := by
    intro x
    have hd := (hasDerivAt_id x).sub (((hasDerivAt_id x).pow 2).div_const (2 * R))
    convert hd using 1 <;> first | rfl | (field_simp [hR] <;> simp only [id_eq] <;> ring)
  calc
    _ = (R - R ^ 2 / (2 * R)) - (0 - 0 ^ 2 / (2 * R)) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) hint
    _ = _ := by field_simp [hR]; ring

theorem half_integral_weighted_cos {R v : ℝ} (hR : R ≠ 0) (hv : v ≠ 0) :
    (∫ u in (0 : ℝ)..R, (1 - u / R) * Real.cos (v * u)) =
      (1 - Real.cos (v * R)) / (R * v ^ 2) := by
  let primitive : ℝ → ℝ := fun u =>
    (1 - u / R) * Real.sin (v * u) / v - Real.cos (v * u) / (R * v ^ 2)
  have hderiv : ∀ x : ℝ,
      HasDerivAt primitive ((1 - x / R) * Real.cos (v * x)) x := by
    intro x
    have hlin : HasDerivAt (fun u : ℝ => v * u) v x := by
      simpa using (hasDerivAt_id x).const_mul v
    have hsin : HasDerivAt (fun u : ℝ => Real.sin (v * u))
        (Real.cos (v * x) * v) x := (Real.hasDerivAt_sin (v * x)).comp x hlin
    have hcos : HasDerivAt (fun u : ℝ => Real.cos (v * u))
        (-Real.sin (v * x) * v) x := (Real.hasDerivAt_cos (v * x)).comp x hlin
    have hweight : HasDerivAt (fun u : ℝ => 1 - u / R) (-(1 / R)) x := by
      exact ((hasDerivAt_id x).div_const R).const_sub 1
    have hd := ((hweight.mul hsin).div_const v).sub (hcos.div_const (R * v ^ 2))
    dsimp only [primitive]
    convert hd using 1 <;> first | rfl | (field_simp [hR, hv] <;> ring)
  have hint : IntervalIntegrable
      (fun u : ℝ => (1 - u / R) * Real.cos (v * u)) volume 0 R :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  calc
    _ = primitive R - primitive 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) hint
    _ = _ := by
      dsimp [primitive]
      simp only [mul_zero, Real.sin_zero, Real.cos_zero]
      field_simp [hR, hv]
      ring

/-- The normalized triangular transform is exactly a sinc square, including zero frequency. -/
theorem triangular_cos_transform {R : ℝ} (hR : 0 < R) (v : ℝ) :
    (1 / R) * (∫ u in (-R)..R, (1 - |u| / R) * Real.cos (v * u)) =
      sincSquared R v := by
  let f : ℝ → ℝ := fun u => (1 - |u| / R) * Real.cos (v * u)
  have hcont : Continuous f := by dsimp [f]; fun_prop
  have heven : ∀ u : ℝ, f (-u) = f u := by
    intro u
    simp [f, mul_neg, Real.cos_neg]
  have hneg : (∫ u in (-R)..0, f u) = ∫ u in (0 : ℝ)..R, f u := by
    have h := intervalIntegral.integral_comp_neg (f := f) (a := (0 : ℝ)) (b := R)
    simpa only [heven, neg_zero] using h.symm
  have hpos : (∫ u in (0 : ℝ)..R, f u) =
      ∫ u in (0 : ℝ)..R, (1 - u / R) * Real.cos (v * u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hR.le] at hu
    simp [f, abs_of_nonneg hu.1]
  have hwhole : (∫ u in (-R)..R, f u) =
      2 * ∫ u in (0 : ℝ)..R, (1 - u / R) * Real.cos (v * u) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable (-R) 0) (hcont.intervalIntegrable 0 R), hneg, hpos]
    ring
  change (1 / R) * (∫ u in (-R)..R, f u) = _
  rw [hwhole]
  by_cases hv : v = 0
  · subst v
    simp only [zero_mul, Real.cos_zero, mul_one]
    rw [half_integral_one_sub_div hR.ne']
    simp only [sincSquared, mul_zero, zero_div, Real.sinc_zero, one_pow]
    field_simp [hR.ne']
  · rw [half_integral_weighted_cos hR.ne' hv]
    have hx : R * v / 2 ≠ 0 := div_ne_zero (mul_ne_zero hR.ne' hv) (by norm_num)
    have hcos : Real.cos (v * R) = 1 - 2 * Real.sin (R * v / 2) ^ 2 := by
      convert Real.cos_two_mul_eq_one_sub (R * v / 2) using 1 <;> ring
    rw [hcos]
    unfold sincSquared
    rw [Real.sinc_of_ne_zero hx]
    field_simp [hR.ne', hv]
    ring

def occurrencePhase (u ordinate : ℝ) : ℂ :=
  Complex.exp (((u * ordinate : ℝ) : ℂ) * Complex.I)

theorem occurrencePhase_mul_conj (u a b : ℝ) :
    occurrencePhase u a * star (occurrencePhase u b) = occurrencePhase u (a - b) := by
  unfold occurrencePhase
  rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I, ← Complex.exp_add]
  congr 1
  push_cast
  ring

variable {ι : Type*} [Fintype ι]

def occurrenceAmplitude (frequency : ι → ℝ) (u : ℝ) : ℂ :=
  ∑ i, occurrencePhase u (frequency i)

/-- Exact cosine expansion; repeated occurrences remain present in both sums. -/
theorem occurrenceAmplitude_normSq (frequency : ι → ℝ) (u : ℝ) :
    Complex.normSq (occurrenceAmplitude frequency u) =
      ∑ i, ∑ j, Real.cos ((frequency i - frequency j) * u) := by
  have hs : (Complex.normSq (occurrenceAmplitude frequency u) : ℂ) =
      ∑ i, ∑ j, occurrencePhase u (frequency i - frequency j) := by
    rw [← Complex.mul_conj]
    unfold occurrenceAmplitude
    simp only [map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    simpa only [Complex.star_def] using occurrencePhase_mul_conj u (frequency i) (frequency j)
  have hre := congrArg Complex.re hs
  simpa only [Complex.ofReal_re, Complex.re_sum, occurrencePhase,
    Complex.exp_ofReal_mul_I_re, mul_comm u] using hre

def triangularBandEnergy (frequency : ι → ℝ) (R : ℝ) : ℝ :=
  (1 / R) * ∫ u in (-R)..R,
    (1 - |u| / R) * Complex.normSq (occurrenceAmplitude frequency u)

/-- The full exact triangular Fourier identity from the paper, with no limiting operation. -/
theorem triangularBandEnergy_eq_sincEnergy (frequency : ι → ℝ) {R : ℝ} (hR : 0 < R) :
    triangularBandEnergy frequency R = sincEnergy frequency R := by
  classical
  have hint : ∀ i j : ι, IntervalIntegrable
      (fun u : ℝ => (1 - |u| / R) * Real.cos ((frequency i - frequency j) * u))
      volume (-R) R := by
    intro i j
    exact Continuous.intervalIntegrable (by fun_prop) _ _
  unfold triangularBandEnergy
  calc
    _ = (1 / R) * (∑ i, ∑ j, ∫ u in (-R)..R,
        (1 - |u| / R) * Real.cos ((frequency i - frequency j) * u)) := by
      congr 1
      simp_rw [occurrenceAmplitude_normSq, Finset.mul_sum]
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i hi
        exact intervalIntegral.integral_finsetSum (fun j _ => hint i j)
      · intro i hi
        apply intervalIntegrable_iff.mpr
        exact integrable_finsetSum Finset.univ (fun j _ => (hint i j).def')
    _ = ∑ i, ∑ j, (1 / R) * (∫ u in (-R)..R,
        (1 - |u| / R) * Real.cos ((frequency i - frequency j) * u)) := by
      simp only [Finset.mul_sum]
    _ = ∑ i, ∑ j, sincSquared R (frequency i - frequency j) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact triangular_cos_transform hR (frequency i - frequency j)
    _ = sincEnergy frequency R := rfl

end RiemannResearch.Analysis.OrdinateCollisionCertificate
