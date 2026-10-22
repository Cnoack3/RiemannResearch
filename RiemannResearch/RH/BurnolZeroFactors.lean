import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Algebra of Burnol's zero factors

Statement source: J.-F. Burnol, *A note on Nyman's equivalent formulation
of the Riemann Hypothesis*, Theorem 1.2 and formula (2.1),
https://arxiv.org/abs/math/9910055. The elementary identities below are
proved directly; no zeta-zero location or Hardy-space theorem is assumed.
-/

noncomputable section
namespace RiemannResearch.RH.Burnol

/-- The squared factor in Burnol's projection-norm product. -/
def factorSq (ρ : ℂ) : ℝ := Complex.normSq (1 - ρ) / Complex.normSq ρ

/-- The unsquared factor in Burnol's Theorem 1.2. -/
def factor (ρ : ℂ) : ℝ := ‖(1 - ρ) / ρ‖

theorem normSq_one_sub (ρ : ℂ) :
    Complex.normSq (1 - ρ) = Complex.normSq ρ + 1 - 2 * ρ.re := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re,
    Complex.sub_im, Complex.one_im]
  ring

theorem normSq_pos_of_half_lt {ρ : ℂ} (hρ : 1 / 2 < ρ.re) :
    0 < Complex.normSq ρ := by
  rw [Complex.normSq_apply]
  nlinarith [sq_nonneg ρ.im]

theorem factorSq_nonneg (ρ : ℂ) : 0 ≤ factorSq ρ := by
  exact div_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

/-- The exact defect of one squared zero factor. -/
theorem one_sub_factorSq {ρ : ℂ} (hρ : ρ ≠ 0) :
    1 - factorSq ρ = (2 * ρ.re - 1) / Complex.normSq ρ := by
  have hd : Complex.normSq ρ ≠ 0 := by simpa using hρ
  unfold factorSq
  rw [normSq_one_sub]
  field_simp
  ring

theorem factorSq_lt_one {ρ : ℂ} (hρ : 1 / 2 < ρ.re) : factorSq ρ < 1 := by
  rw [factorSq, div_lt_one (normSq_pos_of_half_lt hρ), normSq_one_sub]
  linarith

theorem factorSq_le_one {ρ : ℂ} (hρ : 1 / 2 ≤ ρ.re) : factorSq ρ ≤ 1 := by
  have hd : 0 < Complex.normSq ρ := by
    rw [Complex.normSq_apply]
    nlinarith [sq_nonneg ρ.im]
  rw [factorSq, div_le_one hd, normSq_one_sub]
  linarith

theorem factorSq_pos {ρ : ℂ} (hρ : ρ ≠ 0) (h1 : ρ ≠ 1) :
    0 < factorSq ρ := by
  apply div_pos
  · exact Complex.normSq_pos.mpr (sub_ne_zero.mpr (Ne.symm h1))
  · exact Complex.normSq_pos.mpr hρ

theorem factorSq_eq_one_iff {ρ : ℂ} (hρ : ρ ≠ 0) :
    factorSq ρ = 1 ↔ ρ.re = 1 / 2 := by
  have hd : Complex.normSq ρ ≠ 0 := by simpa using hρ
  rw [factorSq, div_eq_one_iff_eq hd, normSq_one_sub]
  constructor <;> intro h <;> linarith

theorem factorSq_conj (ρ : ℂ) : factorSq (star ρ) = factorSq ρ := by
  simp [factorSq, normSq_one_sub]

theorem factor_sq (ρ : ℂ) : factor ρ ^ 2 = factorSq ρ := by
  simp only [factor, factorSq, norm_div, div_pow, Complex.normSq_eq_norm_sq]

/-- The rational part of Burnol's normalized half-plane Blaschke factor. -/
def halfPlaneFactor (ρ s : ℂ) : ℂ := (s - ρ) / (s - (1 - star ρ))

/-- The reflection geometry underlying half-plane inner functions. -/
theorem reflected_normSq_sub (ρ s : ℂ) :
    Complex.normSq (s - (1 - star ρ)) - Complex.normSq (s - ρ) =
      (2 * s.re - 1) * (2 * ρ.re - 1) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  ring

/-- Exact defect before the unimodular normalization is introduced. -/
theorem one_sub_halfPlaneFactor_normSq (ρ s : ℂ)
    (hd : s - (1 - star ρ) ≠ 0) :
    1 - Complex.normSq (halfPlaneFactor ρ s) =
      (2 * s.re - 1) * (2 * ρ.re - 1) /
        Complex.normSq (s - (1 - star ρ)) := by
  have hd' : Complex.normSq (s - (1 - star ρ)) ≠ 0 := by simpa using hd
  rw [halfPlaneFactor, map_div₀]
  have h := reflected_normSq_sub ρ s
  field_simp
  nlinarith

/-- Every non-pole boundary value has modulus one. -/
theorem halfPlaneFactor_boundary_normSq (ρ s : ℂ) (hs : s.re = 1 / 2)
    (hd : s - (1 - star ρ) ≠ 0) :
    Complex.normSq (halfPlaneFactor ρ s) = 1 := by
  have h := one_sub_halfPlaneFactor_normSq ρ s hd
  rw [hs] at h
  norm_num at h
  linarith

/-- At the evaluation point one, the squared factor is exactly `factorSq`. -/
theorem halfPlaneFactor_one_normSq (ρ : ℂ) :
    Complex.normSq (halfPlaneFactor ρ 1) = factorSq ρ := by
  simp [halfPlaneFactor, factorSq, map_div₀]

/-- The factor has positive modulus away from zero and one. -/
theorem factor_pos {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) : 0 < factor ρ := by
  exact norm_pos_iff.mpr (div_ne_zero (sub_ne_zero.mpr h1.symm) h0)

theorem norm_halfPlaneFactor_one (ρ : ℂ) :
    ‖halfPlaneFactor ρ 1‖ = factor ρ := by
  simp [halfPlaneFactor, factor]

/-- Normalize the rational factor to have a positive value at one.
This is the normalization characterized by Burnol's formula (2.1). -/
def normalizedFactor (ρ s : ℂ) : ℂ :=
  halfPlaneFactor ρ s * (halfPlaneFactor ρ 1)⁻¹ * (factor ρ : ℂ)

theorem normalizedFactor_one {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    normalizedFactor ρ 1 = (factor ρ : ℂ) := by
  have hb : halfPlaneFactor ρ 1 ≠ 0 := by
    apply norm_pos_iff.mp
    rw [norm_halfPlaneFactor_one]
    exact factor_pos h0 h1
  simp [normalizedFactor, hb]

/-- The normalization is unimodular and preserves every modulus. -/
theorem norm_normalizedFactor {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) (s : ℂ) :
    ‖normalizedFactor ρ s‖ = ‖halfPlaneFactor ρ s‖ := by
  have hp := factor_pos h0 h1
  rw [normalizedFactor, norm_mul, norm_mul, norm_inv, norm_halfPlaneFactor_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
  field_simp

/-- Boundary values of a normalized factor have modulus one. -/
theorem norm_normalizedFactor_boundary {ρ s : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1)
    (hs : s.re = 1 / 2) (hd : s - (1 - star ρ) ≠ 0) :
    ‖normalizedFactor ρ s‖ = 1 := by
  rw [norm_normalizedFactor h0 h1]
  have h := halfPlaneFactor_boundary_normSq ρ s hs hd
  rw [Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg (halfPlaneFactor ρ s)]

/-- The logarithmic form connects the squared product with the BSY zero sum.
The analytic identification with the critical-line integral is separate. -/
theorem log_factorSq {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    Real.log (factorSq ρ) = -2 * Real.log ‖ρ / (1 - ρ)‖ := by
  have hn0 : ‖ρ‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  have hn1 : ‖1 - ρ‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr h1.symm)
  rw [factorSq, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
    Real.log_div (pow_ne_zero _ hn1) (pow_ne_zero _ hn0),
    Real.log_pow, Real.log_pow, norm_div, Real.log_div hn0 hn1]
  ring

end RiemannResearch.RH.Burnol
