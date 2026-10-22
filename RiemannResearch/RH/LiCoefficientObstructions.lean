import RiemannResearch.RH.ClassicalArithmeticObstructions
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic.FieldSimp

/-!
# Concrete Li coefficients and their requested off-line-zero growth targets

Source: user-provided catalogue, group 34, and the standard Li coefficient
definition in https://arxiv.org/abs/1304.7895. The reference supports the
criterion and exponential obstruction. The two-sign limsup equality is a
research target whose generating-function and Pringsheim proof is not yet
formalized here.

The xi function is regularized at 0 and 1 before derivatives are taken.
The formula uses Mathlib's entire completedRiemannZeta₀, so it never takes
derivatives of the totalized pole-canceling product at its incorrectly
assigned endpoint value. The coefficient index is the conventional n >= 1,
with lambda_0 defined as zero.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.ClassicalObstruction

/-- Entire regularization of s(s-1)Λ(s)/2, with xi(0) = xi(1) = 1/2. -/
def liXi (s : ℂ) : ℂ := (1 + s * (s - 1) * completedRiemannZeta₀ s) / 2

def liCoefficient (n : ℕ) : ℝ :=
  if n = 0 then 0 else
    (((Nat.factorial (n - 1) : ℂ)⁻¹) *
      iteratedDeriv n (fun s : ℂ => s ^ (n - 1) * Complex.log (liXi s)) 1).re

def liZeroRadius (ρ : ℂ) : ℝ := ‖1 - 1 / ρ‖

/-- The nearest transformed right-hand zero is attained, not a default sInf. -/
def NearestLiZeroRadius (R : ℝ) : Prop :=
  0 < R ∧ R < 1 ∧
  (∃ ρ : ℂ, RightZero ρ ∧ liZeroRadius ρ = R) ∧
  ∀ ρ : ℂ, RightZero ρ → R ≤ liZeroRadius ρ

def positiveLiRoot (n : ℕ) : ℝ :=
  (max (liCoefficient n) 0) ^ ((n : ℝ)⁻¹)

def negativeLiRoot (n : ℕ) : ℝ :=
  (max (-liCoefficient n) 0) ^ ((n : ℝ)⁻¹)

/-- Precise group 34 target, including the existence of the minimizing radius. -/
def LiTwoSignExponentialGrowthTarget : Prop :=
  ¬ RiemannHypothesis → ∃ R : ℝ, NearestLiZeroRadius R ∧
    Filter.limsup positiveLiRoot atTop = R⁻¹ ∧
    Filter.limsup negativeLiRoot atTop = R⁻¹

/-- The stated infinite-sign consequence, kept separate from the growth target. -/
def LiInfiniteBothSignsTarget : Prop :=
  ¬ RiemannHypothesis → ∀ N : ℕ,
    (∃ n : ℕ, N < n ∧ 0 < liCoefficient n) ∧
    (∃ n : ℕ, N < n ∧ liCoefficient n < 0)

theorem liXi_one : liXi 1 = 1 / 2 := by simp [liXi]

theorem liXi_zero : liXi 0 = 1 / 2 := by simp [liXi]

theorem liCoefficient_zero : liCoefficient 0 = 0 := by simp [liCoefficient]

/-- The exact transformed-zero radius identity, before asymptotic arguments. -/
theorem liZeroRadius_eq_norm_quotient {ρ : ℂ} (hρ : ρ ≠ 0) :
    liZeroRadius ρ = ‖ρ - 1‖ / ‖ρ‖ := by
  have h : (1 : ℂ) - 1 / ρ = (ρ - 1) / ρ := by
    field_simp [hρ]
  rw [liZeroRadius, h, norm_div]

/-- Exact relation between the Li generating-function radius and the same
horizontal zero defect appearing in the projection/energy inequalities. -/
theorem liZeroRadius_energy_identity {ρ : ℂ} (hρ : ρ ≠ 0) :
    liZeroRadius ρ ^ 2 * ‖ρ‖ ^ 2 = ‖ρ‖ ^ 2 - (2 * ρ.re - 1) := by
  rw [liZeroRadius_eq_norm_quotient hρ, div_pow,
    div_mul_cancel₀ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hρ))]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.one_re, Complex.one_im]
  ring

/-- Every actual right-hand zero gives a radius strictly between zero and one.
This is geometric input; existence of the minimum and coefficient growth are
still genuine analytic obligations. -/
theorem liZeroRadius_mem_Ioo {ρ : ℂ} (hρ : RightZero ρ) :
    liZeroRadius ρ ∈ Set.Ioo (0 : ℝ) 1 := by
  have hρ0 : ρ ≠ 0 := by
    intro h
    have := hρ.2.1
    norm_num [h] at this
  have hρ1 : ρ ≠ 1 := by
    intro h
    have := hρ.2.2
    norm_num [h] at this
  have hnorm : ‖ρ - 1‖ ^ 2 = ‖ρ‖ ^ 2 - 2 * ρ.re + 1 := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.one_re, Complex.one_im]
    ring
  have hlt : ‖ρ - 1‖ < ‖ρ‖ := by
    nlinarith [norm_nonneg (ρ - 1), norm_nonneg ρ, hρ.2.1]
  rw [liZeroRadius_eq_norm_quotient hρ0]
  exact ⟨div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hρ1))
    (norm_pos_iff.mpr hρ0), (div_lt_one (norm_pos_iff.mpr hρ0)).mpr hlt⟩

end RiemannResearch.RH.ClassicalObstruction
