/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.GaussianHorizontalShift
import RiemannResearch.RH.PrimeTreeExpSubstitution
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Gaussian ray rotation in logarithmic coordinates

Source: the user's continuation note, Section 5.2. The intended arithmetic
consumer is the rotation in S. A. C. Baluyot, *On the Zeros of Riemann's
Zeta-function* (2017), Lemma 3.1.7 and Section 3.3,
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320 .

The exact kernel norm yields a Gaussian majorant and a contour rotation
on the entire closed half-sector, including the undamped boundary.
The parameters l and u are arbitrary real numbers and the frequency can
vanish. This is fixed-parameter convergence, not a uniform height bound.
The explicit principal-log parameterization below transfers the result
back to outward ray integrals.
-/

noncomputable section
open Complex MeasureTheory Set Filter
open scoped Topology
namespace Complex

/-- Entire kernel after the substitution r = exp x. The signed angular
frequency b equals tau * 2*pi*omega in the arithmetic application. -/
def gaussianRayLogKernel (l Δ u b : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (((1-l : ℝ) : ℂ) * z + I * u * z -
    ((Δ^2 / 4 : ℝ) : ℂ) * z^2 + I * b * Complex.exp z)

theorem differentiable_gaussianRayLogKernel (l Δ u b : ℝ) :
    Differentiable ℂ (gaussianRayLogKernel l Δ u b) := by
  unfold gaussianRayLogKernel
  fun_prop

/-- Exact norm, retaining the damping term and the sign of the center. -/
theorem norm_gaussianRayLogKernel (l Δ u b x y : ℝ) :
    ‖gaussianRayLogKernel l Δ u b ((x : ℂ) + y * I)‖ =
      Real.exp ((1-l)*x-u*y-(Δ^2/4)*(x^2-y^2)-b*Real.exp x*Real.sin y) := by
  rw [gaussianRayLogKernel, Complex.norm_exp]
  congr 1
  simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im,
    Complex.exp_im, pow_two]
  ring

/-- A concrete uniform-in-angle majorant, with the linear term absorbed. -/
theorem norm_gaussianRayLogKernel_le {Δ : ℝ} (hΔ : 0 < Δ)
    (l u b x y A : ℝ) (hy : |y| ≤ A) (hb : 0 ≤ b * Real.sin y) :
    ‖gaussianRayLogKernel l Δ u b ((x : ℂ) + y * I)‖ ≤
      Real.exp (|u| *A + (Δ^2/4)*A^2 + (1-l)^2/(2*(Δ^2/4))) *
        Real.exp (-(Δ^2/8)*x^2) := by
  let q := Δ^2/4
  have hq : 0 < q := by dsimp [q]; positivity
  have hA : 0 ≤ A := (abs_nonneg y).trans hy
  have hysq : y^2 ≤ A^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg y) hy 2
  have huy : -u*y ≤ |u| *A := by
    calc
      _ ≤ |u*y| := by simpa only [neg_mul] using neg_le_abs (u*y)
      _ = |u| *|y| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hy (abs_nonneg u)
  have hx : (1-l)*x - q*x^2 ≤ (1-l)^2/(2*q) - (q/2)*x^2 := by
    have hs : 0 ≤ (q*x-(1-l))^2 := sq_nonneg _
    have he : ((1-l)^2/(2*q))*(2*q) = (1-l)^2 :=
      div_mul_cancel₀ _ (by positivity)
    nlinarith
  have hdamp : 0 ≤ b*Real.exp x*Real.sin y := by
    nlinarith [mul_nonneg hb (Real.exp_nonneg x)]
  rw [norm_gaussianRayLogKernel, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hyy := mul_le_mul_of_nonneg_left hysq hq.le
  dsimp [q] at hx hyy
  nlinarith

/-- Absolute convergence on every line in either closed half-sector. -/
theorem gaussianRayLogKernel_integrable (l u : ℝ) {Δ ω θ τ : ℝ}
    (hΔ : 0 < Δ) (hω : 0 ≤ ω) (hθ : θ ∈ Icc 0 Real.pi)
    (hτ : τ = 1 ∨ τ = -1) :
    Integrable (fun x : ℝ =>
      gaussianRayLogKernel l Δ u (τ*ω) ((x : ℂ) + (τ*θ : ℝ)*I)) := by
  have hy : |τ*θ| ≤ Real.pi := by
    rcases hτ with rfl | rfl <;> simp [abs_of_nonneg hθ.1, hθ.2]
  have hb : 0 ≤ (τ*ω)*Real.sin (τ*θ) := by
    rcases hτ with rfl | rfl <;>
      simpa using mul_nonneg hω (Real.sin_nonneg_of_mem_Icc hθ)
  have hc : Continuous (fun x : ℝ =>
      gaussianRayLogKernel l Δ u (τ*ω) ((x : ℂ) + (τ*θ : ℝ)*I)) :=
    (differentiable_gaussianRayLogKernel l Δ u (τ*ω)).continuous.comp
      (Complex.continuous_ofReal.add continuous_const)
  exact ((integrable_exp_neg_mul_sq (show 0 < Δ^2/8 by positivity)).const_mul
    (Real.exp (|u| *Real.pi + (Δ^2/4)*Real.pi^2 + (1-l)^2/(2*(Δ^2/4))))).mono'
      hc.aestronglyMeasurable (Eventually.of_forall fun x =>
        norm_gaussianRayLogKernel_le hΔ l u (τ*ω) x (τ*θ) Real.pi hy hb)

/-- Rotation from the real axis through a full closed half-sector. Both
finite vertical sides vanish, and convergence is proved rather than assumed. -/
theorem gaussianRayLogKernel_integral_rotate (l u : ℝ) {Δ ω θ τ : ℝ}
    (hΔ : 0 < Δ) (hω : 0 ≤ ω) (hθ : θ ∈ Icc 0 Real.pi)
    (hτ : τ = 1 ∨ τ = -1) :
    (∫ x : ℝ, gaussianRayLogKernel l Δ u (τ*ω) (x : ℂ)) =
      ∫ x : ℝ, gaussianRayLogKernel l Δ u (τ*ω) ((x : ℂ) + (τ*θ : ℝ)*I) := by
  apply (show (∫ x : ℝ, gaussianRayLogKernel l Δ u (τ*ω) (x : ℂ)) =
      ∫ x : ℝ, gaussianRayLogKernel l Δ u (τ*ω) ((x : ℂ) + (0:ℝ)*I) by simp).trans
  apply integral_horizontal_eq_of_gaussian_bound
    (q := Δ^2/8)
    (C := Real.exp (|u| *Real.pi + (Δ^2/4)*Real.pi^2 + (1-l)^2/(2*(Δ^2/4))))
    (by positivity)
    (fun z _ => differentiable_gaussianRayLogKernel l Δ u (τ*ω) z)
  intro x y hy
  have hangle : |y| ≤ Real.pi ∧ 0 ≤ (τ*ω)*Real.sin y := by
    rcases hτ with rfl | rfl
    · simp only [one_mul, uIcc_of_le hθ.1, mem_Icc] at hy ⊢
      exact ⟨by rw [abs_of_nonneg hy.1]; exact hy.2.trans hθ.2,
        mul_nonneg hω (Real.sin_nonneg_of_nonneg_of_le_pi hy.1 (hy.2.trans hθ.2))⟩
    · have hle : -θ ≤ 0 := neg_nonpos.mpr hθ.1
      simp only [neg_one_mul, uIcc_comm 0 (-θ), uIcc_of_le hle, mem_Icc] at hy ⊢
      have hn : 0 ≤ Real.sin (-y) :=
        Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hy.2]) (by linarith [hy.1, hθ.2])
      constructor
      · rw [abs_of_nonpos hy.2]; linarith [hy.1, hθ.2]
      · simpa using mul_nonneg hω hn
  exact norm_gaussianRayLogKernel_le hΔ l u (τ*ω) x y Real.pi hangle.1 hangle.2

/-- Any two angles in the same closed half-sector give the same integral. -/
theorem gaussianRayLogKernel_integral_angle_independent (l u : ℝ) {Δ ω θ₁ θ₂ τ : ℝ}
    (hΔ : 0 < Δ) (hω : 0 ≤ ω) (hθ₁ : θ₁ ∈ Icc 0 Real.pi)
    (hθ₂ : θ₂ ∈ Icc 0 Real.pi) (hτ : τ = 1 ∨ τ = -1) :
    (∫ x : ℝ, gaussianRayLogKernel l Δ u (τ*ω) ((x : ℂ) + (τ*θ₁ : ℝ)*I)) =
      ∫ x : ℝ, gaussianRayLogKernel l Δ u (τ*ω) ((x : ℂ) + (τ*θ₂ : ℝ)*I) :=
  (gaussianRayLogKernel_integral_rotate l u hΔ hω hθ₁ hτ).symm.trans
    (gaussianRayLogKernel_integral_rotate l u hΔ hω hθ₂ hτ)


/-- Outward ray integrand with the principal power, principal logarithm,
and the Jacobian exp(i*y) all explicit. -/
def gaussianRayIntegrand (l Δ u b y : ℝ) (r : ℝ) : ℂ :=
  ((r : ℂ) * Complex.exp ((y : ℂ)*I)) ^ (-(l : ℂ) + I*u) *
    Complex.exp (-((Δ^2/4 : ℝ) : ℂ) *
      (Complex.log ((r : ℂ) * Complex.exp ((y : ℂ)*I)))^2) *
    Complex.exp (I*b*((r : ℂ)*Complex.exp ((y : ℂ)*I))) *
    Complex.exp ((y : ℂ)*I)

/-- Both signs of the ray are oriented from zero outward. -/
def gaussianRayIntegral (l Δ u b y : ℝ) : ℂ :=
  ∫ r : ℝ in Ioi 0, gaussianRayIntegrand l Δ u b y r

theorem log_ray_exp (x y : ℝ) (hylo : -Real.pi < y) (hyhi : y ≤ Real.pi) :
    Complex.log ((Real.exp x : ℂ)*Complex.exp ((y : ℂ)*I)) =
      (x : ℂ)+(y : ℂ)*I := by
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  exact Complex.log_exp (by simpa using hylo) (by simpa using hyhi)

/-- Exact exponential parameterization, including the positive Jacobian. -/
theorem gaussianRayIntegrand_exp (l Δ u b x y : ℝ)
    (hylo : -Real.pi < y) (hyhi : y ≤ Real.pi) :
    (Real.exp x : ℂ) * gaussianRayIntegrand l Δ u b y (Real.exp x) =
      gaussianRayLogKernel l Δ u b ((x : ℂ)+(y : ℂ)*I) := by
  have hn : (Real.exp x : ℂ)*Complex.exp ((y : ℂ)*I) ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne') (Complex.exp_ne_zero _)
  unfold gaussianRayIntegrand
  rw [Complex.cpow_def_of_ne_zero hn, log_ray_exp x y hylo hyhi]
  rw [Complex.ofReal_exp]
  simp only [← Complex.exp_add]
  unfold gaussianRayLogKernel
  congr 1
  rw [Complex.exp_add]
  push_cast
  ring

/-- Equality with the whole horizontal integral, without an assumed exchange. -/
theorem gaussianRayIntegral_eq_log_integral (l Δ u b y : ℝ)
    (hylo : -Real.pi < y) (hyhi : y ≤ Real.pi) :
    gaussianRayIntegral l Δ u b y =
      ∫ x : ℝ, gaussianRayLogKernel l Δ u b ((x : ℂ)+(y : ℂ)*I) := by
  rw [gaussianRayIntegral, ← RiemannResearch.Analysis.integral_comp_exp_full]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simpa only [Complex.real_smul] using gaussianRayIntegrand_exp l Δ u b x y hylo hyhi

/-- The outward ray is absolutely integrable on both sides of the real axis,
including angle zero. Only the principal-log cut at pi is excluded. -/
theorem gaussianRayIntegrand_integrable (l u : ℝ) {Δ ω θ τ : ℝ}
    (hΔ : 0 < Δ) (hω : 0 ≤ ω) (hθ : θ ∈ Ico 0 Real.pi)
    (hτ : τ = 1 ∨ τ = -1) :
    IntegrableOn (gaussianRayIntegrand l Δ u (τ*ω) (τ*θ)) (Ioi 0) := by
  have hlo : -Real.pi < τ*θ := by
    rcases hτ with rfl | rfl <;> simp only [one_mul, neg_one_mul] <;>
      linarith [Real.pi_pos, hθ.1, hθ.2]
  have hhi : τ*θ ≤ Real.pi := by
    rcases hτ with rfl | rfl <;> simp only [one_mul, neg_one_mul] <;>
      linarith [Real.pi_pos, hθ.1, hθ.2]
  rw [← RiemannResearch.Analysis.integrable_comp_exp_full]
  have he : (fun x : ℝ => Real.exp x • gaussianRayIntegrand l Δ u (τ*ω) (τ*θ) (Real.exp x)) =
      (fun x : ℝ => gaussianRayLogKernel l Δ u (τ*ω) ((x : ℂ)+(τ*θ : ℝ)*I)) := by
    funext x
    simpa only [Complex.real_smul] using gaussianRayIntegrand_exp l Δ u (τ*ω) x (τ*θ) hlo hhi
  rw [he]
  exact gaussianRayLogKernel_integrable l u hΔ hω ⟨hθ.1, hθ.2.le⟩ hτ

/-- Exact principal-log ray rotation in either orientation, for every pair
of angles in [0,pi). This includes the oscillatory real-axis endpoint. -/
theorem gaussianRayIntegral_angle_independent (l u : ℝ) {Δ ω θ₁ θ₂ τ : ℝ}
    (hΔ : 0 < Δ) (hω : 0 ≤ ω) (hθ₁ : θ₁ ∈ Ico 0 Real.pi)
    (hθ₂ : θ₂ ∈ Ico 0 Real.pi) (hτ : τ = 1 ∨ τ = -1) :
    gaussianRayIntegral l Δ u (τ*ω) (τ*θ₁) =
      gaussianRayIntegral l Δ u (τ*ω) (τ*θ₂) := by
  have hb {θ : ℝ} (hθ : θ ∈ Ico 0 Real.pi) :
      -Real.pi < τ*θ ∧ τ*θ ≤ Real.pi := by
    rcases hτ with rfl | rfl <;> simp only [one_mul, neg_one_mul] <;>
      constructor <;> linarith [Real.pi_pos, hθ.1, hθ.2]
  rw [gaussianRayIntegral_eq_log_integral l Δ u (τ*ω) (τ*θ₁) (hb hθ₁).1 (hb hθ₁).2,
    gaussianRayIntegral_eq_log_integral l Δ u (τ*ω) (τ*θ₂) (hb hθ₂).1 (hb hθ₂).2]
  exact gaussianRayLogKernel_integral_angle_independent l u hΔ hω
    ⟨hθ₁.1, hθ₁.2.le⟩ ⟨hθ₂.1, hθ₂.2.le⟩ hτ


theorem gaussianRayLogKernel_zero_integrable (l u y : ℝ) {Δ : ℝ}
    (hΔ : 0 < Δ) :
    Integrable (fun x : ℝ => gaussianRayLogKernel l Δ u 0 ((x:ℂ)+(y:ℂ)*I)) := by
  have hc : Continuous (fun x : ℝ => gaussianRayLogKernel l Δ u 0 ((x:ℂ)+(y:ℂ)*I)) :=
    (differentiable_gaussianRayLogKernel l Δ u 0).continuous.comp
      (Complex.continuous_ofReal.add continuous_const)
  exact ((integrable_exp_neg_mul_sq (show 0 < Δ^2/8 by positivity)).const_mul
    (Real.exp (|u| * |y| + (Δ^2/4)*|y|^2 + (1-l)^2/(2*(Δ^2/4))))).mono'
      hc.aestronglyMeasurable (Eventually.of_forall fun x =>
        norm_gaussianRayLogKernel_le hΔ l u 0 x y |y| le_rfl (by simp))

theorem norm_gaussianRayLogKernel_zero_shift (l Δ u x y : ℝ) (N : ℕ) :
    ‖gaussianRayLogKernel l Δ u 0 ((x:ℂ)+(y:ℂ)*I)‖ *
        Real.exp (-(N:ℝ)*x) =
      ‖gaussianRayLogKernel (l+N) Δ u 0 ((x:ℂ)+(y:ℂ)*I)‖ := by
  rw [norm_gaussianRayLogKernel, norm_gaussianRayLogKernel, ← Real.exp_add]
  congr 1
  ring


end Complex
