/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotGaussianEuler
import RiemannResearch.Analysis.GaussianRayRotation
import RiemannResearch.RH.PrimeTreeExpSubstitution
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The actual Gaussian Euler branches as outward ray integrals

Source: S. A. C. Baluyot, *On the Zeros of Riemann's Zeta-function*
(2017), Lemma 3.1.7 and Section 3.3, pp. 104-105 and 116-117.
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320
The proof uses the exact Euler evaluation already in the repository
and a positive exponential change of variables. Both phases retain
the factor omega^(1-2*l), the frequency 2*pi*omega and outward orientation.
-/

noncomputable section
open Complex MeasureTheory Set Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ConreyBaluyot

private theorem eulerBranch_log_parameterization (l Δ u v : ℝ) {ω : ℝ}
    (hω : 0 < ω) :
    gaussianArithmeticEulerBranch l Δ u ω v =
      (ω : ℂ)^((1-2*l : ℝ) : ℂ) *
        ∫ x : ℝ, Complex.exp (
          ((1-l : ℝ) : ℂ)*((x : ℂ)+(v : ℂ)*I) +
          I*u*((x : ℂ)+(v : ℂ)*I) -
          ((Δ^2/4 : ℝ) : ℂ)*((x : ℂ)+(v : ℂ)*I)^2 -
          ((2*Real.pi*ω : ℝ) : ℂ)*Complex.exp (x : ℂ)) := by
  let c : ℝ := Real.log (2*Real.pi) + Real.log ω
  let g (x : ℝ) : ℂ :=
    ((Real.exp (-x) : ℂ) * (x : ℂ) ^ ((1 - ((2*l : ℝ) : ℂ)) - 1)) *
      Complex.exp (((l : ℂ)+I*u) *
        (-Complex.log (2*Real.pi : ℂ)-Complex.log (ω : ℂ)+I*v+Complex.log (x : ℂ)) -
        (Δ : ℂ)^2 *
        (-Complex.log (2*Real.pi : ℂ)-Complex.log (ω : ℂ)+I*v+Complex.log (x : ℂ))^2/4)
  let P : ℂ := Complex.exp ((1-((2*l : ℝ) : ℂ)) *
    (-Complex.log (2*Real.pi : ℂ)+I*v))
  change P * (∫ x : ℝ in Ioi 0, g x) = _
  rw [← integral_comp_exp_full]
  rw [← integral_add_right_eq_self (fun x : ℝ => Real.exp x • g (Real.exp x)) c]
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  refine Eventually.of_forall fun x => ?_
  have hπ : 0 < 2*Real.pi := by positivity
  have hc : Real.exp c = 2*Real.pi*ω := by
    dsimp [c]
    rw [Real.exp_add, Real.exp_log hπ, Real.exp_log hω]
  have hlog : Complex.log ((Real.exp (x+c) : ℝ) : ℂ) = ((x+c : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]
    exact Complex.log_exp (by simpa using neg_neg_of_pos Real.pi_pos)
      (by simpa using Real.pi_pos.le)
  have hr : ((Real.exp (x+c) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have hw : (ω : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hω.ne'
  dsimp [P, g]
  rw [Complex.cpow_def_of_ne_zero hr,
    Complex.cpow_def_of_ne_zero hw, hlog]
  rw [show (2*Real.pi : ℂ) = ((2*Real.pi : ℝ) : ℂ) by push_cast; rfl,
    ← Complex.ofReal_log hπ.le, ← Complex.ofReal_log hω.le]
  simp only [Complex.ofReal_exp, Complex.ofReal_neg, ← Complex.exp_add]
  congr 1
  have hc' : Complex.exp ((x+c : ℝ) : ℂ) =
      ((2*Real.pi*ω : ℝ) : ℂ) * Complex.exp (x : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_add, hc]
    push_cast
    ring
  rw [hc']
  dsimp [c]
  push_cast
  ring

/-- Each actual Euler branch is exactly an imaginary-axis logarithmic integral. -/
theorem gaussianArithmeticEulerBranch_eq_logIntegral (l Δ u : ℝ) {ω τ : ℝ}
    (hω : 0 < ω) (hτ : τ = 1 ∨ τ = -1) :
    gaussianArithmeticEulerBranch l Δ u ω (τ*(Real.pi/2)) =
      (ω : ℂ)^((1-2*l : ℝ) : ℂ) *
        ∫ x : ℝ, gaussianRayLogKernel l Δ u (τ*(2*Real.pi*ω))
          ((x : ℂ)+(τ*(Real.pi/2) : ℝ)*I) := by
  rw [eulerBranch_log_parameterization l Δ u _ hω]
  congr 1
  apply integral_congr_ae
  refine Eventually.of_forall fun x => ?_
  dsimp only
  unfold gaussianRayLogKernel
  apply congrArg Complex.exp
  have he : Complex.exp ((τ*(Real.pi/2) : ℝ)*I) = (τ : ℂ)*I := by
    rcases hτ with rfl | rfl <;>
      simp [Complex.exp_neg, Complex.exp_mul_I]
  rw [Complex.exp_add, he]
  have ht : τ^2 = 1 := by rcases hτ with rfl | rfl <;> norm_num
  have ht' : (τ : ℂ)^2 = 1 := by exact_mod_cast ht
  push_cast
  ring_nf
  simp [Complex.I_sq, ht']
  ring

/-- Exact Euler-to-ray formula for either sign and any angle in [0,pi). -/
theorem gaussianArithmeticEulerBranch_eq_ray (l u : ℝ) {Δ ω θ τ : ℝ}
    (hΔ : 0 < Δ) (hω : 0 < ω) (hθ : θ ∈ Ico 0 Real.pi)
    (hτ : τ = 1 ∨ τ = -1) :
    gaussianArithmeticEulerBranch l Δ u ω (τ*(Real.pi/2)) =
      (ω : ℂ)^((1-2*l : ℝ) : ℂ) *
        gaussianRayIntegral l Δ u (τ*(2*Real.pi*ω)) (τ*θ) := by
  have hb : -Real.pi < τ*θ ∧ τ*θ ≤ Real.pi := by
    rcases hτ with rfl | rfl <;> simp only [one_mul, neg_one_mul] <;>
      constructor <;> linarith [Real.pi_pos, hθ.1, hθ.2]
  rw [gaussianArithmeticEulerBranch_eq_logIntegral l Δ u hω hτ,
    gaussianRayIntegral_eq_log_integral l Δ u _ _ hb.1 hb.2]
  congr 1
  apply gaussianRayLogKernel_integral_angle_independent l u hΔ
    (show 0 ≤ 2*Real.pi*ω by positivity)
    (show Real.pi/2 ∈ Icc 0 Real.pi by constructor <;> linarith [Real.pi_pos])
    ⟨hθ.1, hθ.2.le⟩ hτ

/-- The normalized pair of outward rays with the natural-index zero convention. -/
def gaussianArithmeticRayValue (l Δ u ω θ : ℝ) : ℂ :=
  if 0 < ω then (ω : ℂ)^((1-2*l : ℝ) : ℂ) *
    (gaussianRayIntegral l Δ u (2*Real.pi*ω) θ +
      gaussianRayIntegral l Δ u (-(2*Real.pi*ω)) (-θ)) else 0

theorem gaussianArithmeticEulerValue_eq_rayValue (l u ω : ℝ) {Δ θ : ℝ}
    (hΔ : 0 < Δ) (hθ : θ ∈ Ico 0 Real.pi) :
    gaussianArithmeticEulerValue l Δ u ω = gaussianArithmeticRayValue l Δ u ω θ := by
  by_cases hω : 0 < ω
  · have hp := gaussianArithmeticEulerBranch_eq_ray l u hΔ hω hθ
      (Or.inl rfl : (1:ℝ)=1 ∨ (1:ℝ) = -1)
    have hm := gaussianArithmeticEulerBranch_eq_ray l u hΔ hω hθ
      (Or.inr rfl : (-1:ℝ)=1 ∨ (-1:ℝ) = -1)
    simp only [one_mul, neg_one_mul] at hp hm
    simp only [gaussianArithmeticEulerValue, gaussianArithmeticRayValue, hω, if_true, hp, hm, mul_add]
  · simp [gaussianArithmeticEulerValue, gaussianArithmeticRayValue, hω]

/-- Actual scalar transform, with its normalization and both ray orientations. -/
theorem gaussianArithmeticTransform_eq_rayValue (l u : ℝ) {c Δ ω θ : ℝ}
    (hc0 : 0 < c) (hc : 0 < 1 - 2*l + c) (hΔ : 0 < Δ) (hω : 0 ≤ ω)
    (hθ : θ ∈ Ico 0 Real.pi) :
    gaussianArithmeticTransform l Δ u c ω =
      ((Δ*Real.sqrt Real.pi : ℝ) : ℂ) * gaussianArithmeticRayValue l Δ u ω θ := by
  rw [gaussianArithmeticTransform_eq_eulerValue l u hc0 hc hΔ hω,
    gaussianArithmeticEulerValue_eq_rayValue l u ω hΔ hθ]

/-- The actual finite mollifier coefficients multiplying the exact paired rays. -/
def mollifiedGaussianRayTerm (σ y ε l Δ u θ : ℝ) (p : ℕ × ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ⌊y^(1+ε)⌋₊,
  ∑ k ∈ Finset.Icc 1 ⌊y^(1+ε)⌋₊,
    ((mollifierCoefficient σ y h * mollifierCoefficient σ y k) *
      (p.2 : ℂ)^(((2*l : ℝ) : ℂ)-1)/(k : ℂ)^((2*l : ℝ) : ℂ)) *
      gaussianArithmeticRayValue l Δ u (((p.1*p.2*h : ℕ) : ℝ)/(k : ℝ)) θ

theorem mollifiedGaussianEulerTerm_eq_rayTerm (σ y ε l u : ℝ) {Δ θ : ℝ}
    (hΔ : 0 < Δ) (hθ : θ ∈ Ico 0 Real.pi) (p : ℕ × ℕ) :
    mollifiedGaussianEulerTerm σ y ε l Δ u p =
      mollifiedGaussianRayTerm σ y ε l Δ u θ p := by
  simp only [mollifiedGaussianEulerTerm, mollifiedGaussianRayTerm,
    gaussianArithmeticEulerValue_eq_rayValue l u _ hΔ hθ]

/-- Absolute convergence of the paired ray series, including angle zero.
This does not interchange its two individual ray integrals with the series. -/
theorem summable_norm_mollifiedGaussianRayTerm (σ y ε l u : ℝ) {Δ θ : ℝ}
    (hΔ : 0 < Δ) (hθ : θ ∈ Ico 0 Real.pi) :
    Summable (fun p : ℕ × ℕ => ‖mollifiedGaussianRayTerm σ y ε l Δ u θ p‖) := by
  simpa only [mollifiedGaussianEulerTerm_eq_rayTerm σ y ε l u hΔ hθ] using
    summable_norm_mollifiedGaussianEulerTerm σ y ε l u hΔ

/-- The complete actual moment identity with both rays and the original signed residue. -/
theorem mollifiedGaussianMoment_eq_ray_series (σ ε u : ℝ) {y l Δ θ : ℝ}
    (hy : 0 < y) (hl : 0 < l) (hl' : l < 1) (hΔ : 0 < Δ)
    (hθ : θ ∈ Ico 0 Real.pi) :
    (mollifiedGaussianMoment σ y ε l Δ u : ℂ) =
      (∑' p : ℕ × ℕ, mollifiedGaussianRayTerm σ y ε l Δ u θ p) -
        ((2*Real.sqrt Real.pi/Δ : ℝ) : ℂ)*mollifiedGaussianPoleCoeff σ y ε l Δ u := by
  simpa only [mollifiedGaussianEulerTerm_eq_rayTerm σ y ε l u hΔ hθ] using
    mollifiedGaussianMoment_eq_euler_series σ ε u hy hl hl' hΔ

end RiemannResearch.Analysis.ConreyBaluyot
