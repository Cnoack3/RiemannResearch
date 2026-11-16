/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.GaussianRayRotation
import RiemannResearch.RH.PrimeTreeExpSubstitution
import RiemannResearch.Analysis.ConreyBaluyotEstermannDampedSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Joint absolute convergence for Gaussian damped Estermann integrals

Source: user-provided ray-rotation continuation, Section 6, and Baluyot (2017),
Section 3.3. The factorial damping estimate absorbs arbitrary complex powers.
After r = exp x, degeneration of the damping at r = 0 contributes exp(-N*x),
which is absorbed by changing l to l+N in the Gaussian kernel. This proves
summability of the integrals of norms before exchanging sum and integral.
All constants are fixed-parameter; no uniform growing-height provider follows.
-/

noncomputable section
open Complex MeasureTheory Set Filter
open scoped Topology BigOperators


namespace RiemannResearch.Analysis.ConreyBaluyot

/-- The joint summand in logarithmic ray coordinates. -/
def gaussianEstermannLogTerm {K : ℕ} [NeZero K] (h : ZMod K)
    (α β : ℂ) (l Δ u y : ℝ) (w : ℝ → ℂ) (p : ℕ × ℕ) (x : ℝ) : ℂ :=
  gaussianRayLogKernel l Δ u 0 ((x:ℂ)+(y:ℂ)*I) *
    estermannDampedTerm h α β (w x) p

theorem norm_gaussianEstermannLogTerm_le {K : ℕ} [NeZero K] (h : ZMod K)
    (α β : ℂ) (l Δ u y : ℝ) {w : ℝ → ℂ} {d : ℝ}
    (hd : 0 < d) (hw : ∀ x, (w x).im = d * Real.exp x) (p : ℕ × ℕ) (N : ℕ) (x : ℝ) :
    ‖gaussianEstermannLogTerm h α β l Δ u y w p x‖ ≤
      (‖estermannTerm h (α+(N:ℂ)) (β+(N:ℂ)) p‖ *
        ((N.factorial : ℝ)/(2*Real.pi*d)^N)) *
          ‖gaussianRayLogKernel (l+N) Δ u 0 ((x:ℂ)+(y:ℂ)*I)‖ := by
  have hpos : 0 < (w x).im := by rw [hw]; positivity
  have he : (N.factorial : ℝ)/(2*Real.pi*(w x).im)^N =
      ((N.factorial : ℝ)/(2*Real.pi*d)^N)*Real.exp (-(N:ℝ)*x) := by
    rw [hw, show 2*Real.pi*(d * Real.exp x) = (2*Real.pi*d)*Real.exp x by ring,
      mul_pow, ← Real.exp_nat_mul, show -(N:ℝ)*x = -((N:ℝ)*x) by ring,
      Real.exp_neg]
    ring
  unfold gaussianEstermannLogTerm
  rw [norm_mul]
  calc
    _ ≤ ‖gaussianRayLogKernel l Δ u 0 ((x:ℂ)+(y:ℂ)*I)‖ *
        (‖estermannTerm h (α+(N:ℂ)) (β+(N:ℂ)) p‖ *
          (((N.factorial : ℝ)/(2*Real.pi*d)^N)*Real.exp (-(N:ℝ)*x))) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [he] using norm_estermannDampedTerm_le_shift h α β hpos p N
    _ = _ := by
      rw [← norm_gaussianRayLogKernel_zero_shift l Δ u x y N]
      ring

theorem gaussianEstermannLogTerm_integrable {K : ℕ} [NeZero K] (h : ZMod K)
    (α β : ℂ) (l u y : ℝ) {Δ d : ℝ} {w : ℝ → ℂ}
    (hΔ : 0 < Δ) (hd : 0 < d) (hwc : Continuous w)
    (hw : ∀ x, (w x).im = d * Real.exp x) (p : ℕ × ℕ) :
    Integrable (gaussianEstermannLogTerm h α β l Δ u y w p) := by
  have hc : Continuous (gaussianEstermannLogTerm h α β l Δ u y w p) := by
    unfold gaussianEstermannLogTerm estermannDampedTerm gaussianRayLogKernel
    fun_prop
  apply ((gaussianRayLogKernel_zero_integrable l u y hΔ).norm.const_mul
    (‖estermannTerm h α β p‖)).mono' hc.aestronglyMeasurable
  exact Eventually.of_forall fun x => by
    simpa using norm_gaussianEstermannLogTerm_le h α β l Δ u y hd hw p 0 x

/-- Joint absolute convergence, not merely pointwise damping. -/
theorem summable_integral_norm_gaussianEstermannLogTerm {K : ℕ} [NeZero K] (h : ZMod K)
    (α β : ℂ) (l u y : ℝ) {Δ d : ℝ} {w : ℝ → ℂ}
    (hΔ : 0 < Δ) (hd : 0 < d) (hwc : Continuous w)
    (hw : ∀ x, (w x).im = d * Real.exp x) :
    Summable (fun p : ℕ × ℕ => ∫ x : ℝ,
      ‖gaussianEstermannLogTerm h α β l Δ u y w p x‖) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max (1-α.re) (1-β.re))
  have ha : 1 < (α+(N:ℂ)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith [(le_max_left (1-α.re) (1-β.re)).trans_lt hN]
  have hb : 1 < (β+(N:ℂ)).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith [(le_max_right (1-α.re) (1-β.re)).trans_lt hN]
  let C : ℝ := (N.factorial : ℝ)/(2*Real.pi*d)^N
  let B := ∫ x : ℝ, ‖gaussianRayLogKernel (l+N) Δ u 0 ((x:ℂ)+(y:ℂ)*I)‖
  have hs := ((summable_norm_estermannTerm h ha hb).mul_right C).mul_right B
  apply Summable.of_nonneg_of_le (fun p => integral_nonneg fun x => norm_nonneg _) _ hs
  intro p
  have hint := gaussianEstermannLogTerm_integrable h α β l u y hΔ hd hwc hw p
  have hmajor := (gaussianRayLogKernel_zero_integrable (l+N) u y hΔ).norm.const_mul
    (‖estermannTerm h (α+(N:ℂ)) (β+(N:ℂ)) p‖*C)
  have hi := integral_mono hint.norm hmajor
    (norm_gaussianEstermannLogTerm_le h α β l Δ u y hd hw p N)
  simpa only [integral_const_mul, C, B] using hi

/-- Fubini for the actual damped Estermann series on any continuous profile
with Im(w(x)) = d exp(x), d > 0, and arbitrary complex shifts. -/
theorem integral_gaussian_mul_estermannDampedSeries {K : ℕ} [NeZero K] (h : ZMod K)
    (α β : ℂ) (l u y : ℝ) {Δ d : ℝ} {w : ℝ → ℂ}
    (hΔ : 0 < Δ) (hd : 0 < d) (hwc : Continuous w)
    (hw : ∀ x, (w x).im = d * Real.exp x) :
    (∫ x : ℝ, gaussianRayLogKernel l Δ u 0 ((x:ℂ)+(y:ℂ)*I) *
      estermannDampedSeries h α β (w x)) =
        ∑' p : ℕ × ℕ, ∫ x : ℝ, gaussianEstermannLogTerm h α β l Δ u y w p x := by
  simp_rw [estermannDampedSeries, ← tsum_mul_left]
  exact (integral_tsum_of_summable_integral_norm
    (gaussianEstermannLogTerm_integrable h α β l u y hΔ hd hwc hw)
    (summable_integral_norm_gaussianEstermannLogTerm h α β l u y hΔ hd hwc hw)).symm

/-- The rational-phase displacement used on either outward ray. -/
def estermannRayDisplacement (a τ θ x : ℝ) : ℂ :=
  ((τ*a : ℝ) : ℂ)*(Complex.exp ((x:ℂ)+(τ * θ : ℝ)*I)-1)

theorem estermannRayDisplacement_im (a θ x : ℝ) {τ : ℝ}
    (hτ : τ = 1 ∨ τ = -1) :
    (estermannRayDisplacement a τ θ x).im = (a*Real.sin θ)*Real.exp x := by
  rcases hτ with rfl | rfl <;>
    simp [estermannRayDisplacement, Complex.mul_im, Complex.exp_im] <;> ring

/-- Both signs of the rotated rational phase lie strictly in the upper half-plane. -/
theorem estermannRayDisplacement_im_pos {a τ θ : ℝ} (ha : 0 < a)
    (hθ : θ ∈ Ioo 0 Real.pi) (hτ : τ = 1 ∨ τ = -1) (x : ℝ) :
    0 < (estermannRayDisplacement a τ θ x).im := by
  rw [estermannRayDisplacement_im a θ x hτ]
  exact mul_pos (mul_pos ha (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)) (Real.exp_pos x)

/-- The joint absolute-convergence theorem applied to the actual ray geometry. -/
theorem summable_integral_norm_estermannRay {K : ℕ} [NeZero K] (h : ZMod K)
    (α β : ℂ) (l u : ℝ) {Δ a τ θ : ℝ} (hΔ : 0 < Δ) (ha : 0 < a)
    (hθ : θ ∈ Ioo 0 Real.pi) (hτ : τ = 1 ∨ τ = -1) :
    Summable (fun p : ℕ × ℕ => ∫ x : ℝ,
      ‖gaussianEstermannLogTerm h α β l Δ u (τ * θ) (estermannRayDisplacement a τ θ) p x‖) := by
  apply summable_integral_norm_gaussianEstermannLogTerm h α β l u (τ * θ) hΔ
    (mul_pos ha (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2))
  · unfold estermannRayDisplacement
    fun_prop
  · exact fun x => estermannRayDisplacement_im a θ x hτ


/-- The same displacement in the original positive radial coordinate. -/
def estermannRayArgument (a τ θ r : ℝ) : ℂ :=
  ((τ*a : ℝ) : ℂ)*((r:ℂ)*Complex.exp ((τ * θ : ℝ)*I)-1)

theorem estermannRayArgument_exp (a τ θ x : ℝ) :
    estermannRayArgument a τ θ (Real.exp x) = estermannRayDisplacement a τ θ x := by
  simp only [estermannRayArgument, estermannRayDisplacement, Complex.ofReal_exp,
    Complex.exp_add]

/-- The actual outward-ray term, including the Jacobian in its Gaussian factor. -/
def gaussianEstermannRayTerm {K : ℕ} [NeZero K] (h : ZMod K)
    (α β : ℂ) (l Δ u a τ θ : ℝ) (p : ℕ × ℕ) (r : ℝ) : ℂ :=
  gaussianRayIntegrand l Δ u 0 (τ * θ) r *
    estermannDampedTerm h α β (estermannRayArgument a τ θ r) p

theorem gaussianEstermannRayTerm_exp {K : ℕ} [NeZero K] (h : ZMod K)
    (α β : ℂ) (l Δ u a τ θ x : ℝ)
    (hlo : -Real.pi < τ * θ) (hhi : τ * θ ≤ Real.pi) (p : ℕ × ℕ) :
    (Real.exp x : ℂ)*gaussianEstermannRayTerm h α β l Δ u a τ θ p (Real.exp x) =
      gaussianEstermannLogTerm h α β l Δ u (τ * θ) (estermannRayDisplacement a τ θ) p x := by
  unfold gaussianEstermannRayTerm gaussianEstermannLogTerm
  rw [← mul_assoc, gaussianRayIntegrand_exp l Δ u 0 x (τ * θ) hlo hhi,
    estermannRayArgument_exp]

private theorem signed_angle_bounds {τ θ : ℝ} (hθ : θ ∈ Ioo 0 Real.pi)
    (hτ : τ = 1 ∨ τ = -1) : -Real.pi < τ * θ ∧ τ * θ ≤ Real.pi := by
  rcases hτ with rfl | rfl <;> simp only [one_mul, neg_one_mul] <;>
    constructor <;> linarith [Real.pi_pos, hθ.1, hθ.2]

theorem gaussianEstermannRayTerm_integrable {K : ℕ} [NeZero K] (h : ZMod K)
    (α β : ℂ) (l u : ℝ) {Δ a τ θ : ℝ} (hΔ : 0 < Δ) (ha : 0 < a)
    (hθ : θ ∈ Ioo 0 Real.pi) (hτ : τ = 1 ∨ τ = -1) (p : ℕ × ℕ) :
    IntegrableOn (gaussianEstermannRayTerm h α β l Δ u a τ θ p) (Ioi 0) := by
  rw [← RiemannResearch.Analysis.integrable_comp_exp_full]
  have hb := signed_angle_bounds hθ hτ
  have he : (fun x : ℝ => Real.exp x •
      gaussianEstermannRayTerm h α β l Δ u a τ θ p (Real.exp x)) =
      gaussianEstermannLogTerm h α β l Δ u (τ * θ) (estermannRayDisplacement a τ θ) p := by
    funext x
    simpa only [Complex.real_smul] using
      gaussianEstermannRayTerm_exp h α β l Δ u a τ θ x hb.1 hb.2 p
  rw [he]
  apply gaussianEstermannLogTerm_integrable h α β l u (τ * θ) hΔ
    (mul_pos ha (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2))
  · unfold estermannRayDisplacement
    fun_prop
  · exact fun x => estermannRayDisplacement_im a θ x hτ

/-- Joint absolute convergence in the original radial variable. The damping
degenerates at zero, and the logarithmic Gaussian supplies the needed control. -/
theorem summable_integral_norm_gaussianEstermannRayTerm {K : ℕ} [NeZero K] (h : ZMod K)
    (α β : ℂ) (l u : ℝ) {Δ a τ θ : ℝ} (hΔ : 0 < Δ) (ha : 0 < a)
    (hθ : θ ∈ Ioo 0 Real.pi) (hτ : τ = 1 ∨ τ = -1) :
    Summable (fun p : ℕ × ℕ => ∫ r : ℝ in Ioi 0,
      ‖gaussianEstermannRayTerm h α β l Δ u a τ θ p r‖) := by
  have hb := signed_angle_bounds hθ hτ
  have he (p : ℕ × ℕ) :
      (∫ r : ℝ in Ioi 0, ‖gaussianEstermannRayTerm h α β l Δ u a τ θ p r‖) =
        ∫ x : ℝ, ‖gaussianEstermannLogTerm h α β l Δ u (τ * θ)
          (estermannRayDisplacement a τ θ) p x‖ := by
    rw [← RiemannResearch.Analysis.integral_comp_exp_full]
    apply integral_congr_ae
    refine Eventually.of_forall fun x => ?_
    have hn := congrArg norm (gaussianEstermannRayTerm_exp h α β l Δ u a τ θ x hb.1 hb.2 p)
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos x), smul_eq_mul] using hn
  simp_rw [he]
  exact summable_integral_norm_estermannRay h α β l u hΔ ha hθ hτ

/-- Exact sum/integral exchange for the outward Gaussian Estermann ray.
No convergence or tail provider occurs among the hypotheses. -/
theorem integral_gaussianRay_mul_estermannDampedSeries {K : ℕ} [NeZero K] (h : ZMod K)
    (α β : ℂ) (l u : ℝ) {Δ a τ θ : ℝ} (hΔ : 0 < Δ) (ha : 0 < a)
    (hθ : θ ∈ Ioo 0 Real.pi) (hτ : τ = 1 ∨ τ = -1) :
    (∫ r : ℝ in Ioi 0, gaussianRayIntegrand l Δ u 0 (τ * θ) r *
      estermannDampedSeries h α β (estermannRayArgument a τ θ r)) =
        ∑' p : ℕ × ℕ, ∫ r : ℝ in Ioi 0, gaussianEstermannRayTerm h α β l Δ u a τ θ p r := by
  simp_rw [estermannDampedSeries, ← tsum_mul_left]
  exact (integral_tsum_of_summable_integral_norm
    (gaussianEstermannRayTerm_integrable h α β l u hΔ ha hθ hτ)
    (summable_integral_norm_gaussianEstermannRayTerm h α β l u hΔ ha hθ hτ)).symm

end RiemannResearch.Analysis.ConreyBaluyot
