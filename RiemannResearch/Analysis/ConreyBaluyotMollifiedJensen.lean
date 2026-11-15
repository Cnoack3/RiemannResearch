/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyBaluyotMollifierLinearGrowth
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Tactic.FunProp

/-!
# Jensen bounds for the actual mollified zeta

The analytic symmetrization has the real part of the mollified zeta on its
real axis. Jensen's inequality, the proved linear growth, and the right-line
anchor give an unconditional uniform logarithmic bound on the divisor sum.
Identifying that sum with the horizontal real-part zero count and converting
it into an argument-variation bound are separate remaining steps.
-/

noncomputable section
open Complex Set
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- The analytic symmetrization whose values on the real axis are the real
parts of the original function at height T. -/
def heightSymmetrization (f : ℂ → ℂ) (T : ℝ) (z : ℂ) : ℂ :=
  (f (z + (T : ℂ) * I) + star (f (star z + (T : ℂ) * I))) / 2

theorem differentiableAt_heightSymmetrization
    (f : ℂ → ℂ) (T : ℝ) {z : ℂ} (hz : |z.im| < T)
    (hf : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℂ f w) :
    DifferentiableAt ℂ (heightSymmetrization f T) z := by
  have hp : 0 < (z + (T : ℂ) * I).im := by
    have h := (abs_lt.mp hz).1
    simp
    linarith
  have hm : 0 < ((star z : ℂ) + (T : ℂ) * I).im := by
    have h := (abs_lt.mp hz).2
    simp
    linarith
  let g : ℂ → ℂ := fun w => f (w + (T : ℂ) * I)
  have h1 : DifferentiableAt ℂ g z := by
    apply (hf _ hp).comp z
    fun_prop
  have h2 : DifferentiableAt ℂ g (star z) := by
    apply (hf _ hm).comp (star z)
    fun_prop
  have h3 : DifferentiableAt ℂ (fun w : ℂ => star (g (star w))) z := by
    simpa [Function.comp_def] using h2.star_conj
  change DifferentiableAt ℂ (fun w => (g w + star (g (star w))) / 2) z
  exact (h1.add h3).div_const 2

theorem analyticOnNhd_heightSymmetrization
    (f : ℂ → ℂ) (T : ℝ)
    (hf : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℂ f w) :
    AnalyticOnNhd ℂ (heightSymmetrization f T) {z : ℂ | |z.im| < T} := by
  have hopen : IsOpen {z : ℂ | |z.im| < T} :=
    isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  apply (Complex.analyticOnNhd_iff_differentiableOn hopen).mpr
  intro z hz
  exact (differentiableAt_heightSymmetrization f T hz hf).differentiableWithinAt

theorem analyticOnNhd_heightSymmetrization_closedBall
    (f : ℂ → ℂ) (T b R : ℝ) (hR : R < T)
    (hf : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℂ f w) :
    AnalyticOnNhd ℂ (heightSymmetrization f T) (Metric.closedBall (b : ℂ) R) := by
  apply (analyticOnNhd_heightSymmetrization f T hf).mono
  intro z hz
  have hd : ‖z - (b : ℂ)‖ ≤ R := by
    simpa only [dist_eq_norm] using (Metric.mem_closedBall.mp hz)
  have hi := (Complex.abs_im_le_norm (z - (b : ℂ))).trans hd
  simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at hi
  exact hi.trans_lt hR

theorem heightSymmetrization_realAxis (f : ℂ → ℂ) (T x : ℝ) :
    (heightSymmetrization f T (x : ℂ)).re =
      (f ((x : ℂ) + (T : ℂ) * I)).re := by
  simp [heightSymmetrization, Complex.div_ofNat_re]

theorem norm_heightSymmetrization_le (f : ℂ → ℂ) (T M : ℝ) (z : ℂ)
    (h1 : ‖f (z + (T : ℂ) * I)‖ ≤ M)
    (h2 : ‖f ((star z : ℂ) + (T : ℂ) * I)‖ ≤ M) :
    ‖heightSymmetrization f T z‖ ≤ M := by
  unfold heightSymmetrization
  calc
    _ = ‖f (z + (T : ℂ) * I) + star (f (star z + (T : ℂ) * I))‖ / 2 := by
      rw [norm_div]
      norm_num
    _ ≤ (‖f (z + (T : ℂ) * I)‖ + ‖star (f (star z + (T : ℂ) * I))‖) / 2 :=
      div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)
    _ ≤ (M + M) / 2 := by simpa only [norm_star] using
      div_le_div_of_nonneg_right (add_le_add h1 h2) (by norm_num : (0 : ℝ) ≤ 2)
    _ = M := by ring

/-- The actual mollified zeta is holomorphic at every positive ordinate. -/
theorem differentiableAt_mollifiedZeta_of_im_pos (σ y ε : ℝ) {w : ℂ}
    (hw : 0 < w.im) : DifferentiableAt ℂ (mollifiedZeta σ y ε) w := by
  apply (analyticAt_mollifiedZeta σ y ε ?_).differentiableAt
  intro he
  have hi := congrArg Complex.im he
  simp at hi
  linarith

/-- Jensen controls the zero multiplicity of the real-part symmetrization on
a fixed inner disk. The bound uses only explicit strip, growth and anchor
assumptions and applies before any choice of a logarithm branch. -/
theorem heightSymmetrization_jensen_bound
    (f : ℂ → ℂ) (T b a r R M : ℝ)
    (hr : 0 < r) (hrR : r < R) (hT : R + 1 ≤ T)
    (ha : a ≤ b - R) (hM : 1 ≤ M)
    (hf : ∀ w : ℂ, 0 < w.im → DifferentiableAt ℂ f w)
    (hbound : ∀ w : ℂ, a ≤ w.re → 1 ≤ w.im → |w.im - T| ≤ R → ‖f w‖ ≤ M)
    (hcenter : (1 / 2 : ℝ) ≤ (f ((b : ℂ) + (T : ℂ) * I)).re) :
    ((∑ᶠ u : ℂ,
      MeromorphicOn.divisor (heightSymmetrization f T) (Metric.closedBall (b : ℂ) |r|) u : ℤ) : ℝ)
        ≤ Real.log (2 * M) / Real.log (R / r) := by
  have hR : 0 < R := by linarith
  have hRT : R < T := by linarith
  have han : AnalyticOnNhd ℂ (heightSymmetrization f T)
      (Metric.closedBall (b : ℂ) |R|) := by
    simpa only [abs_of_pos hR] using
      analyticOnNhd_heightSymmetrization_closedBall f T b R hRT hf
  have hcenter' : (1 / 2 : ℝ) ≤ (heightSymmetrization f T (b : ℂ)).re := by
    rw [heightSymmetrization_realAxis]
    exact hcenter
  have hn : (1 / 2 : ℝ) ≤ ‖heightSymmetrization f T (b : ℂ)‖ :=
    hcenter'.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  have hnpos : 0 < ‖heightSymmetrization f T (b : ℂ)‖ := by linarith
  have hne : heightSymmetrization f T (b : ℂ) ≠ 0 := norm_pos_iff.mp hnpos
  have hSphere : ∀ z ∈ Metric.sphere (b : ℂ) |R|,
      ‖heightSymmetrization f T z‖ ≤ M := by
    intro z hz
    have hd : ‖z - (b : ℂ)‖ = R := by
      simpa only [dist_eq_norm, abs_of_pos hR] using (Metric.mem_sphere.mp hz)
    have hre : |z.re - b| ≤ R := by
      simpa only [Complex.sub_re, Complex.ofReal_re, hd] using
        Complex.abs_re_le_norm (z - (b : ℂ))
    have him : |z.im| ≤ R := by
      simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero, hd] using
        Complex.abs_im_le_norm (z - (b : ℂ))
    have hre' := abs_le.mp hre
    have him' := abs_le.mp him
    apply norm_heightSymmetrization_le f T M z
    · apply hbound
      · simp
        linarith
      · simp
        linarith
      · simpa using him
    · apply hbound
      · simp
        linarith
      · simp
        linarith
      · simpa using him
  have hJ :
      ((∑ᶠ u : ℂ,
        MeromorphicOn.divisor (heightSymmetrization f T)
          (Metric.closedBall (b : ℂ) |r|) u : ℤ) : ℝ) ≤
          Real.log (M / ‖heightSymmetrization f T (b : ℂ)‖) / Real.log (R / r) :=
    AnalyticOnNhd.sum_divisor_le
      (by simpa only [abs_of_pos hr] using hr)
      (by simpa only [abs_of_pos hr, abs_of_pos hR] using hrR)
      hM han hne hSphere
  have hq : M / ‖heightSymmetrization f T (b : ℂ)‖ ≤ 2 * M := by
    apply (div_le_iff₀ hnpos).mpr
    have hp := mul_nonneg (show 0 ≤ M by linarith)
      (show 0 ≤ 2 * ‖heightSymmetrization f T (b : ℂ)‖ - 1 by linarith)
    nlinarith
  have hl : Real.log (M / ‖heightSymmetrization f T (b : ℂ)‖) ≤
      Real.log (2 * M) :=
    Real.log_le_log (div_pos (by linarith) hnpos) hq
  have hden : 0 ≤ Real.log (R / r) :=
    Real.log_nonneg ((one_le_div hr).2 hrR.le)
  exact hJ.trans (div_le_div_of_nonneg_right hl hden)

/-- The actual symmetrized mollified zeta has a uniform logarithmic bound
on its Jensen divisor sum. The horizontal real-zero and argument-variation
interpretations are not included in this statement. -/
theorem exists_uniform_mollifiedZeta_jensen_bound {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ η Y b C : ℝ, 0 < η ∧ η < 1 / 4 ∧ 1 < Y ∧ 2 ≤ b ∧ 0 < C ∧
      ∀ y : ℝ, Y ≤ y → ∀ σ : ℝ, 1 / 2 + 1 / Real.log y ≤ σ →
        σ ≤ 1 / 2 + η → ∀ T : ℝ, b + 1 ≤ T →
          ((∑ᶠ u : ℂ, MeromorphicOn.divisor
            (heightSymmetrization (mollifiedZeta σ y ε) T)
            (Metric.closedBall (b : ℂ) |b - 1 / 2|) u : ℤ) : ℝ) ≤
            Real.log (2 * (1 + C * (T + (b - 1 / 4)) * y)) /
              Real.log ((b - 1 / 4) / (b - 1 / 2)) := by
  obtain ⟨η1, Y1, C, hη1, hη1', hY1, hC, hg⟩ :=
    exists_uniform_mollifiedZeta_linear_growth
  obtain ⟨η2, Y2, b, hη2, hη2', hY2, hb, hanchor⟩ :=
    exists_uniform_mollifiedZeta_right_real_lower hε
  let η := min η1 η2
  let Y := max Y1 Y2
  refine ⟨η, Y, b, C, by dsimp [η]; exact lt_min hη1 hη2,
    by dsimp [η]; exact (min_le_left _ _).trans_lt hη1',
    by dsimp [Y]; exact hY1.trans_le (le_max_left _ _),
    hb, hC, ?_⟩
  intro y hy σ hσ hση T hT
  have hy1 : Y1 ≤ y := (le_max_left _ _).trans hy
  have hy2 : Y2 ≤ y := (le_max_right _ _).trans hy
  have hy0 : 0 ≤ y := by dsimp [Y] at hy; linarith [le_max_left Y1 Y2]
  have hs1 : σ ≤ 1 / 2 + η1 := by
    dsimp [η] at hση
    linarith [min_le_left η1 η2]
  have hs2 : σ ≤ 1 / 2 + η2 := by
    dsimp [η] at hση
    linarith [min_le_right η1 η2]
  let r := b - 1 / 2
  let R := b - 1 / 4
  let M := 1 + C * (T + R) * y
  have hr : 0 < r := by dsimp [r]; linarith
  have hrR : r < R := by dsimp [r, R]; linarith
  have hTR : R + 1 ≤ T := by dsimp [R]; linarith
  have ha : (1 / 4 : ℝ) ≤ b - R := by dsimp [R]; linarith
  have hTR0 : 0 ≤ T + R := by dsimp [R]; linarith
  have hM : 1 ≤ M := by
    dsimp [M]
    have hp : 0 ≤ C * (T + R) * y :=
      mul_nonneg (mul_nonneg hC.le hTR0) hy0
    linarith
  have hbound : ∀ w : ℂ, (1 / 4 : ℝ) ≤ w.re → 1 ≤ w.im →
      |w.im - T| ≤ R → ‖mollifiedZeta σ y ε w‖ ≤ M := by
    intro w hw hwi hnear
    have habs : |w.im| ≤ T + R := by
      rw [abs_of_nonneg (by linarith : 0 ≤ w.im)]
      have hn := (abs_le.mp hnear).2
      linarith
    have hgrowth := hg y hy1 σ hσ hs1 ε w hw
      (by rw [abs_of_nonneg (by linarith : 0 ≤ w.im)]; exact hwi)
    calc
      _ ≤ C * |w.im| * y := hgrowth
      _ ≤ C * (T + R) * y :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left habs hC.le) hy0
      _ ≤ M := by dsimp [M]; linarith
  have hc : (1 / 2 : ℝ) ≤ (mollifiedZeta σ y ε ((b : ℂ) + (T : ℂ) * I)).re :=
    hanchor y hy2 σ hσ hs2 _ (by simp)
  simpa only [r, R, M] using
    heightSymmetrization_jensen_bound (mollifiedZeta σ y ε) T b (1 / 4) r R M
      hr hrR hTR ha hM
      (fun w hw => differentiableAt_mollifiedZeta_of_im_pos σ y ε hw) hbound hc

end RiemannResearch.Analysis.ConreyBaluyot
