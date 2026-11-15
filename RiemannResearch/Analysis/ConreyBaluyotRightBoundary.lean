import RiemannResearch.Analysis.ComplexRightBoundary
import RiemannResearch.Analysis.ConreyBaluyotMollifiedBoundary
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-!
# Signed right boundary for the actual Conrey--Baluyot product

Source for the target: the user-provided normalized Littlewood continuation
(15 November 2026), section 8. The coefficient and decay providers are the
existing actual-mollifier theorems of ConreyBaluyotMollifiedBoundary.
Cauchy's rectangle identity supplies cancellation; no moment estimate,
Dirichlet-series exchange, or identification with a different mollifier is used.
-/
noncomputable section
open Complex Set MeasureTheory
namespace RiemannResearch.Analysis.ConreyBaluyot

private theorem dyadic_decay_eq_exp (x : ℝ) :
    (2 : ℝ) ^ (2 - x) = 4 * Real.exp (-(Real.log 2) * x) := by
  rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_two,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    show -(Real.log 2) * x = -(Real.log 2 * x) by ring, Real.exp_neg]
  norm_num
  ring

/-- Both complex and signed real vertical integrals, with the same parameters
and principal logarithm as the normalized Littlewood construction. -/
theorem mollifiedZeta_right_integral_bounds {σ y ε b D : ℝ}
    (hb : 2 ≤ b) (hD : 0 ≤ D)
    (hr : ∀ s : ℂ, b ≤ s.re → 1 / 2 ≤ (mollifiedZeta σ y ε s).re)
    (hdecay : ∀ s : ℂ, b ≤ s.re →
      ‖mollifiedZeta σ y ε s - 1‖ ≤ D * (2 : ℝ) ^ (2 - s.re))
    (u v : ℝ) :
    ‖∫ t in u..v, log (mollifiedZeta σ y ε ((b : ℂ) + t * I))‖ ≤
        (4 * D / Real.log 2) * (2 : ℝ) ^ (2 - b) ∧
    |∫ t in u..v, Real.log ‖mollifiedZeta σ y ε ((b : ℂ) + t * I)‖| ≤
        (4 * D / Real.log 2) * (2 : ℝ) ^ (2 - b) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd : ∀ z : ℂ, b ≤ z.re → DifferentiableAt ℂ (mollifiedZeta σ y ε) z := by
    intro z hz
    apply (analyticAt_mollifiedZeta σ y ε ?_).differentiableAt
    intro he
    have hh := congrArg Complex.re he
    simp at hh
    linarith
  have hB : ∀ z : ℂ, b ≤ z.re →
      ‖mollifiedZeta σ y ε z - 1‖ ≤ (4 * D) * Real.exp (-(Real.log 2) * z.re) := by
    intro z hz
    have hh := hdecay z hz
    rw [dyadic_decay_eq_exp] at hh
    nlinarith
  have he : 4 * ((4 * D) / Real.log 2 * Real.exp (-(Real.log 2) * b)) =
      (4 * D / Real.log 2) * (2 : ℝ) ^ (2 - b) := by
    rw [dyadic_decay_eq_exp]
    ring
  constructor
  · rw [← he]
    exact Complex.norm_integral_log_vertical_le_of_exp_decay hlog (by positivity) hd hr hB u v
  · rw [← he]
    exact Complex.abs_integral_log_norm_vertical_le_of_exp_decay hlog (by positivity) hd hr hB u v

/-- Uniform signed cancellation for the actual nonstandard mollifier.
The constants precede the length, sigma, right line and both endpoints.
The bound decays exponentially as the right line moves right. -/
theorem exists_uniform_mollifiedZeta_right_integral_bound {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ η Y b C : ℝ, 0 < η ∧ η < 1 / 4 ∧ 1 < Y ∧ 2 ≤ b ∧ 0 < C ∧
      (∀ y : ℝ, Y ≤ y → ∀ σ : ℝ, 1 / 2 + 1 / Real.log y ≤ σ →
        σ ≤ 1 / 2 + η → ∀ s : ℂ, b ≤ s.re →
          1 / 2 ≤ (mollifiedZeta σ y ε s).re) ∧
      ∀ y : ℝ, Y ≤ y → ∀ σ : ℝ, 1 / 2 + 1 / Real.log y ≤ σ →
        σ ≤ 1 / 2 + η → ∀ c : ℝ, b ≤ c → ∀ u v : ℝ,
          ‖∫ t in u..v, log (mollifiedZeta σ y ε ((c : ℂ) + t * I))‖ ≤
              C * (2 : ℝ) ^ (2 - c) ∧
          |∫ t in u..v, Real.log ‖mollifiedZeta σ y ε ((c : ℂ) + t * I)‖| ≤
              C * (2 : ℝ) ^ (2 - c) := by
  obtain ⟨η₁, Y₁, D, hη₁, hη₁', hY₁, hD, hdecay⟩ :=
    exists_uniform_mollifiedZeta_right_decay hε
  obtain ⟨η₂, Y₂, b, hη₂, hη₂', hY₂, hb, hr⟩ :=
    exists_uniform_mollifiedZeta_right_real_lower hε
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨min η₁ η₂, max Y₁ Y₂, b, 4 * D / Real.log 2,
    lt_min hη₁ hη₂, (min_le_left _ _).trans_lt hη₁',
    hY₁.trans_le (le_max_left _ _), hb, by positivity, ?_, ?_⟩
  · intro y hy σ hσ hση s hs
    exact hr y ((le_max_right _ _).trans hy) σ hσ
      (hση.trans (by linarith [min_le_right η₁ η₂])) s hs
  · intro y hy σ hσ hση c hc u v
    apply mollifiedZeta_right_integral_bounds (hb.trans hc) hD.le
    · intro s hs
      exact hr y ((le_max_right _ _).trans hy) σ hσ
        (hση.trans (by linarith [min_le_right η₁ η₂])) s (hc.trans hs)
    · intro s hs
      exact hdecay y ((le_max_left _ _).trans hy) σ hσ
        (hση.trans (by linarith [min_le_left η₁ η₂])) s ((hb.trans hc).trans hs)
end RiemannResearch.Analysis.ConreyBaluyot
