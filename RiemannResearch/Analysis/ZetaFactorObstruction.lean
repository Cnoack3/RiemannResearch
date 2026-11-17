import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Convex.Topology
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Push
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# A zeta-factor obstruction to exact finite spectral cancellation

Source: user-selected highest viability RH.pdf, sections 7.3--7.5 and agenda G2:
https://drive.google.com/file/d/1smLPEbJDfOV2Z5mMSMMQvFEd3_qRYopL/view
The source supplies the numerator H + zeta(1-z) Gamma(z) and finite projected
columns zeta(1-z) G_q(z). The identity-theorem obstruction is derived here.
The result concerns exact finite-cutoff interpolation, not the approximate
uniform G1 estimate or the Riemann hypothesis.
-/

noncomputable section
open Filter Set
open scoped Topology
namespace RiemannResearch.Analysis.ZetaFactorObstruction

def numerator (H : ℂ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  H + riemannZeta (1-z) * F z

theorem numerator_three (H : ℂ) (F : ℂ → ℂ) :
    numerator H F 3 = H := by
  have hz : riemannZeta (-2) = 0 := by
    simpa using riemannZeta_neg_two_mul_nat_add_one 0
  norm_num [numerator, hz]

theorem numerator_analytic (H : ℂ) (F : ℂ → ℂ)
    (hF : Differentiable ℂ F) :
    AnalyticOnNhd ℂ (numerator H F) {z : ℂ | 0 < z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro z hz
  have hne : (1-z : ℂ) ≠ 1 := by
    intro he
    have he' : z = 0 := by linear_combination -he
    simp [he'] at hz
  exact ((differentiableAt_const H).add
    (((differentiableAt_riemannZeta hne).comp z
      ((differentiableAt_const 1).sub differentiableAt_id)).mul
      (hF z))).differentiableWithinAt

theorem no_accumulating_zeros (H : ℂ) (hH : H ≠ 0)
    (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (z : ℂ) (hz : 0 < z.re) :
    ¬ ∃ᶠ w in 𝓝[≠] z, numerator H F w = 0 := by
  intro hf
  have hc : IsPreconnected {w : ℂ | 0 < w.re} :=
    ((convex_Ioi (0 : ℝ)).linear_preimage Complex.reLm).isPreconnected
  have he := (numerator_analytic H F hF).eqOn_of_preconnected_of_frequently_eq
    (analyticOnNhd_const : AnalyticOnNhd ℂ (fun _ : ℂ => (0 : ℂ))
      {w : ℂ | 0 < w.re}) hc hz hf
  have h3 := he (show (3 : ℂ) ∈ {w : ℂ | 0 < w.re} by norm_num)
  rw [numerator_three] at h3
  exact hH h3


def line (σ t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I

@[simp] theorem line_re (σ t : ℝ) : (line σ t).re = σ := by
  simp [line, Complex.mul_re]
@[simp] theorem line_im (σ t : ℝ) : (line σ t).im = t := by
  simp [line, Complex.mul_im]

theorem exists_nonzero_on_interval (H : ℂ) (hH : H ≠ 0)
    (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (σ a b : ℝ) (hσ : 0 < σ) (hab : a < b) :
    ∃ t ∈ Ioo a b, numerator H F (line σ t) ≠ 0 := by
  by_contra hn
  push Not at hn
  let t₀ : ℝ := (a+b)/2
  have ha : a < t₀ := by dsimp [t₀]; linarith
  have hb : t₀ < b := by dsimp [t₀]; linarith
  have hfreal : ∃ᶠ t : ℝ in 𝓝[≠] t₀, numerator H F (line σ t) = 0 := by
    apply Filter.Eventually.frequently
    have hI : ∀ᶠ t : ℝ in 𝓝 t₀, t ∈ Ioo a b := Ioo_mem_nhds ha hb
    filter_upwards [hI.filter_mono nhdsWithin_le_nhds] with t ht
    exact hn t ht
  have hfreq : ∃ᶠ w : ℂ in 𝓝[≠] (line σ t₀), numerator H F w = 0 := by
    rw [frequently_iff_seq_forall] at hfreal ⊢
    obtain ⟨xs, hxs, heq⟩ := hfreal
    refine ⟨fun n => line σ (xs n), ?_, heq⟩
    rw [tendsto_nhdsWithin_iff] at hxs ⊢
    constructor
    · have hc : Continuous (line σ) := by unfold line; fun_prop
      exact hc.continuousAt.tendsto.comp hxs.1
    · filter_upwards [hxs.2] with n hn
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hn ⊢
      intro he
      exact hn (by simpa using congrArg Complex.im he)
  exact no_accumulating_zeros H hH F hF (line σ t₀) (by simpa using hσ) hfreq

theorem numerator_on_line_continuous (H : ℂ) (F : ℂ → ℂ)
    (hF : Differentiable ℂ F) (σ : ℝ) (hσ : 0 < σ) :
    Continuous (fun t : ℝ => numerator H F (line σ t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hl : Continuous (line σ) := by unfold line; fun_prop
  exact ((numerator_analytic H F hF) (line σ t) (by simpa using hσ)).continuousAt.comp
    hl.continuousAt

theorem mellin_block_pos (H : ℂ) (hH : H ≠ 0)
    (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (σ a b : ℝ) (hσ : 0 < σ) (hab : a < b) :
    0 < ∫ t in a..b, ‖numerator H F (line σ t)‖ ^ 2 /
      (Real.pi * (t ^ 2 + 1/4)) := by
  have hc := numerator_on_line_continuous H F hF σ hσ
  apply intervalIntegral.integral_pos hab
  · apply Continuous.continuousOn
    exact (hc.norm.pow 2).div
      (continuous_const.mul ((continuous_id.pow 2).add continuous_const))
      (by intro t; positivity)
  · intro t ht
    positivity
  · obtain ⟨t, ht, hn⟩ := exists_nonzero_on_interval H hH F hF σ a b hσ hab
    refine ⟨t, ⟨ht.1.le, ht.2.le⟩, ?_⟩
    exact div_pos (sq_pos_of_pos (norm_pos_iff.mpr hn)) (by positivity)

open scoped BigOperators
def expPolynomial {ι : Type*} [Fintype ι] (c frequency : ι → ℂ) (z : ℂ) : ℂ :=
  ∑ i, c i * Complex.exp (frequency i * z)

theorem expPolynomial_entire {ι : Type*} [Fintype ι] (c frequency : ι → ℂ) :
    Differentiable ℂ (expPolynomial c frequency) := by
  unfold expPolynomial
  fun_prop

theorem finite_corrected_block_pos {ι : Type*} [Fintype ι]
    (H : ℂ) (hH : H ≠ 0) (F : ℂ → ℂ) (hF : Differentiable ℂ F)
    (G : ι → ℂ → ℂ) (hG : ∀ i, Differentiable ℂ (G i))
    (c : ι → ℂ) (σ a b : ℝ) (hσ : 0 < σ) (hab : a < b) :
    0 < ∫ t in a..b,
      ‖numerator H F (line σ t) +
        ∑ i, c i * (riemannZeta (1 - line σ t) * G i (line σ t))‖ ^ 2 /
          (Real.pi * (t ^ 2 + 1/4)) := by
  have he (z : ℂ) :
      numerator H F z + ∑ i, c i * (riemannZeta (1-z) * G i z) =
        numerator H (fun z => F z + ∑ i, c i * G i z) z := by
    simp only [numerator, mul_add, Finset.mul_sum, ← add_assoc]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  simp_rw [he]
  apply mellin_block_pos H hH _ _ σ a b hσ hab
  fun_prop

end RiemannResearch.Analysis.ZetaFactorObstruction
