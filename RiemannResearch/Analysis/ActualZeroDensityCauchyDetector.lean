import RiemannResearch.Analysis.RectanglePoleSubtraction
import RiemannResearch.Analysis.ActualMollifierRightBoundary
import RiemannResearch.Analysis.MontgomeryCauchyGram
import RiemannResearch.RH.WeilExplicitFormula.RvM.ZetaGrowth
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# A Gaussian Cauchy kernel for detecting actual zeta zeros

At a zero the finite Möbius mollifier error is exactly minus one. Cauchy's formula
recovers this value from four sides, with a Gaussian translated to the ordinate
and an exponential tilt towards the right boundary. The critical-line input used
in the density argument is the mixed moment of Chourasiya and Simonič,
https://arxiv.org/abs/2507.15184, equation (41).
-/

noncomputable section
open Complex Filter Set MeasureTheory
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.InghamMollifier
open MontgomeryPoisson

def mollifiedError (X : ℕ) (s : ℂ) : ℂ := riemannZeta s * mollifier X s - 1

def cauchyDetector (X : ℕ) (L : ℝ) (ρ s : ℂ) : ℂ :=
  mollifiedError X s * exp ((L : ℂ) * (s - 1 / 2) + (s - ρ) ^ 2) / (s - ρ)

/-- The signed boundary integral of the mollified error at any enclosed zero. -/
theorem cauchyDetector_rectangle {z w ρ : ℂ} (X : ℕ) (L : ℝ)
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im) (hlo : 0 < z.im)
    (hρ : Rectangle z w ∈ 𝓝 ρ) (hz : riemannZeta ρ = 0) :
    RectangleIntegral' (cauchyDetector X L ρ) z w = -exp ((L : ℂ) * (ρ - 1 / 2)) := by
  classical
  let F : ℂ → ℂ := fun s => mollifiedError X s * exp ((L : ℂ) * (s - 1 / 2) + (s - ρ) ^ 2)
  have hF {s : ℂ} (hs : s ∈ Rectangle z w) : AnalyticAt ℂ F s := by
    have hpos := hlo.trans_le ((mem_Rect hre him s).mp hs).2.2.1
    have hs1 : s ≠ 1 := by rintro rfl; simp at hpos
    exact ((analyticAt_riemannZeta hs1).mul (mollifier_analyticAt X s) |>.sub
      analyticAt_const).mul (by fun_prop)
  have hlim : Tendsto (fun s : ℂ => (s - ρ) * cauchyDetector X L ρ s)
      (𝓝[≠] ρ) (𝓝 (F ρ)) := by
    refine ((hF (mem_of_mem_nhds hρ)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hne : s - ρ ≠ 0 := sub_ne_zero.mpr (by simpa using hs)
    change F s = (s - ρ) * (F s / (s - ρ))
    field_simp
  have eqn := Complex.rectangleIntegral'_eq_sum_of_residue_limits (cauchyDetector X L ρ)
    hre him {ρ} F
    (fun s hs => (hF hs).meromorphicAt.div (analyticAt_id.sub analyticAt_const).meromorphicAt)
    (by simpa using hρ)
    (fun s hs hn => (hF hs).div (analyticAt_id.sub analyticAt_const)
      (sub_ne_zero.mpr (by simpa using hn)))
    (by simpa using hlim)
  simpa [F, mollifiedError, hz] using eqn

theorem norm_cauchyDetector (X : ℕ) (L : ℝ) (ρ s : ℂ) :
    ‖cauchyDetector X L ρ s‖ =
      ‖mollifiedError X s‖ *
        Real.exp (L * (s.re - 1 / 2) + (s.re - ρ.re) ^ 2 - (s.im - ρ.im) ^ 2) /
          ‖s - ρ‖ := by
  rw [cauchyDetector, norm_div, norm_mul, Complex.norm_exp]
  congr 3
  simp [pow_two, Complex.mul_re] <;> ring

theorem gaussian_le_cauchyWeight (v : ℝ) : Real.exp (-v^2) ≤ cauchyWeight v := by
  rw [Real.exp_neg, cauchyWeight, inv_eq_one_div]
  apply (div_le_div_iff₀ (Real.exp_pos _) (by positivity)).mpr
  nlinarith [Real.add_one_le_exp (v^2), sq_nonneg v]

theorem mollifier_norm_le_cutoff (X : ℕ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖mollifier X s‖ ≤ (X : ℝ) := by
  classical
  unfold mollifier
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _n ∈ Finset.Icc 1 X, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hm : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
      rw [norm_mul, Complex.norm_exp]
      apply mul_le_one₀ hm (Real.exp_nonneg _)
      apply Real.exp_le_one_iff.mpr
      simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (Real.log_nonneg hn1)
    _ = (X : ℝ) := by simp [Nat.card_Icc]

/-- A coarse bound used only on the Gaussian-damped horizontal edges. -/
theorem mollifiedError_norm_le_on_horizontal {X : ℕ} {s : ℂ} {T : ℝ}
    (hT : 1 ≤ T) (hX : (X : ℝ) ≤ 2 * T) (hre : 1 / 2 ≤ s.re)
    (hlo : 1 ≤ |s.im|) (hhi : |s.im| ≤ 2 * T) :
    ‖mollifiedError X s‖ ≤ 20 * T ^ 2 := by
  have hz := Zeta23.RvM.riemannZeta_linear_growth (δ := 1 / 2) (by norm_num) hre hlo
  have hm := (mollifier_norm_le_cutoff X (by linarith : 0 ≤ s.re)).trans hX
  have hz' : ‖riemannZeta s‖ ≤ 9 * T := by norm_num at hz; linarith
  have hp := mul_le_mul hz' hm (norm_nonneg _) (by positivity : 0 ≤ 9 * T)
  have h := norm_sub_le (riemannZeta s * mollifier X s) 1
  rw [norm_one, norm_mul] at h
  unfold mollifiedError
  nlinarith [sq_nonneg (T - 1)]

end RiemannResearch.Analysis.InghamMollifier
