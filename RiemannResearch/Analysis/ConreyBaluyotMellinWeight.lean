/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.GammaMellinBounds
import RiemannResearch.Analysis.ZetaAbsoluteConvergenceBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Conrey--Baluyot nonstandard mollifier and its Mellin weight

Source for the definitions and Gamma-recurrence strategy:
S. A. C. Baluyot, *On the Zeros of Riemann's Zeta-function* (2017),
(1.2.6)--(1.2.7), Lemma 3.1.1, especially (3.1.4):
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320 .

The actual normalized Gamma/zeta Mellin integrand is absolutely integrable
for sigma>1/2, xi>0 and r>0. The explicit majorant and integral bound are
uniform in sigma. The constant depends on r and is not bounded as r tends
to zero.

Positive-contour independence and reality are proved in the sibling module
ConreyBaluyotMellinContour; exponential small-xi decay is proved in
ConreyBaluyotMellinDecay, and the actual local residues are computed in
ConreyBaluyotMellinResidues. The signed contour expansion (3.1.3) is proved in
ConreyBaluyotMellinShift; uniform positive normalization and global bounds are
proved in ConreyBaluyotMellinNormalization, with exact-floor tails in
ConreyBaluyotMollifierTruncation. Estermann/Kloosterman input and the actual
uniform mollified second moment remain open.
In particular this module supplies no ConreyBaluyotDensityHypothesis.
The finite coefficient normalization theorem keeps W(y) nonzero explicit.
-/

open Complex MeasureTheory Set
open scoped BigOperators


noncomputable section
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- The integrand in (1.2.7), with the positive vertical line parametrized by t. -/
def mellinIntegrand (σ ξ r t : ℝ) : ℂ :=
  let z : ℂ := (r : ℂ) + I * t
  Gamma (z + 1) * (riemannZeta ((2 * σ : ℝ) + z) / riemannZeta (2 * σ : ℝ)) *
    riemannZeta (1 + z) * (ξ : ℂ) ^ z

/-- Baluyot's actual Mellin weight on Re z = r. The factor i from dz cancels. -/
def weightOnLine (σ ξ r : ℝ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ * ∫ t : ℝ, mellinIntegrand σ ξ r t

/-- Fixing the admissible defining line r=1. Positive-line independence is in MellinContour. -/
def weight (σ ξ : ℝ) : ℂ := weightOnLine σ ξ 1

/-- A pointwise majorant uniform in sigma>1/2. The dependence on r is explicit. -/
theorem norm_mellinIntegrand_le {σ ξ r : ℝ}
    (hσ : 1 / 2 < σ) (hξ : 0 < ξ) (hr : 0 < r) (t : ℝ) :
    ‖mellinIntegrand σ ξ r t‖ ≤
      (Real.Gamma (r + 3) * (1 + 1 / r) * ξ ^ r) * (1 + t ^ 2)⁻¹ := by
  let z : ℂ := (r : ℂ) + I * t
  have hz : z.re = r := by simp [z]
  have hgam := Complex.gamma_vertical_cauchy_bound hr.le t
  have hzeta : ‖riemannZeta ((2 * σ : ℝ) + z) /
      riemannZeta (2 * σ : ℝ)‖ ≤ 1 := by
    apply norm_riemannZeta_div_real_le_one (by linarith)
    simp [hz]; linarith
  have hother : ‖riemannZeta (1 + z)‖ ≤ 1 + 1 / r := by
    have hh := norm_riemannZeta_le_integral_test (s := 1 + z) (by simp [hz]; linarith)
    simpa [hz] using hh
  have hpower : ‖(ξ : ℂ) ^ z‖ = ξ ^ r := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hξ, hz]
  unfold mellinIntegrand
  change ‖Gamma (z + 1) * _ * _ * _‖ ≤ _
  simp only [norm_mul]
  rw [hpower]
  calc
    _ ≤ (Real.Gamma (r + 3) / (1 + t ^ 2) * 1) *
        (1 + 1 / r) * ξ ^ r := by
      gcongr
    _ = _ := by ring

/-- There are no Gamma or zeta poles on this positive vertical line. -/
theorem continuous_mellinIntegrand {σ ξ r : ℝ}
    (hσ : 1 / 2 < σ) (hξ : 0 < ξ) (hr : 0 < r) :
    Continuous (mellinIntegrand σ ξ r) := by
  let z : ℝ → ℂ := fun t => (r : ℂ) + I * t
  have hz : Continuous z := by fun_prop
  have hgam : Continuous (fun t => Gamma (z t + 1)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (Complex.continuousAt_Gamma _ ?_).comp (hz.continuousAt.add continuousAt_const)
    intro n hn
    have he := congrArg Complex.re hn
    simp [z] at he
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hleft : Continuous (fun t => riemannZeta ((2 * σ : ℝ) + z t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (differentiableAt_riemannZeta ?_).continuousAt.comp
      (continuousAt_const.add hz.continuousAt)
    intro he
    have hh := congrArg Complex.re he
    simp [z] at hh
    linarith
  have hright : Continuous (fun t => riemannZeta (1 + z t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (differentiableAt_riemannZeta ?_).continuousAt.comp
      (continuousAt_const.add hz.continuousAt)
    intro he
    have hh := congrArg Complex.re he
    simp [z] at hh
    linarith
  have : NeZero (ξ : ℂ) := ⟨by exact_mod_cast hξ.ne'⟩
  have hpow : Continuous (fun t => (ξ : ℂ) ^ z t) :=
    (continuous_const_cpow (ξ : ℂ)).comp hz
  exact ((hgam.mul (hleft.div_const _)).mul hright).mul hpow

/-- Absolute convergence of the actual Mellin integral; no analytic provider hypothesis. -/
theorem integrable_mellinIntegrand {σ ξ r : ℝ}
    (hσ : 1 / 2 < σ) (hξ : 0 < ξ) (hr : 0 < r) :
    Integrable (mellinIntegrand σ ξ r) := by
  apply (integrable_inv_one_add_sq.const_mul
    (Real.Gamma (r + 3) * (1 + 1 / r) * ξ ^ r)).mono'
    (continuous_mellinIntegrand hσ hξ hr).aestronglyMeasurable
  exact Filter.Eventually.of_forall (norm_mellinIntegrand_le hσ hξ hr)

/-- Explicit Mellin weight bound, uniform in sigma>1/2, for each r>0. -/
theorem norm_weightOnLine_le {σ ξ r : ℝ}
    (hσ : 1 / 2 < σ) (hξ : 0 < ξ) (hr : 0 < r) :
    ‖weightOnLine σ ξ r‖ ≤ Real.Gamma (r + 3) * (1 + 1 / r) * ξ ^ r / 2 := by
  have hI := integrable_mellinIntegrand hσ hξ hr
  have hbound : ‖∫ t : ℝ, mellinIntegrand σ ξ r t‖ ≤
      (Real.Gamma (r + 3) * (1 + 1 / r) * ξ ^ r) * Real.pi := by
    calc
      _ ≤ ∫ t : ℝ, ‖mellinIntegrand σ ξ r t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, (Real.Gamma (r + 3) * (1 + 1 / r) * ξ ^ r) *
          (1 + t ^ 2)⁻¹ :=
        integral_mono hI.norm (integrable_inv_one_add_sq.const_mul _)
          (norm_mellinIntegrand_le hσ hξ hr)
      _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]
  unfold weightOnLine
  rw [norm_mul, norm_inv]
  have hnorm : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
    rw [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.norm_of_nonneg (by positivity)]
  rw [hnorm]
  calc
    _ ≤ (2 * Real.pi)⁻¹ * ((Real.Gamma (r + 3) * (1 + 1 / r) * ξ ^ r) * Real.pi) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = _ := by field_simp [Real.pi_ne_zero]


/-- The coefficient in Baluyot (2017), (1.2.6), before the cutoff.
A nonzero normalizing weight is a separate analytic obligation. -/
def mollifierCoefficient (σ y : ℝ) (n : ℕ) : ℂ :=
  (ArithmeticFunction.moebius n : ℂ) * (weight σ (y / n) / weight σ y)

/-- The actual finite, nonstandard mollifier. Here the cutoff follows the thesis
convention y^(1+ε), with y=T^θ. -/
def nonstandardMollifier (σ y ε : ℝ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊y ^ (1 + ε)⌋₊, mollifierCoefficient σ y n / (n : ℂ) ^ s

theorem mollifierCoefficient_one {σ y : ℝ} (hy : weight σ y ≠ 0) :
    mollifierCoefficient σ y 1 = 1 := by
  simp [mollifierCoefficient, hy]

/-- A concrete bound for the fixed defining line. This is not the exponential-tail estimate. -/
theorem norm_weight_le {σ ξ : ℝ} (hσ : 1 / 2 < σ) (hξ : 0 < ξ) :
    ‖weight σ ξ‖ ≤ 6 * ξ := by
  have h := norm_weightOnLine_le hσ hξ (show (0 : ℝ) < 1 by norm_num)
  have hg : Real.Gamma 4 = 6 := by
    convert Real.Gamma_nat_eq_factorial 3 using 1 <;> norm_num
  norm_num [weight, hg] at h ⊢
  linarith

end RiemannResearch.Analysis.ConreyBaluyot
