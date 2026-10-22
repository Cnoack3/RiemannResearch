import RiemannResearch.RH.BurnolZeroFactors
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The pole-removed Cayley zeta function and its finite-radius Jensen formula

The proof strategy is the disk/Jensen approach to the Balazard--Saias--Yor
identity discussed in Burnol, Theorem 1.3, https://arxiv.org/abs/math/9910055.
This module proves the actual analytic pullback and Jensen identity on every
strict subdisk. The boundary passage to the critical-line integral is not
assumed or asserted. The value at the removable point is explicitly one.
-/

noncomputable section
open scoped Topology
namespace RiemannResearch.RH.Burnol

/-- Cayley map from the unit disk to `re s > 1/2`. -/
def cayley (z : ℂ) : ℂ := (1 - z)⁻¹

@[simp] theorem cayley_zero : cayley 0 = 1 := by simp [cayley]

theorem cayley_ne_zero {z : ℂ} (hz : z ≠ 1) : cayley z ≠ 0 := by
  exact inv_ne_zero (sub_ne_zero.mpr hz.symm)

theorem ne_one_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) : z ≠ 1 := by
  intro h
  simp [h] at hz

theorem cayley_re (z : ℂ) :
    (cayley z).re = (1 - z.re) / Complex.normSq (1 - z) := by
  simp [cayley, Complex.inv_re]

theorem cayley_re_gt_half {z : ℂ} (hz : ‖z‖ < 1) : 1 / 2 < (cayley z).re := by
  have hd : 0 < Complex.normSq (1 - z) :=
    Complex.normSq_pos.mpr (sub_ne_zero.mpr (ne_one_of_norm_lt_one hz).symm)
  have hn : Complex.normSq z < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  rw [cayley_re, lt_div_iff₀ hd, normSq_one_sub]
  linarith

/-- The inverse map, whose modulus is exactly the Burnol factor. -/
def diskCoordinate (s : ℂ) : ℂ := (s - 1) / s

theorem cayley_diskCoordinate {s : ℂ} (hs : s ≠ 0) : cayley (diskCoordinate s) = s := by
  unfold cayley diskCoordinate
  field_simp
  ring

theorem diskCoordinate_cayley {z : ℂ} (hz : z ≠ 1) : diskCoordinate (cayley z) = z := by
  have hd : 1 - z ≠ 0 := sub_ne_zero.mpr hz.symm
  unfold diskCoordinate cayley
  field_simp
  ring

theorem norm_diskCoordinate (s : ℂ) : ‖diskCoordinate s‖ = factor s := by
  rw [diskCoordinate, factor, norm_div, norm_div, norm_sub_rev]

/-- Explicit analytic removal of the pole at one in `(s-1) zeta(s) / s`.
The reciprocal Gamma factor is entire; only zero is excluded analytically. -/
def regularZetaRatio (s : ℂ) : ℂ :=
  (s * (s - 1) * completedRiemannZeta₀ s + 1) * (Complex.Gammaℝ s)⁻¹ / s ^ 2

@[simp] theorem regularZetaRatio_one : regularZetaRatio 1 = 1 := by
  simp [regularZetaRatio]

theorem analyticAt_regularZetaRatio {s : ℂ} (hs : s ≠ 0) :
    AnalyticAt ℂ regularZetaRatio s := by
  have hnum : AnalyticAt ℂ
      (fun w => w * (w - 1) * completedRiemannZeta₀ w + 1) s :=
    ((analyticAt_id.mul (analyticAt_id.sub analyticAt_const)).mul
      (differentiable_completedZeta₀.analyticAt s)).add analyticAt_const
  exact (hnum.mul (Complex.differentiable_Gammaℝ_inv.analyticAt s)).div
    (analyticAt_id.pow 2) (pow_ne_zero 2 hs)

theorem regularZetaRatio_eq {s : ℂ} (hpos : 0 < s.re) (h1 : s ≠ 1) :
    regularZetaRatio s = (s - 1) / s * riemannZeta s := by
  have h0 : s ≠ 0 := by intro h; simp [h] at hpos
  have hG := Complex.Gammaℝ_ne_zero_of_re_pos hpos
  have hm : 1 - s ≠ 0 := sub_ne_zero.mpr h1.symm
  rw [regularZetaRatio, riemannZeta_def_of_ne_zero h0, completedRiemannZeta_eq]
  field_simp
  ring

/-- The holomorphic disk function `z * zeta(1/(1-z))`, repaired at zero. -/
def diskZeta (z : ℂ) : ℂ := regularZetaRatio (cayley z)

@[simp] theorem diskZeta_zero : diskZeta 0 = 1 := by simp [diskZeta]

theorem analyticAt_diskZeta {z : ℂ} (hz : z ≠ 1) : AnalyticAt ℂ diskZeta z := by
  have hc : AnalyticAt ℂ cayley z :=
    (analyticAt_const.sub analyticAt_id).inv (sub_ne_zero.mpr hz.symm)
  exact (analyticAt_regularZetaRatio (cayley_ne_zero hz)).comp hc

/-- No boundary regularity is required for analyticity on a strict subdisk. -/
theorem analyticOnNhd_diskZeta_closedBall {r : ℝ} (hr : |r| < 1) :
    AnalyticOnNhd ℂ diskZeta (Metric.closedBall 0 |r|) := by
  intro z hz
  apply analyticAt_diskZeta
  apply ne_one_of_norm_lt_one
  have h := Metric.mem_closedBall.mp hz
  rw [dist_zero_right] at h
  exact h.trans_lt hr

theorem diskZeta_eq {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    diskZeta z = z * riemannZeta (cayley z) := by
  have hz1 := ne_one_of_norm_lt_one hz
  have hc1 : cayley z ≠ 1 := by
    intro h
    have hh := diskCoordinate_cayley hz1
    rw [h] at hh
    simp [diskCoordinate] at hh
    exact hz0 hh.symm
  rw [diskZeta, regularZetaRatio_eq (by linarith [cayley_re_gt_half hz]) hc1]
  change diskCoordinate (cayley z) * riemannZeta (cayley z) = _
  rw [diskCoordinate_cayley hz1]

/-- The analytic disk function has precisely the transported zeta zeros,
with its center handled by the proved removable value. -/
theorem diskZeta_zero_iff {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) :
    diskZeta z = 0 ↔ riemannZeta (cayley z) = 0 := by
  rw [diskZeta_eq hz hz0, mul_eq_zero]
  simp [hz0]

/-- An exact Jensen identity for the actual zeta pullback on each strict subdisk. -/
theorem diskZeta_jensen {r : ℝ} (hr0 : r ≠ 0) (hr1 : |r| < 1) :
    Real.circleAverage (fun z => Real.log ‖diskZeta z‖) 0 r =
      ∑ᶠ u : ℂ,
        (MeromorphicOn.divisor diskZeta (Metric.closedBall 0 |r|) u : ℝ) *
          Real.log (r * ‖(0 : ℂ) - u‖⁻¹) := by
  simpa only [diskZeta_zero, norm_one, Real.log_one, add_zero] using
    (analyticOnNhd_diskZeta_closedBall hr1).circleAverage_log_norm hr0
      (by simp : diskZeta 0 ≠ 0)

end RiemannResearch.RH.Burnol
