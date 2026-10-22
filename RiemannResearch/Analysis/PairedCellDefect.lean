import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic

/-!
# A sharper signed physical-cell defect bound

Source: user-provided CRT and Four Improvements continuation, 6–7 October 2026.
The extensions retain complete signed identities and correction squares.


The tail loss on a cell of length h is at most h times the first fractional
moment on that cell.  The previous argument used the larger factor 2h.  Pairing
s and h-s proves the sharper estimate before any absolute values are taken.
The global identification with Euler's constant is a separate analytic input.
-/

noncomputable section
open MeasureTheory Set

namespace RiemannResearch.Analysis.PairedCellDefect

def cellLoss (a u s : ℝ) : ℝ := (2 * u * s + s ^ 2) / (a + s) ^ 2
def cellMoment (a u s : ℝ) : ℝ := (u + s) / (a + s) ^ 2
def cellDefect (a u h s : ℝ) : ℝ := h * cellMoment a u s - cellLoss a u s

theorem cellDefect_eq (a u h s : ℝ) :
    cellDefect a u h s =
      (u * (h - 2 * s) + s * (h - s)) / (a + s) ^ 2 := by
  unfold cellDefect cellMoment cellLoss
  ring

/-- The complete signed pair retains both nonnegative contributions. -/
theorem cellDefect_pair_eq (a u h s : ℝ) :
    cellDefect a u h s + cellDefect a u h (h - s) =
      u * (h - 2 * s) * (1 / (a + s) ^ 2 - 1 / (a + h - s) ^ 2) +
        s * (h - s) * (1 / (a + s) ^ 2 + 1 / (a + h - s) ^ 2) := by
  rw [cellDefect_eq, cellDefect_eq]
  have he : a + (h - s) = a + h - s := by ring
  rw [he]
  ring

theorem cellDefect_pair_nonneg_half {a u h s : ℝ}
    (ha : 0 < a) (hu : 0 ≤ u) (hs0 : 0 ≤ s) (hs1 : s ≤ h / 2) :
    0 ≤ cellDefect a u h s + cellDefect a u h (h - s) := by
  rw [cellDefect_pair_eq]
  have hA : 0 < a + s := by linarith
  have hB : a + s ≤ a + h - s := by linarith
  have hsq : (a + s) ^ 2 ≤ (a + h - s) ^ 2 :=
    (sq_le_sq₀ hA.le (by linarith)).mpr hB
  have hinv : 1 / (a + h - s) ^ 2 ≤ 1 / (a + s) ^ 2 :=
    one_div_le_one_div_of_le (sq_pos_of_pos hA) hsq
  have hfirst : 0 ≤ u * (h - 2 * s) *
      (1 / (a + s) ^ 2 - 1 / (a + h - s) ^ 2) :=
    mul_nonneg (mul_nonneg hu (by linarith)) (sub_nonneg.mpr hinv)
  have hsecond : 0 ≤ s * (h - s) *
      (1 / (a + s) ^ 2 + 1 / (a + h - s) ^ 2) :=
    mul_nonneg (mul_nonneg hs0 (by linarith)) (by positivity)
  exact add_nonneg hfirst hsecond

theorem cellDefect_pair_nonneg {a u h s : ℝ}
    (ha : 0 < a) (hu : 0 ≤ u) (hs0 : 0 ≤ s) (hs1 : s ≤ h) :
    0 ≤ cellDefect a u h s + cellDefect a u h (h - s) := by
  by_cases hs : s ≤ h / 2
  · exact cellDefect_pair_nonneg_half ha hu hs0 hs
  · have ht := cellDefect_pair_nonneg_half (a := a) (u := u) (h := h) (s := h - s) ha hu
      (by linarith) (by linarith)
    rw [show h - (h - s) = s by ring] at ht
    simpa only [add_comm] using ht

private theorem rational_cell_integrable {a h : ℝ} (ha : 0 < a) (hh : 0 ≤ h)
    (f : ℝ → ℝ) (hf : Continuous f) :
    IntervalIntegrable (fun s => f s / (a + s) ^ 2) volume 0 h := by
  have hc : ContinuousOn (fun s => f s / (a + s) ^ 2) (uIcc 0 h) := by
    apply hf.continuousOn.div (by fun_prop)
    intro s hs
    rw [uIcc_of_le hh] at hs
    exact pow_ne_zero 2 (ne_of_gt (by linarith [hs.1] : 0 < a + s))
  exact hc.intervalIntegrable

theorem cellLoss_integrable {a h : ℝ} (ha : 0 < a) (hh : 0 ≤ h) (u : ℝ) :
    IntervalIntegrable (cellLoss a u) volume 0 h := by
  unfold cellLoss
  exact rational_cell_integrable ha hh _ (by fun_prop)

theorem cellMoment_integrable {a h : ℝ} (ha : 0 < a) (hh : 0 ≤ h) (u : ℝ) :
    IntervalIntegrable (cellMoment a u) volume 0 h := by
  unfold cellMoment
  exact rational_cell_integrable ha hh _ (by fun_prop)

theorem cellDefect_integrable {a h : ℝ} (ha : 0 < a) (hh : 0 ≤ h) (u : ℝ) :
    IntervalIntegrable (cellDefect a u h) volume 0 h := by
  unfold cellDefect
  exact ((cellMoment_integrable ha hh u).const_mul h).sub
    (cellLoss_integrable ha hh u)

/-- The sharper finite cell inequality, with all smooth integrability inputs
discharged from positivity of the actual tail-cell origin. -/
theorem cellLoss_integral_le_moment {a u h : ℝ}
    (ha : 0 < a) (hu : 0 ≤ u) (hh : 0 ≤ h) :
    (∫ s in 0..h, cellLoss a u s) ≤
      h * (∫ s in 0..h, cellMoment a u s) := by
  have hf := cellDefect_integrable ha hh u
  have hcont : ContinuousOn (cellDefect a u h) (uIcc 0 h) := by
    have he : cellDefect a u h = fun s =>
        (u * (h - 2 * s) + s * (h - s)) / (a + s) ^ 2 :=
      funext (cellDefect_eq a u h)
    rw [he]
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro s hs
    rw [uIcc_of_le hh] at hs
    exact pow_ne_zero 2 (ne_of_gt (by linarith [hs.1] : 0 < a + s))
  have hreflect : IntervalIntegrable (fun s => cellDefect a u h (h - s)) volume 0 h := by
    apply ContinuousOn.intervalIntegrable
    apply hcont.comp (by fun_prop)
    intro s hs
    rw [uIcc_of_le hh] at hs ⊢
    constructor <;> linarith [hs.1, hs.2]
  have hpair : 0 ≤ ∫ s in 0..h,
      cellDefect a u h s + cellDefect a u h (h - s) := by
    apply intervalIntegral.integral_nonneg hh
    intro s hs
    exact cellDefect_pair_nonneg ha hu hs.1 hs.2
  rw [intervalIntegral.integral_add hf hreflect] at hpair
  have href : (∫ s in 0..h, cellDefect a u h (h - s)) =
      ∫ s in 0..h, cellDefect a u h s := by
    simpa only [sub_self, sub_zero] using
      intervalIntegral.integral_comp_sub_left (cellDefect a u h) h (a := 0) (b := h)
  rw [href] at hpair
  have hnonneg : 0 ≤ ∫ s in 0..h, cellDefect a u h s := by linarith
  unfold cellDefect at hnonneg
  rw [intervalIntegral.integral_sub
    ((cellMoment_integrable ha hh u).const_mul h) (cellLoss_integrable ha hh u),
    intervalIntegral.integral_const_mul] at hnonneg
  linarith

end RiemannResearch.Analysis.PairedCellDefect
