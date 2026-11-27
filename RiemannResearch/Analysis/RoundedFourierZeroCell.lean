import RiemannResearch.Analysis.RoundedFourierCellParseval
import RiemannResearch.Analysis.ActualZeroCountNormalization
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Vanishing of the constant Fourier cell on the fine prime-word mesh

The cell of integer word order zero has physical Fourier width h/log T.
Although its actual amplitude equals the entire zero count, after the
pair normalization its signed contribution tends to zero for h ≤ T⁻³ and
bounded weights. The collision subtraction extends over all cells.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped Topology

namespace RiemannResearch.Analysis.RoundedFourierCellParseval
open ActualZeroOrdinate

/-- The left tie belongs to the zero-order cell and the right tie belongs to
the next integer, by Lean's rounding convention. -/
theorem roundedOrder_zero_cell {T h : ℝ} (hT : 1 < T) (hh : 0 < h) :
    roundedOrder T h ⁻¹' {0} = Ico (-(h/2)/Real.log T) ((h/2)/Real.log T) := by
  have hL := Real.log_pos hT
  ext v
  change round (Real.log T * v / h) = 0 ↔ -(h/2)/Real.log T ≤ v ∧ v < (h/2)/Real.log T
  rw [round_eq_zero_iff]
  change (-(1 / 2) ≤ Real.log T * v / h ∧ Real.log T * v / h < 1 / 2) ↔ _
  rw [le_div_iff₀ hh, div_lt_iff₀ hh, div_le_iff₀ hL, lt_div_iff₀ hL]
  ring_nf

theorem abs_central_cellMass_le {T h : ℝ} (hT : 1 < T) (hh : 0 < h)
    (w : ℝ → ℝ) {C : ℝ} (hC : ∀ v, |w v| ≤ C) :
    |cellMass (roundedOrder T h) w 0| ≤ C * (h / Real.log T) := by
  have hL := Real.log_pos hT
  let l := -(h / 2) / Real.log T
  let r := (h / 2) / Real.log T
  have hlr : l ≤ r := div_le_div_of_nonneg_right (by linarith) hL.le
  have hlen : r - l = h / Real.log T := by dsimp [r, l]; ring
  have hbound := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := w)
    (s := Ico l r) (by rw [Real.volume_Ico]; exact ENNReal.ofReal_lt_top)
    (fun x _ => by simpa only [Real.norm_eq_abs] using hC x)
  rw [Real.volume_real_Ico_of_le hlr, hlen, Real.norm_eq_abs] at hbound
  simpa only [cellMass, roundedOrder_zero_cell hT hh] using hbound

/-- Signed contribution of the ordinary constant Fourier coefficient before
the separate full equal-height subtraction. -/
def centralWordContribution (T h : ℝ) (w : ℝ → ℝ) : ℝ :=
  cellMass (roundedOrder T h) w 0 * (Ncount 0 T : ℝ)^2 /
    (2 * (T * Real.log T / (2 * Real.pi)))

/-- Eventually the absolute normalized contribution is at most C/(π T²). -/
theorem eventually_centralWordContribution_le {h : ℝ → ℝ}
    (hh : ∀ᶠ T in atTop, 0 < h T ∧ h T ≤ 1 / T^3)
    (w : ℝ → ℝ) {C : ℝ} (hC : ∀ v, |w v| ≤ C) :
    ∀ᶠ T in atTop, |centralWordContribution T (h T) w| ≤ (C / Real.pi) * (T⁻¹)^2 := by
  have hcount := tendsto_count_div_mainTerm.eventually
    (eventually_lt_nhds (show (1:ℝ) < 2 by norm_num))
  filter_upwards [hh, hcount, eventually_gt_atTop (1:ℝ)] with T hm hc hT
  have hpos := zero_lt_one.trans hT
  have hL := Real.log_pos hT
  let D := T * Real.log T / (2 * Real.pi)
  have hD : 0 < D := by dsimp [D]; positivity
  have hN : (Ncount 0 T : ℝ) ≤ 2 * D := ((div_lt_iff₀ hD).mp hc).le
  have hC₀ := (abs_nonneg (w 0)).trans (hC 0)
  have ha := abs_central_cellMass_le hT hm.1 w hC
  change |cellMass (roundedOrder T (h T)) w 0 * (Ncount 0 T : ℝ)^2 / (2 * D)| ≤ _
  rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg (Ncount 0 T : ℝ)), abs_of_pos (by positivity : 0 < 2 * D)]
  calc
    _ ≤ (C * ((1 / T^3) / Real.log T)) * (2 * D)^2 / (2 * D) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      apply mul_le_mul _ (pow_le_pow_left₀ (Nat.cast_nonneg _) hN 2) (sq_nonneg _) (by positivity)
      exact ha.trans (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hm.2 hL.le) hC₀)
    _ = _ := by dsimp only [D]; field_simp

theorem centralWordContribution_tendsto_zero {h : ℝ → ℝ}
    (hh : ∀ᶠ T in atTop, 0 < h T ∧ h T ≤ 1 / T^3)
    (w : ℝ → ℝ) {C : ℝ} (hC : ∀ v, |w v| ≤ C) :
    Tendsto (fun T => centralWordContribution T (h T) w) atTop (𝓝 0) := by
  apply squeeze_zero_norm'
  · simpa only [Real.norm_eq_abs] using eventually_centralWordContribution_le hh w hC
  · simpa using ((tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0)).pow 2).const_mul (C / Real.pi)

end RiemannResearch.Analysis.RoundedFourierCellParseval
