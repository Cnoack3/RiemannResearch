import RiemannResearch.RH.ParetoMellinInnovationRemainder
import RiemannResearch.RH.ParetoMellinProbeGeometry
import RiemannResearch.RH.QRamanujanMellinCertificates

/-!
# Sharp screened residual observations in actual P and Q

Source: algebraic consequences of the complete Schur remainder identity,
24 October 2026. Equality is characterized by exhaustion of the entire new
Mellin remainder. The Q formula retains its exact measure correction.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def mellinPhysicalInnovation (f : ThresholdHilbert) (s : ι → ℂ) (t : ℂ) : ℂ :=
  mellinSchurInnovation s (fun i => paretoMellin f (s i)) t (paretoMellin f t)

/-- Exact scaled error budget; the whole new integral appears on the right. -/
theorem mellinPhysicalInnovation_exact (f : ThresholdHilbert) (s : ι → ℂ) (t : ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) (ht : (1 / 2 : ℝ) < t.re)
    (hinj : Function.Injective s) (hnew : ∀ i, s i ≠ t) :
    mellinCenteredProduct s t * mellinProjectionRemainder f s =
      (2 * t.re - 1) * ‖mellinPhysicalInnovation f s t‖ ^ 2 +
      mellinCenteredProduct s t * mellinProjectionRemainder f (mellinAppend s t) := by
  have hp := (mellinCenteredProduct_pos s t hs ht hnew).ne'
  rw [mellinProjectionRemainder_append f s t hs ht hinj hnew]
  unfold mellinPhysicalInnovation
  field_simp
  <;> ring

theorem mellinPhysicalInnovation_sharp_bound (f : ThresholdHilbert) (s : ι → ℂ) (t : ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) (ht : (1 / 2 : ℝ) < t.re)
    (hinj : Function.Injective s) (hnew : ∀ i, s i ≠ t) :
    ‖mellinPhysicalInnovation f s t‖ ^ 2 ≤
      mellinCenteredProduct s t * mellinProjectionRemainder f s / (2 * t.re - 1) := by
  have he := mellinPhysicalInnovation_exact f s t hs ht hinj hnew
  have hr := mul_nonneg (mellinCenteredProduct_nonneg s t)
    (mellinProjectionRemainder_nonneg f (mellinAppend s t))
  apply (le_div_iff₀ (by linarith : 0 < 2 * t.re - 1)).mpr
  nlinarith

/-- Saturation of the screened bound is exactly complete exhaustion by the enlarged probes. -/
theorem mellinPhysicalInnovation_bound_eq_iff (f : ThresholdHilbert) (s : ι → ℂ) (t : ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) (ht : (1 / 2 : ℝ) < t.re)
    (hinj : Function.Injective s) (hnew : ∀ i, s i ≠ t) :
    ‖mellinPhysicalInnovation f s t‖ ^ 2 =
      mellinCenteredProduct s t * mellinProjectionRemainder f s / (2 * t.re - 1) ↔
        mellinProjectionRemainder f (mellinAppend s t) = 0 := by
  have he := mellinPhysicalInnovation_exact f s t hs ht hinj hnew
  have hp := mellinCenteredProduct_pos s t hs ht hnew
  rw [eq_div_iff (by linarith : 2 * t.re - 1 ≠ 0)]
  constructor <;> intro h <;> nlinarith

/-- Every nonempty old probe family strictly improves the unscreened residual bound. -/
theorem mellinPhysicalInnovation_strict_unscreened_bound [Nonempty ι]
    (f : ThresholdHilbert) (s : ι → ℂ) (t : ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) (ht : (1 / 2 : ℝ) < t.re)
    (hinj : Function.Injective s) (hnew : ∀ i, s i ≠ t)
    (hr : 0 < mellinProjectionRemainder f s) :
    ‖mellinPhysicalInnovation f s t‖ ^ 2 <
      mellinProjectionRemainder f s / (2 * t.re - 1) := by
  have hb := mellinPhysicalInnovation_sharp_bound f s t hs ht hinj hnew
  have hp := mellinCenteredProduct_lt_one s t hs ht
  apply hb.trans_lt
  apply (div_lt_div_iff_of_pos_right (by linarith : 0 < 2 * t.re - 1)).mpr
  nlinarith

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.QRamanujanMellinCertificates
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QParetoMetric QMellinTransfer
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The available Q budget excludes precisely the observed capacity and the
full measure correction, with the whole new remainder retained. -/
theorem qMellin_screened_budget_exact (f : QHilbert) (s : ι → ℂ) (t : ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) (ht : (1 / 2 : ℝ) < t.re)
    (hinj : Function.Injective s) (hnew : ∀ i, s i ≠ t) :
    mellinCenteredProduct s t *
      (zetaTwo * ‖f‖ ^ 2 - metricCorrection f -
        mellinInverseCapacity s (fun i => qMellin f (s i))) =
      (2 * t.re - 1) *
        ‖mellinSchurInnovation s (fun i => qMellin f (s i)) t (qMellin f t)‖ ^ 2 +
      mellinCenteredProduct s t * mellinProjectionRemainder (toPareto f) (mellinAppend s t) := by
  have hc := qMellin_inverse_capacity_completion f s hs hinj
  have he := mellinPhysicalInnovation_exact (toPareto f) s t hs ht hinj hnew
  have hr : zetaTwo * ‖f‖ ^ 2 - metricCorrection f -
      mellinInverseCapacity s (fun i => qMellin f (s i)) =
      mellinProjectionRemainder (toPareto f) s := by linarith
  rw [hr]
  exact he

end RiemannResearch.RH.QRamanujanMellinCertificates
