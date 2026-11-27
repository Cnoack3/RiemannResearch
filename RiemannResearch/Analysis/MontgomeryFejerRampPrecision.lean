import RiemannResearch.Analysis.MontgomeryPhysicalGapTransfer
import RiemannResearch.Analysis.MontgomeryMacroscopicGap

/-!
# Fejér precision for RH and simplicity

The raw sine-process tent contracts the spike plus ramp/plateau law
to 1 + 1/(3R²) for R ≥ 1. We remove the model baseline 1, restore the
exact finite diagonal N(T), and compare the remaining physical total
with D(T)/(3R²), where D(T) = T log T / (2π). This defines a signed
discrepancy in units of individual ordered pairs. The one-sided bound in
the transfer theorem is an additional arithmetic hypothesis.
-/

noncomputable section
open Filter MeasureTheory Zeta23
open scoped Topology

namespace RiemannResearch.Analysis.MontgomeryFormFactor
open MontgomeryPositiveGap ActualZeroOrdinate ActualZeroCollisionCertificate

/-- The exact finite Fejér energy, centered by its number of labels and the
ramp correction of the sine model. Each term is in absolute pair units. -/
def fejerSineRampDiscrepancy (T R : ℝ) : ℝ :=
  unfoldedCutoff T * fejerFormFactor T R - (Ncount 0 T : ℝ) -
    unfoldedCutoff T * ((1 / R) *
      (1 + ∫ a in (-R)..R, (1 - |a| / R) * min |a| 1) - 1)

/-- Separate the exact collision excess, the nonnegative unequal-ordinate
remainder, and the signed model correction. -/
theorem fejerSineRampDiscrepancy_eq {T R : ℝ} (hT : 1 < T) (hR : 1 ≤ R) :
    fejerSineRampDiscrepancy T R =
      ((actualCollision T : ℝ) - Ncount 0 T) + fejerNonzeroGapRemainder T R -
        unfoldedCutoff T / (3 * R^2) := by
  rw [fejerSineRampDiscrepancy, fejer_model_value hR]
  change (T * Real.log T / (2 * Real.pi)) * fejerFormFactor T R - _ - _ = _
  rw [normalized_fejer_eq_collision_add_nonzeroGap hT (zero_lt_one.trans_le hR)]
  ring

/-- A single exceptional zero forces a one-sided discrepancy at every
large height and every bandwidth R ≥ 1, with the explicit ramp loss. -/
theorem eventually_fejerSineRampDiscrepancy_lower_of_global_failure
    (h : ¬ (RiemannHypothesis ∧ ∀ ρ : ℂ, IsNontrivialZero ρ → zeroMult ρ = 1)) :
    ∀ᶠ T : ℝ in atTop, ∀ R : ℝ, 1 ≤ R →
      2 - unfoldedCutoff T / (3 * R^2) ≤ fejerSineRampDiscrepancy T R := by
  filter_upwards [eventually_two_le_collision_excess_of_global_failure h,
    eventually_gt_atTop (1 : ℝ)] with T hbad hT
  intro R hR
  have hbad' : (Ncount 0 T : ℝ) + 2 ≤ actualCollision T := by exact_mod_cast hbad
  rw [fejerSineRampDiscrepancy_eq hT hR]
  linarith only [hbad', fejerNonzeroGapRemainder_nonneg T R]

/-- A cofinal upper error c in absolute pair units rules out every
exception provided the model ramp also fits inside the two-pair budget.
In particular a vanishing absolute upper error allows any limiting
ratio D(T)/R(T)² strictly below six. -/
theorem global_of_cofinal_fejerSineRampDiscrepancy {c : ℝ} {R : ℝ → ℝ}
    (h : ∃ᶠ T : ℝ in atTop, 1 ≤ R T ∧ fejerSineRampDiscrepancy T (R T) ≤ c ∧
      unfoldedCutoff T / (3 * (R T)^2) < 2 - c) :
    RiemannHypothesis ∧ ∀ ρ : ℂ, IsNontrivialZero ρ → zeroMult ρ = 1 := by
  by_contra hfail
  obtain ⟨T, ht, hl⟩ := (h.and_eventually
    (eventually_fejerSineRampDiscrepancy_lower_of_global_failure hfail)).exists
  linarith only [hl (R T) ht.1, ht.2.1, ht.2.2]

/-- Moving-bandwidth limit version. A signed upper-error limit c and
window-bias limit κ/3 are sufficient precisely at the strict budget
c + κ/3 < 2 in this estimate. -/
theorem global_of_fejerSineRamp_limits {c κ : ℝ} {R : ℝ → ℝ}
    (hR : ∀ᶠ T : ℝ in atTop, 1 ≤ R T)
    (herr : Tendsto (fun T => fejerSineRampDiscrepancy T (R T)) atTop (𝓝 c))
    (hratio : Tendsto (fun T => unfoldedCutoff T / (R T)^2) atTop (𝓝 κ))
    (hbudget : c + κ/3 < 2) :
    RiemannHypothesis ∧ ∀ ρ : ℂ, IsNontrivialZero ρ → zeroMult ρ = 1 := by
  by_contra hfail
  have hlim := herr.add (hratio.div_const 3)
  obtain ⟨T, hrad, hlo, hhi⟩ :=
    (hR.and ((eventually_fejerSineRampDiscrepancy_lower_of_global_failure hfail).and
      (hlim.eventually_lt_const hbudget))).exists
  change fejerSineRampDiscrepancy T (R T) + unfoldedCutoff T / (R T)^2 / 3 < 2 at hhi
  have he : unfoldedCutoff T / (R T)^2 / 3 = unfoldedCutoff T / (3 * (R T)^2) := by
    rw [div_div, mul_comm]
  rw [he] at hhi
  linarith only [hlo (R T) hrad, hhi]

end RiemannResearch.Analysis.MontgomeryFormFactor
