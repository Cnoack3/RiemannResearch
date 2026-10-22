import RiemannResearch.Analysis.WeightedMellinHardy
import RiemannResearch.RH.ChebyshevMellin

/-!
# Conditional energy-to-holomorphy and Hardy consequences for Chebyshev error

Source: user-requested RH_Energy_Holomorphy_Hardy_Implications_2026-09-18.md.
The hypotheses are actual weighted integrability of (psi(x)-x)^2.
These are conditional research reductions, not proofs of those energy bounds
or of the Riemann hypothesis. Identifying this energy assumption with the
prime-power signed prefix condition requires the further geometric transfer.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set

namespace RiemannResearch.RH.ChebyshevMellin
open MeasureTheory.WeightedMellin

/-- The remaining substantive energy assumption, expressed as an actual integral. -/
def ErrorFiniteEnergy (s : ℝ) : Prop :=
  IntegrableOn (fun x : ℝ => (Chebyshev.psi x-x)^2 * x^(-s-1)) (Ioi 1)

theorem error_finiteEnergy {s : ℝ} (hs : ErrorFiniteEnergy s) :
    FiniteEnergy (fun x : ℝ => (Chebyshev.psi x:ℂ)-(x:ℂ)) s := by
  refine ⟨(Complex.continuous_ofReal.measurable.comp psi_measurable).sub
    Complex.continuous_ofReal.measurable, ?_⟩
  simpa only [ErrorFiniteEnergy, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    using hs

theorem errorMellin_eq_transform :
    errorMellin = transform (fun x : ℝ => (Chebyshev.psi x:ℂ)-(x:ℂ)) := by
  funext z
  unfold errorMellin transform
  congr 1
  funext x
  rw [neg_add_rev]
  congr 2
  ring

/-- Conditional reduction: the actual Chebyshev energy supplies holomorphy. -/
theorem errorMellin_analyticAt_of_energy {s : ℝ} (hs : ErrorFiniteEnergy s)
    {z : ℂ} (hz : s/2 < z.re) : AnalyticAt ℂ errorMellin z := by
  rw [errorMellin_eq_transform]
  exact transform_analyticAt (error_finiteEnergy hs) hz

/-- Conditional reduction: the actual Chebyshev energy supplies Hardy H2. -/
theorem errorMellin_hardy_of_energy {s : ℝ} (hs : ErrorFiniteEnergy s) :
    HardyH2 errorMellin (s/2) := by
  rw [errorMellin_eq_transform]
  exact energy_to_hardy (error_finiteEnergy hs)

/-- All positive damping gives holomorphy on the open right critical half-plane. -/
theorem errorMellin_analyticAt_of_all_damping
    (h : ∀ ε : ℝ, 0 < ε → ErrorFiniteEnergy (1+ε))
    {z : ℂ} (hz : 1/2 < z.re) : AnalyticAt ℂ errorMellin z := by
  apply errorMellin_analyticAt_of_energy (h (z.re-1/2) (by linarith))
  linarith
end RiemannResearch.RH.ChebyshevMellin
