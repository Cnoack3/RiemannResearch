import RiemannResearch.Analysis.ActualZeroDiscrepancy
import RiemannResearch.Analysis.SpectralResidualMeanSquare

/-!
# Actual integrated zero-count discrepancy and S₁ providers

The functions here use the actual multiplicity-weighted `Ncount` and the exact
smooth gamma contribution already constructed in `ActualZeroDiscrepancy`.
The argument discrepancy is right-continuous and is N minus (1 + smoothCount).
Its primitive is continuous, with a visible integration constant C.

The classical canonical normalization is expressed separately by
`CanonicalNormalization`; neither its improper-integral convergence nor the
identification with a conventional continued argument is asserted here.
Likewise the quantitative `MeanSquareError` and `ModeCorrelationError` are
named propositions about this actual primitive, not newly assumed axioms.

The final theorem discharges the polynomial mean square using MV26 and the
primitive's L² regularity. Only the two stated zeta-specific providers remain.

Source: A. Chirre and E. Quesada-Herrera, arXiv:2006.08503v2, (1.5) and footnote a.
Its unconditional S₁ mean-square error is O(T/log T); its sharper second-order
formula assumes RH and is not used here.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
open RiemannResearch.Analysis.ActualZeroDiscrepancy
open RiemannResearch.Analysis.SpectralResidualMeanSquare
open RiemannResearch.Analysis.ZeroOrdinate
open RiemannResearch.Analysis.DirichletMeanSquare

namespace RiemannResearch.Analysis.ActualIntegratedDiscrepancy

/-- Right-continuous version of the count/gamma argument discrepancy. -/
def argument (t : ℝ) : ℝ := discrepancy t - 1

/-- The actual S₁-type primitive, with its additive constant visible. -/
def primitive (C t : ℝ) : ℝ := C + ∫ u in 0..t, argument u

def complexPrimitive (C t : ℝ) : ℂ := (primitive C t : ℝ)

theorem argument_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable argument volume a b :=
  (discrepancy_intervalIntegrable a b).sub intervalIntegrable_const

theorem primitive_continuous (C : ℝ) : Continuous (primitive C) :=
  continuous_const.add (intervalIntegral.continuous_primitive
    argument_intervalIntegrable 0)

@[simp] theorem primitive_zero (C : ℝ) : primitive C 0 = C := by
  simp [primitive]

theorem primitive_sub_constant (C D t : ℝ) :
    primitive C t - primitive D t = C - D := by
  unfold primitive
  ring

/-- The primitive increments are exact; no endpoint-jump convention is needed. -/
theorem primitive_sub (C a b : ℝ) :
    primitive C b - primitive C a = ∫ u in a..b, argument u := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (argument_intervalIntegrable 0 a) (argument_intervalIntegrable a b)
  unfold primitive
  linarith

/-- Local L² regularity of the actual primitive is proved, not a provider. -/
theorem complexPrimitive_memLp (C A B : ℝ) :
    MemLp (complexPrimitive C) 2 (volume.restrict (Set.Ioc A B)) := by
  have hc : Continuous (complexPrimitive C) :=
    Complex.continuous_ofReal.comp (primitive_continuous C)
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  exact ((hc.norm.pow 2).intervalIntegrable A B).1

/-- The remaining absolute-normalization obligation in the conventional S₁.
The integral is over the real σ-axis, and convergence is included explicitly. -/
def CanonicalNormalization (C : ℝ) : Prop :=
  IntegrableOn (fun σ : ℝ => Real.log ‖riemannZeta (σ : ℂ)‖)
      (Set.Ioi (1 / 2 : ℝ)) volume ∧
    C = (1 / Real.pi) *
      ∫ σ in Set.Ioi (1 / 2 : ℝ), Real.log ‖riemannZeta (σ : ℂ)‖

/-- A quantitative actual S₁ mean-square provider. The classical theorem
would instantiate total = C₁/(2π²) and error T = O(T/log T). -/
def MeanSquareError (C total : ℝ) (error : ℝ → ℝ) : Prop :=
  ∀ T : ℝ, 2 ≤ T →
    |(∫ t in 0..T, ‖complexPrimitive C t‖ ^ 2) - T * total| ≤ error T

variable {ι : Type} [Fintype ι]

/-- Actual Fourier-correlation errors for the selected finite frequencies. -/
def ModeCorrelationError (C : ℝ) (c : ι → ℂ) (ω : ι → ℝ)
    (error : ℝ → ι → ℝ) : Prop :=
  ∀ T : ℝ, 2 ≤ T → ∀ i,
    ‖(∫ t in 0..T, complexPrimitive C t * star (phase (ω i) t)) -
      (T : ℂ) * c i‖ ≤ error T i

/-- Actual S₁ residual assembly with a fully discharged polynomial mean square.
The precise unresolved inputs are named actual energy and mode correlations. -/
theorem actual_primitive_residual_sq_le
    (C total : ℝ) (errS : ℝ → ℝ) (c : ι → ℂ) (ω δ : ι → ℝ)
    (errC : ℝ → ι → ℝ)
    (henergy : MeanSquareError C total errS)
    (hmodes : ModeCorrelationError C c ω errC)
    (hω : Function.Injective ω) (hδ : ∀ i, 0 < δ i)
    (hsep : ∀ i j, i ≠ j → δ i ≤ |ω i - ω j|)
    {T : ℝ} (hT : 2 ≤ T) :
    (∫ t in 0..T, ‖complexPrimitive C t - polynomial c ω t‖ ^ 2) ≤
      T * (total - ∑ i, ‖c i‖ ^ 2) + errS T +
        26 * ∑ i, ‖c i‖ ^ 2 / δ i + 2 * ∑ i, ‖c i‖ * errC T i := by
  classical
  have hs : (∫ t in 0..T, ‖complexPrimitive C t‖ ^ 2) ≤
      (T - 0) * total + errS T := by
    have h := (abs_le.mp (henergy T hT)).2
    linarith
  have hm : ∀ i, ‖(∫ t in 0..T, complexPrimitive C t * star (phase (ω i) t)) -
      ((T - 0 : ℝ) : ℂ) * c i‖ ≤ errC T i := by
    simpa only [sub_zero] using hmodes T hT
  simpa only [sub_zero] using separated_frequency_residual_sq_le
    (by linarith : 0 ≤ T) (complexPrimitive_memLp C 0 T) c ω δ
    hω hδ hsep total (errS T) (errC T) hs hm

end RiemannResearch.Analysis.ActualIntegratedDiscrepancy
