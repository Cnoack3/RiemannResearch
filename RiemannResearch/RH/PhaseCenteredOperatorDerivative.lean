import RiemannResearch.RH.PhaseCenteredActualOperator
import RiemannResearch.RH.ParetoMellinOperatorDerivative
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
open MeasureTheory Set
namespace RiemannResearch.RH.Pareto.CompressedMellin

theorem phaseMellinForward_hasDerivAt (t : ℝ) (ht : 0 < t) :
    HasDerivAt phaseMellinForward
      (Complex.I * (Real.log t : ℂ) * phaseMellinForward t) t := by
  have hφ : HasDerivAt (fun u : ℝ => u * Real.log u - u) (Real.log t) t := by
    convert! ((hasDerivAt_id t).mul (Real.hasDerivAt_log ht.ne')).sub
      (hasDerivAt_id t) using 1 <;>
      simp [Pi.mul_apply, Pi.sub_apply, id_eq, ht.ne', div_eq_mul_inv] <;> ring
  have h := (hφ.ofReal_comp.const_mul Complex.I).cexp
  convert h using 1
  · rfl
  · unfold phaseMellinForward
    ring

def actualPhaseCenteredDerivativeOperator (t : ℝ) : ThresholdHilbert →L[ℝ] ℂ :=
  (Complex.I * (Real.log t : ℂ) * phaseMellinForward t) • mellinLineOperator t +
    phaseMellinForward t • mellinLineDerivativeOperator t

theorem actualPhaseCenteredOperator_hasDerivAt (t : ℝ) (ht : 0 < t) :
    HasDerivAt actualPhaseCenteredOperator (actualPhaseCenteredDerivativeOperator t) t := by
  convert! (phaseMellinForward_hasDerivAt t ht).smul
    (mellinLineOperator_hasDerivAt t) using 1 <;>
    first | rfl | exact add_comm _ _

theorem actualPhaseCenteredOperator_differentiableAt (t : ℝ) (ht : 0 < t) :
    DifferentiableAt ℝ actualPhaseCenteredOperator t :=
  (actualPhaseCenteredOperator_hasDerivAt t ht).differentiableAt

theorem actualPhaseCenteredOperator_deriv (t : ℝ) (ht : 0 < t) :
    deriv actualPhaseCenteredOperator t = actualPhaseCenteredDerivativeOperator t :=
  (actualPhaseCenteredOperator_hasDerivAt t ht).deriv

theorem actualPhaseCenteredDerivativeOperator_apply (t : ℝ) (f : ThresholdHilbert) :
    actualPhaseCenteredDerivativeOperator t f =
      ∫ x in Ioi (1 : ℝ), Complex.I * ((Real.log t - Real.log x : ℝ) : ℂ) *
        phaseMellinForward t * (hilbertSequence f ⌊x⌋₊ : ℂ) *
          (x : ℂ) ^ (-phaseMellinPoint t - 1) := by
  let a : ℂ := Complex.I * (Real.log t : ℂ) * phaseMellinForward t
  let b : ℂ := phaseMellinForward t
  have hi := mellinKernelPairing_integrable (mellinLineKernel t) (mellinLineKernel_memLp t) f
  have hd := mellinKernelPairing_integrable (mellinLineDerivativeKernel t)
    (mellinLineDerivativeKernel_memLp t) f
  change a * (∫ x in Ioi (1 : ℝ), mellinWeightedStep f x * mellinLineKernel t x) +
    b * (∫ x in Ioi (1 : ℝ), mellinWeightedStep f x * mellinLineDerivativeKernel t x) = _
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hi.const_mul a) (hd.const_mul b)]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans zero_lt_one hx))
  dsimp only
  rw [Complex.cpow_sub (-phaseMellinPoint t) 1 hxC, Complex.cpow_one]
  simp only [a, b, mellinWeightedStep, mellinLineDerivativeKernel, mellinLogKernel,
    mellinLineKernel, paretoMellinKernel, pow_one, phaseMellinPoint, mellinLinePoint,
    Complex.ofReal_sub]
  ring

end RiemannResearch.RH.Pareto.CompressedMellin
