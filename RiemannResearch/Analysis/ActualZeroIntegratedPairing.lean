import RiemannResearch.Analysis.ActualZeroAbelPairing
import RiemannResearch.Analysis.ActualIntegratedDiscrepancy
import RiemannResearch.Analysis.SpectralDerivativePairing

/-!
# Actual zero sums: signed S₁ decomposition and J₄ remainder

This joins the actual finite zero-count Abel theorem to the actual integrated
discrepancy, proves the required right-derivative regularity, retains the two
signed boundary terms, and applies the MV/J₄ residual estimate. The quantitative
inputs are precisely the named actual S₁ energy and mode-correlation providers;
no hypothesis restates the resulting zero-sum error bound.
-/

noncomputable section
open MeasureTheory Filter Zeta23
open scoped BigOperators Topology
open RiemannResearch.Analysis.ActualZeroDiscrepancy
open RiemannResearch.Analysis.ActualIntegratedDiscrepancy
open RiemannResearch.Analysis.ActualZeroAbelPairing
open RiemannResearch.Analysis.IntegratedCountingPairing
open RiemannResearch.Analysis.DirichletMeanSquare
open RiemannResearch.Analysis.SpectralDerivativePairing

namespace RiemannResearch.Analysis.ActualZeroIntegratedPairing

def complexArgument (t : ℝ) : ℂ := (argument t : ℝ)

def complexSmooth (t : ℝ) : ℂ := ((1 + smoothCount t : ℝ) : ℂ)

private theorem step_continuousWithinAt (y w t : ℝ) :
    ContinuousWithinAt (fun x => if y ≤ x then w else 0) (Set.Ioi t) t := by
  by_cases h : y ≤ t
  · apply continuousWithinAt_const.congr_of_eventuallyEq
      (f := fun _ : ℝ => w)
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact if_pos (h.trans hx.le)
    · exact if_pos h
  · apply continuousWithinAt_const.congr_of_eventuallyEq
      (f := fun _ : ℝ => (0 : ℝ))
    · filter_upwards [(eventually_lt_nhds (lt_of_not_ge h)).filter_mono
        nhdsWithin_le_nhds] with x hx
      exact if_neg (not_le.mpr hx)
    · exact if_neg h

/-- Local finiteness and the upper-inclusive convention prove right continuity
of the actual count, including at multiple-zero heights. -/
theorem count_continuousWithinAt_right (t : ℝ) :
    ContinuousWithinAt (fun x => (Ncount 0 x : ℝ)) (Set.Ioi t) t := by
  classical
  let g : ℝ → ℝ := fun x => ∑ ρ ∈ ActualZeroOrdinate.cutoff (t + 1),
    if ρ.im ≤ x then (zeroMult ρ : ℝ) else 0
  have heq (x : ℝ) (hx : x ≤ t + 1) : (Ncount 0 x : ℝ) = g x := by
    have h := congrArg Complex.re (count_eq_finite_steps hx)
    simpa [g, apply_ite] using h
  have hg : ContinuousWithinAt g (Set.Ioi t) t := by
    exact tendsto_finsetSum _ (fun ρ hρ =>
      step_continuousWithinAt ρ.im (zeroMult ρ) t)
  apply hg.congr_of_eventuallyEq
  · filter_upwards [(eventually_lt_nhds (by linarith : t < t + 1)).filter_mono
      nhdsWithin_le_nhds] with x hx
    exact heq x hx.le
  · exact heq t (by linarith)

theorem complexArgument_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable complexArgument volume a b := by
  have h := argument_intervalIntegrable a b
  exact ⟨Complex.ofRealCLM.integrable_comp h.1, Complex.ofRealCLM.integrable_comp h.2⟩

theorem complexArgument_continuousWithinAt_right (t : ℝ) :
    ContinuousWithinAt complexArgument (Set.Ioi t) t := by
  have h : ContinuousWithinAt argument (Set.Ioi t) t :=
    ((count_continuousWithinAt_right t).sub smoothCount_continuous.continuousWithinAt).sub
      continuousWithinAt_const
  exact Complex.continuous_ofReal.continuousAt.comp_continuousWithinAt h

/-- The actual primitive has the right derivative used in the signed formula;
this regularity is proved even at zero heights. -/
theorem complexPrimitive_hasDerivWithinAt_right (C t : ℝ) :
    HasDerivWithinAt (complexPrimitive C) (complexArgument t) (Set.Ioi t) t := by
  have hm : Measurable complexArgument :=
    Complex.continuous_ofReal.measurable.comp
      (discrepancy_measurable.sub measurable_const)
  have h := intervalIntegral.integral_hasDerivWithinAt_right
    (s := Set.Ici t) (t := Set.Ioi t)
    (complexArgument_intervalIntegrable 0 t)
    hm.stronglyMeasurable.stronglyMeasurableAtFilter
    (complexArgument_continuousWithinAt_right t)
  have heq : complexPrimitive C = fun x => (C : ℂ) + ∫ u in 0..x, complexArgument u := by
    funext x
    simp only [complexPrimitive, primitive, complexArgument, Complex.ofReal_add,
      intervalIntegral.integral_ofReal]
  rw [heq]
  exact (h.const_add (C : ℂ)).mono Set.Ioi_subset_Ici_self

theorem complexSmooth_hasDerivAt (t : ℝ) :
    HasDerivAt complexSmooth (mu t : ℂ) t := by
  have hc : Continuous (fun x => (mu x : ℂ)) :=
    Complex.continuous_ofReal.comp (RvM.mu_continuous gammaFacts)
  have h := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 t) hc.stronglyMeasurable.stronglyMeasurableAtFilter
    hc.continuousAt
  have heq : complexSmooth = fun x => (1 : ℂ) + ∫ u in 0..x, (mu u : ℂ) := by
    funext x
    simp only [complexSmooth, smoothCount, Complex.ofReal_add, Complex.ofReal_one,
      intervalIntegral.integral_ofReal]
  rw [heq]
  exact h.const_add (1 : ℂ)

theorem complexSmooth_add_argument (t : ℝ) :
    complexSmooth t + complexArgument t = (Ncount 0 t : ℂ) := by
  unfold complexSmooth complexArgument argument discrepancy
  push_cast
  ring

variable {ι : Type} [Fintype ι]

/-- The complete signed second-integration formula for actual zero sums
and an actual finite exponential polynomial. -/
theorem actual_sum_sub_eq_twice_integrated
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (C : ℝ)
    (c : ι → ℂ) (ω : ι → ℝ) :
    ActualZeroOrdinate.sum b (fun ρ => polynomial c ω ρ.im) -
      ActualZeroOrdinate.sum a (fun ρ => polynomial c ω ρ.im) =
      (∫ t in a..b, (mu t : ℂ) * polynomial c ω t) +
        boundary complexArgument (complexPrimitive C)
          (polynomial c ω) (polynomial (derivativeCoeff c ω) ω) a b +
      ∫ t in a..b, complexPrimitive C t * polynomial (secondCoeff c ω) ω t := by
  classical
  have hF := polynomial_continuous c ω
  have hF₁ := polynomial_continuous (derivativeCoeff c ω) ω
  have hF₂ := polynomial_continuous (secondCoeff c ω) ω
  have hM : Continuous complexSmooth :=
    Complex.continuous_ofReal.comp (continuous_const.add smoothCount_continuous)
  have hU : Continuous (complexPrimitive C) :=
    Complex.continuous_ofReal.comp (primitive_continuous C)
  have hmu : Continuous (fun t => (mu t : ℂ)) :=
    Complex.continuous_ofReal.comp (RvM.mu_continuous gammaFacts)
  have hF₁der (t : ℝ) : HasDerivAt (polynomial (derivativeCoeff c ω) ω)
      (polynomial (secondCoeff c ω) ω t) t := by
    simpa only [derivativeCoeff_twice] using
      hasDerivAt_polynomial (derivativeCoeff c ω) ω t
  rw [← abelPairing_count_eq_actual_sum_sub ha hab
    (fun t _ => hasDerivAt_polynomial c ω t) (hF₁.intervalIntegrable 0 b)]
  have hid := abelPairing_eq_twice_integrated hM.continuousOn hU.continuousOn
    hF.continuousOn hF₁.continuousOn
    (fun t _ => (complexSmooth_hasDerivAt t).hasDerivWithinAt)
    (fun t _ => complexPrimitive_hasDerivWithinAt_right C t)
    (fun t _ => (hasDerivAt_polynomial c ω t).hasDerivWithinAt)
    (fun t _ => (hF₁der t).hasDerivWithinAt)
    (hmu.intervalIntegrable a b) (complexArgument_intervalIntegrable a b)
    (hF₁.intervalIntegrable a b) (hF₂.intervalIntegrable a b)
  simpa only [complexSmooth_add_argument] using hid

/-- The exact remainder after subtracting a continuous approximation P from
the actual S₁ primitive. All zero sums and boundary terms are retained. -/
theorem actual_remainder_eq_residual
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (C : ℝ)
    (c : ι → ℂ) (ω : ι → ℝ) (P : ℝ → ℂ) (hP : Continuous P) :
    ActualZeroOrdinate.sum b (fun ρ => polynomial c ω ρ.im) -
      ActualZeroOrdinate.sum a (fun ρ => polynomial c ω ρ.im) -
      (∫ t in a..b, (mu t : ℂ) * polynomial c ω t) -
      boundary complexArgument (complexPrimitive C)
        (polynomial c ω) (polynomial (derivativeCoeff c ω) ω) a b -
      (∫ t in a..b, P t * polynomial (secondCoeff c ω) ω t) =
      ∫ t in a..b, (complexPrimitive C t - P t) *
        deriv (deriv (polynomial c ω)) t := by
  classical
  rw [actual_sum_sub_eq_twice_integrated ha hab C c ω]
  have hU : Continuous (complexPrimitive C) :=
    Complex.continuous_ofReal.comp (primitive_continuous C)
  rw [integral_subtraction_identity hU.continuousOn hP.continuousOn
    ((polynomial_continuous (secondCoeff c ω) ω).intervalIntegrable a b)]
  simp only [second_derivative_polynomial]
  ring

variable {κ : Type} [Fintype κ]

/-- Actual-zero J₄ bound with the S₁ approximation budget proved from the named
energy and individual mode-correlation providers. Polynomial mean-square and
all count/primitive/derivative identifications are discharged. -/
theorem actual_zero_remainder_sq_le
    (C total : ℝ) (errS : ℝ → ℝ)
    (d : κ → ℂ) (ν η : κ → ℝ) (errC : ℝ → κ → ℝ)
    (henergy : MeanSquareError C total errS)
    (hmodes : ModeCorrelationError C d ν errC)
    (hν : Function.Injective ν) (hη : ∀ i, 0 < η i)
    (hνsep : ∀ i j, i ≠ j → η i ≤ |ν i - ν j|)
    (c : ι → ℂ) (ω : ι → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hωsep : ∀ i j, i ≠ j → δ ≤ |ω i - ω j|)
    {T : ℝ} (hT : 2 ≤ T) :
    ‖ActualZeroOrdinate.sum T (fun ρ => polynomial c ω ρ.im) -
      ActualZeroOrdinate.sum 0 (fun ρ => polynomial c ω ρ.im) -
      (∫ t in 0..T, (mu t : ℂ) * polynomial c ω t) -
      boundary complexArgument (complexPrimitive C)
        (polynomial c ω) (polynomial (derivativeCoeff c ω) ω) 0 T -
      (∫ t in 0..T, polynomial d ν t * polynomial (secondCoeff c ω) ω t)‖ ^ 2 ≤
    (T * (total - ∑ i, ‖d i‖ ^ 2) + errS T +
      26 * ∑ i, ‖d i‖ ^ 2 / η i + 2 * ∑ i, ‖d i‖ * errC T i) *
        ((T + 26 / δ) * fourthEnergy c ω) := by
  classical
  rw [actual_remainder_eq_residual le_rfl (by linarith) C c ω
    (polynomial d ν) (polynomial_continuous d ν)]
  have hR := actual_primitive_residual_sq_le C total errS d ν η errC
    henergy hmodes hν hη hνsep hT
  simpa only [sub_zero] using residual_second_derivative_pairing_sq_le_uniform
    (by linarith : 0 ≤ T) (complexPrimitive_memLp C 0 T)
    (polynomial_memLp d ν 0 T) hR c ω δ hδ hωsep

end RiemannResearch.Analysis.ActualZeroIntegratedPairing
