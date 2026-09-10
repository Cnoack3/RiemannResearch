import RiemannResearch.RH.DyadicRegularizedGramAssembly
import RiemannResearch.RH.DyadicRegularizedSummability

/-!
# The remaining normalization-remainder obligation

Source: user-provided DyadicResidueKernelVerification20260910(1).md,
September 10, 2026, normalization-remainder target; the weaker bounded-error
reduction follows directly from the established exact decomposition.

Actual product-series convergence is now supplied by
`dyadicRegularizedSeriesSummable_proved`. The concrete diagonal, off-diagonal,
and prefix Gram inputs have already been proved in the imported assembly.
Consequently the endpoints here assume only the displayed estimate for the
actual normalization remainder, with one nonnegative constant R independent
of ε. They retain both the base and full physical X,d tail conclusions.

The normalization-remainder estimate remains a hypothesis. These conditional
endpoints do not prove the uniform vanishing-damping bound or RH.
-/

namespace RiemannResearch.RH.Pareto

open RiemannResearch.Analysis

noncomputable section

/-- The complete physical tail-series obligation is unconditional. -/
theorem dyadicTailRegularizedSeriesSummable_proved :
    DyadicTailRegularizedSeriesSummable :=
  dyadicTailRegularizedSeriesSummable_of_base dyadicRegularizedSeriesSummable_proved

/-- The actual normalization remainder is the sole remaining analytic provider
for the explicit base and all-tail squared norm bounds. -/
theorem dyadicRegularized_explicit_bounds_of_error
    (R : ℝ) (hR : 0 ≤ R)
    (herror : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ‖dyadicRegularizedFamily ε -
        (dyadicQuotientProjection hilbertOne +
          (Real.log 2)⁻¹ • dyadicQuotientProjection (hilbertResidue 2 (by norm_num)) -
          dyadicStepAbelOrbit ε)‖ ≤ R * Real.sqrt ε) :
    DyadicRegularizedSeriesSummable ∧ DyadicTailRegularizedSeriesSummable ∧
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ‖dyadicRegularizedFamily ε‖ ^ 2 ≤
        dyadicRegularizedGramNormConstant (3 / 2) triadicLogGramPrefixConstant R) ∧
    (∀ X d (hX : 0 < X) (hXd : X ≤ d),
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        ‖dyadicTailRegularizedFamily X d (Nat.lt_of_lt_of_le hX hXd) ε‖ ^ 2 ≤
          dyadicRegularizedGramNormConstant (3 / 2) triadicLogGramPrefixConstant R * d) := by
  exact dyadicRegularized_explicit_bounds_of_series_and_error
    dyadicRegularizedSeriesSummable_proved R hR herror

/-- Both norm obligations follow from only the actual normalization error.
There is no remaining supplied series or Gram estimate. -/
theorem dyadicRegularized_norm_obligations_of_error
    (R : ℝ) (hR : 0 ≤ R)
    (herror : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ‖dyadicRegularizedFamily ε -
        (dyadicQuotientProjection hilbertOne +
          (Real.log 2)⁻¹ • dyadicQuotientProjection (hilbertResidue 2 (by norm_num)) -
          dyadicStepAbelOrbit ε)‖ ≤ R * Real.sqrt ε) :
    DyadicRegularizedSeriesSummable ∧ DyadicRegularizedNormBound ∧
      DyadicTailRegularizedSeriesSummable ∧ DyadicTailRegularizedNormBound := by
  exact dyadicRegularized_norm_obligations_of_series_and_error
    dyadicRegularizedSeriesSummable_proved R hR herror

/-- For the uniform norm bound alone, uniform boundedness of the actual
normalization remainder suffices; no decay rate in ε is needed. -/
theorem dyadicRegularized_norm_sq_le_of_bounded_error
    (R : ℝ) (hR : 0 ≤ R)
    (herror : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ‖dyadicRegularizedFamily ε -
        (dyadicQuotientProjection hilbertOne +
          (Real.log 2)⁻¹ • dyadicQuotientProjection (hilbertResidue 2 (by norm_num)) -
          dyadicStepAbelOrbit ε)‖ ≤ R)
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    ‖dyadicRegularizedFamily ε‖ ^ 2 ≤
      dyadicRegularizedGramNormConstant (3 / 2) triadicLogGramPrefixConstant R := by
  let u := dyadicQuotientProjection hilbertOne
  let v := (Real.log 2)⁻¹ • dyadicQuotientProjection (hilbertResidue 2 (by norm_num))
  let A := Real.sqrt ((3 / 2 : ℝ) + 2 * triadicLogGramPrefixConstant)
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  have hrad : 0 ≤ (3 / 2 : ℝ) + 2 * triadicLogGramPrefixConstant := by
    have hp := triadicLogGramPrefixConstant_nonneg
    positivity
  have hstep : ‖dyadicStepAbelOrbit ε‖ ≤ A := by
    have hs := dyadicStepAbelOrbit_norm_sq_le_explicit ε hε
    have ha : A ^ 2 = (3 / 2 : ℝ) + 2 * triadicLogGramPrefixConstant :=
      Real.sq_sqrt hrad
    nlinarith [norm_nonneg (dyadicStepAbelOrbit ε)]
  have herr : ‖dyadicRegularizedFamily ε - (u + v - dyadicStepAbelOrbit ε)‖ ≤ R :=
    herror ε hε hεhalf
  have hrecon : dyadicRegularizedFamily ε =
      (u + v - dyadicStepAbelOrbit ε) +
        (dyadicRegularizedFamily ε - (u + v - dyadicStepAbelOrbit ε)) := by abel
  have hnorm : ‖dyadicRegularizedFamily ε‖ ≤ ‖u‖ + ‖v‖ + A + R := by
    calc
      _ = ‖(u + v - dyadicStepAbelOrbit ε) +
          (dyadicRegularizedFamily ε - (u + v - dyadicStepAbelOrbit ε))‖ :=
        congrArg (fun x => ‖x‖) hrecon
      _ ≤ ‖u + v - dyadicStepAbelOrbit ε‖ +
          ‖dyadicRegularizedFamily ε - (u + v - dyadicStepAbelOrbit ε)‖ := norm_add_le _ _
      _ ≤ ‖u + v‖ + ‖dyadicStepAbelOrbit ε‖ +
          ‖dyadicRegularizedFamily ε - (u + v - dyadicStepAbelOrbit ε)‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ ‖u‖ + ‖v‖ + A + R := by linarith [norm_add_le u v]
  change ‖dyadicRegularizedFamily ε‖ ^ 2 ≤ (‖u‖ + ‖v‖ + A + R) ^ 2
  simpa only [pow_two] using
    mul_le_mul hnorm hnorm (norm_nonneg _) (by positivity)

/-- The weaker bounded-remainder obligation already closes both the base and
all physical tail norm bounds, with actual convergence supplied internally. -/
theorem dyadicRegularized_norm_obligations_of_bounded_error
    (R : ℝ) (hR : 0 ≤ R)
    (herror : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ‖dyadicRegularizedFamily ε -
        (dyadicQuotientProjection hilbertOne +
          (Real.log 2)⁻¹ • dyadicQuotientProjection (hilbertResidue 2 (by norm_num)) -
          dyadicStepAbelOrbit ε)‖ ≤ R) :
    DyadicRegularizedSeriesSummable ∧ DyadicRegularizedNormBound ∧
      DyadicTailRegularizedSeriesSummable ∧ DyadicTailRegularizedNormBound := by
  let C := dyadicRegularizedGramNormConstant (3 / 2) triadicLogGramPrefixConstant R
  have hC : 0 ≤ C := dyadicRegularizedGramNormConstant_nonneg _ _ _
  have hbase : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → ‖dyadicRegularizedFamily ε‖ ^ 2 ≤ C :=
    dyadicRegularized_norm_sq_le_of_bounded_error R hR herror
  refine ⟨dyadicRegularizedSeriesSummable_proved, ⟨C, hC, hbase⟩,
    dyadicTailRegularizedSeriesSummable_proved, C, hC, ?_⟩
  intro X d hX hXd ε hε hεhalf
  rw [dyadicTailRegularizedFamily_eq_transfer X d (Nat.lt_of_lt_of_le hX hXd)
    hXd ε ((dyadicRegularizedSeriesSummable_proved ε hε hεhalf).2)]
  calc
    _ ≤ (d : ℝ) * ‖dyadicRegularizedFamily ε‖ ^ 2 :=
      dyadicTailTransfer_norm_sq_le X d (Nat.lt_of_lt_of_le hX hXd) _
    _ ≤ (d : ℝ) * C :=
      mul_le_mul_of_nonneg_left (hbase ε hε hεhalf) (Nat.cast_nonneg d)
    _ = C * d := mul_comm _ _

end
end RiemannResearch.RH.Pareto
