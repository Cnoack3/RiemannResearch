import RiemannResearch.RH.DyadicTriadicGramBound
import RiemannResearch.RH.DyadicQuotientAbel
import RiemannResearch.RH.DyadicTailQuotient
import RiemannResearch.RH.DyadicStepLogBound

/-!
# Explicit assembly from the concrete step Gram estimates

Source: user-provided September 10, 2026 dyadic-regularization ledger and
continuation (N24), (N26)--(N30), and Section 7; supports the assembly strategy.

This file closes the assembly between the existing physical Gram reduction and
the actual base and tail regularized families. The arithmetic series convergence,
the concrete off-diagonal Gram/prefix estimates, and the concrete remainder
estimate are hypotheses. The diagonal growth is now proved internally with
D = 3/2 by DyadicStepLogBound; it is no longer an assembly hypothesis.
The specialized endpoints at the end of this module now supply the actual
off-diagonal and prefix providers internally. The actual step average is
unconditionally bounded. The full arithmetic norm obligation still requires
series convergence and the normalization remainder; RH is not established.
-/

namespace RiemannResearch.RH.Pareto

noncomputable section

/-- Explicit squared norm constant obtained from the complete Gram estimates. -/
def dyadicRegularizedGramNormConstant (D A R : ℝ) : ℝ :=
  (‖dyadicQuotientProjection hilbertOne‖ +
    ‖(Real.log 2)⁻¹ • dyadicQuotientProjection (hilbertResidue 2 (by norm_num))‖ +
    Real.sqrt (D + 2 * A) + R) ^ 2

theorem dyadicRegularizedGramNormConstant_nonneg (D A R : ℝ) :
    0 ≤ dyadicRegularizedGramNormConstant D A R := by
  exact sq_nonneg _

/-- Concrete Gram data and the concrete remainder imply the same explicit
constant for the base bound and the full physical `X,d` tail bound. Both actual
series convergence conclusions are retained independently of the norm bounds. -/
theorem dyadicRegularized_explicit_bounds_of_gram_and_error
    (hseries : DyadicRegularizedSeriesSummable)
    (A R : ℝ) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hprefix : ∀ N, RiemannResearch.Analysis.prefixSum a N ≤ A * N)
    (hoff : ∀ j k : ℕ, j < k →
      |inner ℝ (dyadicQuotientProjection
          (hilbertDilation (3 ^ (j + 1)) (by positivity) hilbertOne))
        (dyadicQuotientProjection
          (hilbertDilation (3 ^ (k + 1)) (by positivity) hilbertOne))| ≤ a (k - j))
    (herror : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ‖dyadicRegularizedFamily ε -
        (dyadicQuotientProjection hilbertOne +
          (Real.log 2)⁻¹ • dyadicQuotientProjection (hilbertResidue 2 (by norm_num)) -
          dyadicStepAbelOrbit ε)‖ ≤ R * Real.sqrt ε) :
    DyadicRegularizedSeriesSummable ∧
    DyadicTailRegularizedSeriesSummable ∧
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ‖dyadicRegularizedFamily ε‖ ^ 2 ≤ dyadicRegularizedGramNormConstant (3 / 2) A R) ∧
    (∀ X d (hX : 0 < X) (hXd : X ≤ d),
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        ‖dyadicTailRegularizedFamily X d (Nat.lt_of_lt_of_le hX hXd) ε‖ ^ 2 ≤
          dyadicRegularizedGramNormConstant (3 / 2) A R * d) := by
  have hDA : 0 ≤ (3 / 2 : ℝ) + 2 * A := by positivity
  have hstep : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ‖dyadicStepAbelOrbit ε‖ ≤ Real.sqrt ((3 / 2 : ℝ) + 2 * A) := by
    intro ε hε _
    have hb := dyadicStepAbelOrbit_norm_sq_le_of_gram
      (3 / 2) A (by norm_num) hA a ha dyadicProjectedStep_triadic_diagonal hprefix hoff ε hε
    nlinarith [Real.sq_sqrt hDA, Real.sqrt_nonneg ((3 / 2 : ℝ) + 2 * A),
      norm_nonneg (dyadicStepAbelOrbit ε)]
  have hbase : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ‖dyadicRegularizedFamily ε‖ ^ 2 ≤ dyadicRegularizedGramNormConstant (3 / 2) A R := by
    intro ε hε hεhalf
    apply uniform_norm_sq_of_exact_decomposition
      dyadicRegularizedFamily dyadicStepAbelOrbit
      (fun δ => dyadicRegularizedFamily δ -
        (dyadicQuotientProjection hilbertOne +
          (Real.log 2)⁻¹ • dyadicQuotientProjection (hilbertResidue 2 (by norm_num)) -
          dyadicStepAbelOrbit δ))
      (dyadicQuotientProjection hilbertOne)
      ((Real.log 2)⁻¹ • dyadicQuotientProjection (hilbertResidue 2 (by norm_num)))
      (Real.sqrt ((3 / 2 : ℝ) + 2 * A)) R (Real.sqrt_nonneg _) hR
      (fun δ _ _ => by abel) hstep herror ε hε hεhalf
  refine ⟨hseries, dyadicTailRegularizedSeriesSummable_of_base hseries, hbase, ?_⟩
  intro X d hX hXd ε hε hεhalf
  rw [dyadicTailRegularizedFamily_eq_transfer X d (Nat.lt_of_lt_of_le hX hXd)
    hXd ε ((hseries ε hε hεhalf).2)]
  calc
    _ ≤ (d : ℝ) * ‖dyadicRegularizedFamily ε‖ ^ 2 :=
      dyadicTailTransfer_norm_sq_le X d (Nat.lt_of_lt_of_le hX hXd) _
    _ ≤ (d : ℝ) * dyadicRegularizedGramNormConstant (3 / 2) A R :=
      mul_le_mul_of_nonneg_left (hbase ε hε hεhalf) (Nat.cast_nonneg d)
    _ = dyadicRegularizedGramNormConstant (3 / 2) A R * d := mul_comm _ _

/-- The proposition-level base and full-tail norm obligations follow from the
preceding explicit bounds, with no additional transfer assumptions. -/
theorem dyadicRegularized_norm_obligations_of_gram_and_error
    (hseries : DyadicRegularizedSeriesSummable)
    (A R : ℝ) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hprefix : ∀ N, RiemannResearch.Analysis.prefixSum a N ≤ A * N)
    (hoff : ∀ j k : ℕ, j < k →
      |inner ℝ (dyadicQuotientProjection
          (hilbertDilation (3 ^ (j + 1)) (by positivity) hilbertOne))
        (dyadicQuotientProjection
          (hilbertDilation (3 ^ (k + 1)) (by positivity) hilbertOne))| ≤ a (k - j))
    (herror : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ‖dyadicRegularizedFamily ε -
        (dyadicQuotientProjection hilbertOne +
          (Real.log 2)⁻¹ • dyadicQuotientProjection (hilbertResidue 2 (by norm_num)) -
          dyadicStepAbelOrbit ε)‖ ≤ R * Real.sqrt ε) :
    DyadicRegularizedSeriesSummable ∧ DyadicRegularizedNormBound ∧
    DyadicTailRegularizedSeriesSummable ∧ DyadicTailRegularizedNormBound := by
  obtain ⟨hs, hts, hb, htb⟩ := dyadicRegularized_explicit_bounds_of_gram_and_error
    hseries A R hA hR a ha hprefix hoff herror
  exact ⟨hs,
    ⟨dyadicRegularizedGramNormConstant (3 / 2) A R,
      dyadicRegularizedGramNormConstant_nonneg (3 / 2) A R, hb⟩,
    hts,
    ⟨dyadicRegularizedGramNormConstant (3 / 2) A R,
      dyadicRegularizedGramNormConstant_nonneg (3 / 2) A R, htb⟩⟩

end
end RiemannResearch.RH.Pareto


namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis
noncomputable section

/-- Unconditional uniform bound for the actual damped projected step average.
This is not the product-index Mobius-series bound. -/
theorem dyadicStepAbelOrbit_norm_sq_le_explicit (ε : ℝ) (hε : 0 < ε) :
    ‖dyadicStepAbelOrbit ε‖^2 ≤ (3/2 : ℝ) + 2 * triadicLogGramPrefixConstant := by
  exact dyadicStepAbelOrbit_norm_sq_le_of_gram (3/2) triadicLogGramPrefixConstant
    (by norm_num) triadicLogGramPrefixConstant_nonneg
    triadicLogGramMajorant triadicLogGramMajorant_nonneg
    dyadicProjectedStep_triadic_diagonal triadicLogGramMajorant_prefix_le
    dyadicProjectedStep_triadic_off_diagonal ε hε

/-- With the complete actual step Gram inputs discharged, only the original
arithmetic-series convergence and normalization remainder remain as providers
for the explicit base and all-tail norm bounds. -/
theorem dyadicRegularized_explicit_bounds_of_series_and_error
    (hseries : DyadicRegularizedSeriesSummable)
    (R : ℝ) (hR : 0 ≤ R)
    (herror : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ‖dyadicRegularizedFamily ε -
        (dyadicQuotientProjection hilbertOne +
          (Real.log 2)⁻¹ • dyadicQuotientProjection (hilbertResidue 2 (by norm_num)) -
          dyadicStepAbelOrbit ε)‖ ≤ R * Real.sqrt ε) :
    DyadicRegularizedSeriesSummable ∧ DyadicTailRegularizedSeriesSummable ∧
    (∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ‖dyadicRegularizedFamily ε‖ ^ 2 ≤
        dyadicRegularizedGramNormConstant (3/2) triadicLogGramPrefixConstant R) ∧
    (∀ X d (hX : 0 < X) (hXd : X ≤ d),
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        ‖dyadicTailRegularizedFamily X d (Nat.lt_of_lt_of_le hX hXd) ε‖ ^ 2 ≤
          dyadicRegularizedGramNormConstant (3/2) triadicLogGramPrefixConstant R * d) := by
  exact dyadicRegularized_explicit_bounds_of_gram_and_error hseries
    triadicLogGramPrefixConstant R triadicLogGramPrefixConstant_nonneg hR
    triadicLogGramMajorant triadicLogGramMajorant_nonneg
    triadicLogGramMajorant_prefix_le dyadicProjectedStep_triadic_off_diagonal herror

theorem dyadicRegularized_norm_obligations_of_series_and_error
    (hseries : DyadicRegularizedSeriesSummable)
    (R : ℝ) (hR : 0 ≤ R)
    (herror : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ‖dyadicRegularizedFamily ε -
        (dyadicQuotientProjection hilbertOne +
          (Real.log 2)⁻¹ • dyadicQuotientProjection (hilbertResidue 2 (by norm_num)) -
          dyadicStepAbelOrbit ε)‖ ≤ R * Real.sqrt ε) :
    DyadicRegularizedSeriesSummable ∧ DyadicRegularizedNormBound ∧
      DyadicTailRegularizedSeriesSummable ∧ DyadicTailRegularizedNormBound := by
  exact dyadicRegularized_norm_obligations_of_gram_and_error hseries
    triadicLogGramPrefixConstant R triadicLogGramPrefixConstant_nonneg hR
    triadicLogGramMajorant triadicLogGramMajorant_nonneg
    triadicLogGramMajorant_prefix_le dyadicProjectedStep_triadic_off_diagonal herror

end
end RiemannResearch.RH.Pareto
