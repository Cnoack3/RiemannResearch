import RiemannResearch.RH.DyadicQuotientAbel
import RiemannResearch.RH.DyadicTailQuotient

/-!
# Explicit assembly from the concrete step Gram estimates

Source: user-provided September 10, 2026 dyadic-regularization ledger and
continuation (N24), (N26)--(N30), and Section 7; supports the assembly strategy.

This file closes the assembly between the existing physical Gram reduction and
the actual base and tail regularized families. The arithmetic series convergence,
the concrete Gram estimates, and the concrete remainder estimate are hypotheses.
Consequently these theorems do not assert the unconditional norm obligation or RH.
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
    (D A R : ℝ) (hD : 0 ≤ D) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hdiag : ∀ j : ℕ,
      ‖dyadicQuotientProjection
        (hilbertDilation (3 ^ (j + 1)) (by positivity) hilbertOne)‖ ^ 2 ≤
          D * ((j : ℝ) + 1))
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
      ‖dyadicRegularizedFamily ε‖ ^ 2 ≤ dyadicRegularizedGramNormConstant D A R) ∧
    (∀ X d (hX : 0 < X) (hXd : X ≤ d),
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
        ‖dyadicTailRegularizedFamily X d (Nat.lt_of_lt_of_le hX hXd) ε‖ ^ 2 ≤
          dyadicRegularizedGramNormConstant D A R * d) := by
  have hDA : 0 ≤ D + 2 * A := by positivity
  have hstep : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ‖dyadicStepAbelOrbit ε‖ ≤ Real.sqrt (D + 2 * A) := by
    intro ε hε _
    have hb := dyadicStepAbelOrbit_norm_sq_le_of_gram
      D A hD hA a ha hdiag hprefix hoff ε hε
    nlinarith [Real.sq_sqrt hDA, Real.sqrt_nonneg (D + 2 * A),
      norm_nonneg (dyadicStepAbelOrbit ε)]
  have hbase : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ‖dyadicRegularizedFamily ε‖ ^ 2 ≤ dyadicRegularizedGramNormConstant D A R := by
    intro ε hε hεhalf
    apply uniform_norm_sq_of_exact_decomposition
      dyadicRegularizedFamily dyadicStepAbelOrbit
      (fun δ => dyadicRegularizedFamily δ -
        (dyadicQuotientProjection hilbertOne +
          (Real.log 2)⁻¹ • dyadicQuotientProjection (hilbertResidue 2 (by norm_num)) -
          dyadicStepAbelOrbit δ))
      (dyadicQuotientProjection hilbertOne)
      ((Real.log 2)⁻¹ • dyadicQuotientProjection (hilbertResidue 2 (by norm_num)))
      (Real.sqrt (D + 2 * A)) R (Real.sqrt_nonneg _) hR
      (fun δ _ _ => by abel) hstep herror ε hε hεhalf
  refine ⟨hseries, dyadicTailRegularizedSeriesSummable_of_base hseries, hbase, ?_⟩
  intro X d hX hXd ε hε hεhalf
  rw [dyadicTailRegularizedFamily_eq_transfer X d (Nat.lt_of_lt_of_le hX hXd)
    hXd ε ((hseries ε hε hεhalf).2)]
  calc
    _ ≤ (d : ℝ) * ‖dyadicRegularizedFamily ε‖ ^ 2 :=
      dyadicTailTransfer_norm_sq_le X d (Nat.lt_of_lt_of_le hX hXd) _
    _ ≤ (d : ℝ) * dyadicRegularizedGramNormConstant D A R :=
      mul_le_mul_of_nonneg_left (hbase ε hε hεhalf) (Nat.cast_nonneg d)
    _ = dyadicRegularizedGramNormConstant D A R * d := mul_comm _ _

/-- The proposition-level base and full-tail norm obligations follow from the
preceding explicit bounds, with no additional transfer assumptions. -/
theorem dyadicRegularized_norm_obligations_of_gram_and_error
    (hseries : DyadicRegularizedSeriesSummable)
    (D A R : ℝ) (hD : 0 ≤ D) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hdiag : ∀ j : ℕ,
      ‖dyadicQuotientProjection
        (hilbertDilation (3 ^ (j + 1)) (by positivity) hilbertOne)‖ ^ 2 ≤
          D * ((j : ℝ) + 1))
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
    hseries D A R hD hA hR a ha hdiag hprefix hoff herror
  exact ⟨hs,
    ⟨dyadicRegularizedGramNormConstant D A R,
      dyadicRegularizedGramNormConstant_nonneg D A R, hb⟩,
    hts,
    ⟨dyadicRegularizedGramNormConstant D A R,
      dyadicRegularizedGramNormConstant_nonneg D A R, htb⟩⟩

end
end RiemannResearch.RH.Pareto
