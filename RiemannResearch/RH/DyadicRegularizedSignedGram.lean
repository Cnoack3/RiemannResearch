import RiemannResearch.Analysis.AbsolutelySummableGram
import RiemannResearch.RH.DyadicRegularizedSummability

/-!
# Exact signed Gram energy of the actual arithmetic family

Source: user-provided DyadicAllScaleConvergenceVerification20260910(2).md,
September 10, 2026, continuation of the remaining uniform norm obligation.
Actual absolute convergence discharges every series premise below. The complete
product-index Gram sum retains all Möbius signs and all mixed pairings.
No uniform vanishing-damping bound is asserted.
-/

namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis
noncomputable section

/-- The signed Gram entry of the genuine arithmetic terms. -/
def dyadicRegularizedGram (ε : ℝ) (p q : ℕ × ℕ) : ℝ :=
  inner ℝ (dyadicRegularizedTerm ε p) (dyadicRegularizedTerm ε q)

theorem dyadicRegularizedGram_eq_signed (ε : ℝ) (p q : ℕ × ℕ) :
    dyadicRegularizedGram ε p q =
      dyadicRegularizationCoefficient ε p.1 p.2 *
      dyadicRegularizationCoefficient ε q.1 q.2 *
      inner ℝ
        (dyadicQuotientProjection (hilbertDilation ((p.1 + 1) * 3 ^ p.2)
          (by positivity) (hilbertResidue 3 (by norm_num))))
        (dyadicQuotientProjection (hilbertDilation ((q.1 + 1) * 3 ^ q.2)
          (by positivity) (hilbertResidue 3 (by norm_num)))) := by
  simp only [dyadicRegularizedGram, dyadicRegularizedTerm,
    real_inner_smul_left, real_inner_smul_right]
  ring

/-- Absolute convergence of every signed mixed pairing at positive damping. -/
theorem dyadicRegularizedGram_abs_summable {ε : ℝ} (hε : 0 < ε) :
    Summable (fun z : (ℕ × ℕ) × (ℕ × ℕ) =>
      |dyadicRegularizedGram ε z.1 z.2|) := by
  simpa only [dyadicRegularizedGram, Real.norm_eq_abs] using
    summable_norm_inner_product_of_summable_norm
      (dyadicRegularizedTerm ε) (dyadicRegularizedTerm ε)
      (dyadicRegularizedTerm_norm_summable hε)
      (dyadicRegularizedTerm_norm_summable hε)

/-- The complete norm is the signed double Gram series, not its diagonal. -/
theorem dyadicRegularizedFamily_norm_sq_eq_signed_gram {ε : ℝ} (hε : 0 < ε) :
    ‖dyadicRegularizedFamily ε‖ ^ 2 =
      dyadicRegularizationNormalization ε ^ 2 *
        ∑' z : (ℕ × ℕ) × (ℕ × ℕ), dyadicRegularizedGram ε z.1 z.2 := by
  rw [dyadicRegularizedFamily, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    norm_sq_tsum_eq_tsum_gram _ (dyadicRegularizedTerm_norm_summable hε)]
  rfl

theorem dyadicRegularizedTerm_pairing_abs_summable {ε : ℝ} (hε : 0 < ε)
    (g : ThresholdHilbert) :
    Summable (fun p : ℕ × ℕ => |inner ℝ (dyadicRegularizedTerm ε p) g|) := by
  have hm := (dyadicRegularizedTerm_norm_summable hε).mul_right ‖g‖
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) _ hm
  intro p
  simpa only [Real.norm_eq_abs] using
    norm_inner_le_norm (𝕜 := ℝ) (dyadicRegularizedTerm ε p) g

/-- A physical pairing may pass through the actual convergent series. -/
theorem dyadicRegularizedFamily_inner_eq_series {ε : ℝ} (hε : 0 < ε)
    (g : ThresholdHilbert) :
    inner ℝ (dyadicRegularizedFamily ε) g =
      dyadicRegularizationNormalization ε *
        ∑' p : ℕ × ℕ, inner ℝ (dyadicRegularizedTerm ε p) g := by
  rw [dyadicRegularizedFamily, real_inner_smul_left]
  congr 1
  rw [real_inner_comm]
  have hm := (innerSL ℝ g).map_tsum (dyadicRegularizedTerm_summable hε)
  exact hm.trans (tsum_congr (fun p => real_inner_comm (dyadicRegularizedTerm ε p) g))

/-- Exact squared error against any physical comparison vector. The cross
series is retained with its sign, including for the proposed remainder. -/
theorem dyadicRegularizedFamily_error_sq_eq_signed_gram {ε : ℝ} (hε : 0 < ε)
    (g : ThresholdHilbert) :
    ‖dyadicRegularizedFamily ε - g‖ ^ 2 =
      dyadicRegularizationNormalization ε ^ 2 *
        (∑' z : (ℕ × ℕ) × (ℕ × ℕ), dyadicRegularizedGram ε z.1 z.2) -
      2 * dyadicRegularizationNormalization ε *
        (∑' p : ℕ × ℕ, inner ℝ (dyadicRegularizedTerm ε p) g) + ‖g‖ ^ 2 := by
  have he : ‖dyadicRegularizedFamily ε - g‖ ^ 2 =
      ‖dyadicRegularizedFamily ε‖ ^ 2 -
        2 * inner ℝ (dyadicRegularizedFamily ε) g + ‖g‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq]
    rw [real_inner_comm g (dyadicRegularizedFamily ε)]
    ring
  rw [he, dyadicRegularizedFamily_norm_sq_eq_signed_gram hε,
    dyadicRegularizedFamily_inner_eq_series hε]
  ring

end
end RiemannResearch.RH.Pareto
