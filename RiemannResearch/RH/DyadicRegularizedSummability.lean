import RiemannResearch.RH.DyadicResidueDepthGrowth
import RiemannResearch.RH.DyadicRegularizedResolvent
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Actual arithmetic product-series convergence at every positive damping

Source: user-provided DyadicResidueKernelVerification20260910(1).md,
September 10, 2026, convergence target and ordinary depth-bound argument.
The proved dyadic depth bound implies subpower growth. This is used only
for an absolute norm majorant, retaining every term of the actual signed
Möbius product series. No normalization-remainder or uniform norm estimate
is inferred from fixed-damping convergence.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Every positive power majorizes the actual projected residue growth.
The constant can depend on the exponent; this is not a uniform damping bound. -/
theorem dyadicQuotientProjection_triadicResidue_subpower
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (hm : 0 < m),
      ‖dyadicQuotientProjection
        (hilbertDilation m hm (hilbertResidue 3 (by norm_num)))‖ ≤
        C * (m : ℝ) ^ δ := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let R := ‖hilbertResidue 3 (by norm_num)‖
  let C := 4 * (δ * Real.log 2)⁻¹ + 4 + R
  refine ⟨C, by dsimp [C, R]; positivity, ?_⟩
  intro m hm
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast hm
  have hm1 : 1 ≤ (m : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hm)
  have hupper : m ≤ 2 ^ (Nat.log 2 m + 1) :=
    (Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) m).le
  have hd := dyadicQuotientProjection_triadicResidue_norm_le_depth
    (Nat.log 2 m + 1) m hm hupper
  have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs1 : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hd' : ‖dyadicQuotientProjection
      (hilbertDilation m hm (hilbertResidue 3 (by norm_num)))‖ ≤
      4 * ((Nat.log 2 m : ℝ) + 1) + R := by
    have ht : 4 * ((Nat.log 2 m + 1 : ℕ) : ℝ) / Real.sqrt 2 ≤
        4 * ((Nat.log 2 m + 1 : ℕ) : ℝ) := by
      apply (div_le_iff₀ hs2).2
      have hn : 0 ≤ ((Nat.log 2 m + 1 : ℕ) : ℝ) := by positivity
      nlinarith
    dsimp [R]
    push_cast at hd ht
    exact hd.trans (add_le_add ht le_rfl)
  have hp : (2 : ℝ) ^ Nat.log 2 m ≤ (m : ℝ) := by
    exact_mod_cast Nat.pow_log_le_self 2 hm.ne'
  have hlog : (Nat.log 2 m : ℝ) * Real.log 2 ≤ Real.log m := by
    have h := Real.log_le_log (by positivity : 0 < (2 : ℝ) ^ Nat.log 2 m) hp
    simpa only [Real.log_pow] using h
  have hlogpow := hlog.trans (Real.log_le_rpow_div hm0.le hδ)
  have hlogpow' : (Nat.log 2 m : ℝ) ≤ (m : ℝ) ^ δ / (δ * Real.log 2) := by
    have h := (le_div_iff₀ hl2).2 hlogpow
    simpa only [div_div] using h
  have hpower : 1 ≤ (m : ℝ) ^ δ := Real.one_le_rpow hm1 hδ.le
  have hmain := mul_le_mul_of_nonneg_left hlogpow' (by norm_num : (0 : ℝ) ≤ 4)
  have hconst := mul_le_mul_of_nonneg_left hpower
    (show 0 ≤ 4 + R by dsimp [R]; positivity)
  dsimp [C]
  simp only [div_eq_mul_inv] at hmain
  nlinarith [norm_nonneg (hilbertResidue 3 (by norm_num))]

private theorem dyadicRegularizationCoefficient_abs_le
    (ε : ℝ) (m j : ℕ) :
    |dyadicRegularizationCoefficient ε m j| ≤
      (m + 1 : ℝ) ^ (-(1 + ε)) * triadicDampingRatio ε ^ j := by
  have hm : 0 < (m + 1 : ℝ) := by positivity
  have hμ : |(ArithmeticFunction.moebius (m + 1) : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := m + 1))
  have hd : 0 < (m + 1 : ℝ) ^ (1 + ε) := Real.rpow_pos_of_pos hm _
  have hr : 0 ≤ triadicDampingRatio ε ^ j :=
    pow_nonneg (triadicDampingRatio_pos ε).le _
  unfold dyadicRegularizationCoefficient
  rw [abs_mul, abs_div, abs_of_pos hd, abs_of_nonneg hr]
  have h := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right hμ hd.le) hr
  simpa only [one_div, Real.rpow_neg hm.le] using h

private theorem regularization_power_majorant_identity
    (ε C : ℝ) (m j : ℕ) :
    ((m + 1 : ℝ) ^ (-(1 + ε)) * triadicDampingRatio ε ^ j) *
        (C * ((((m + 1) * 3 ^ j : ℕ) : ℝ) ^ (ε / 2))) =
      C * ((m + 1 : ℝ) ^ (-(1 + ε / 2)) *
        triadicDampingRatio (ε / 2) ^ j) := by
  have hm : 0 < (m + 1 : ℝ) := by positivity
  have h3 : 0 < (3 : ℝ) := by norm_num
  have hp : ((3 : ℝ) ^ j) ^ (ε / 2) = ((3 : ℝ) ^ (ε / 2)) ^ j := by
    rw [← Real.rpow_natCast_mul h3.le, ← Real.rpow_mul_natCast h3.le]
    congr 1
    ring
  have hmcombine : (m + 1 : ℝ) ^ (-(1 + ε)) * (m + 1 : ℝ) ^ (ε / 2) =
      (m + 1 : ℝ) ^ (-(1 + ε / 2)) := by
    rw [← Real.rpow_add hm]
    congr 1
    ring
  have h3combine : triadicDampingRatio ε ^ j * ((3 : ℝ) ^ (ε / 2)) ^ j =
      triadicDampingRatio (ε / 2) ^ j := by
    rw [← mul_pow]
    unfold triadicDampingRatio
    rw [← Real.rpow_add h3]
    congr 2
    ring
  push_cast
  rw [Real.mul_rpow hm.le (by positivity), hp]
  calc
    _ = C * (((m + 1 : ℝ) ^ (-(1 + ε)) * (m + 1 : ℝ) ^ (ε / 2)) *
      (triadicDampingRatio ε ^ j * ((3 : ℝ) ^ (ε / 2)) ^ j)) := by ring
    _ = _ := by rw [hmcombine, h3combine]

/-- The norm series of the genuine product-index regularization converges
at every positive damping, without Möbius cancellation assumptions. -/
theorem dyadicRegularizedTerm_norm_summable {ε : ℝ} (hε : 0 < ε) :
    Summable (fun p : ℕ × ℕ => ‖dyadicRegularizedTerm ε p‖) := by
  have hh : 0 < ε / 2 := half_pos hε
  obtain ⟨C, hC, hgrowth⟩ := dyadicQuotientProjection_triadicResidue_subpower hh
  have hn := regularizationZetaSeries_summable hh
  have hj := triadicDampingRatio_pow_summable hh
  have hprod : Summable (fun p : ℕ × ℕ =>
      (p.1 + 1 : ℝ) ^ (-(1 + ε / 2)) * triadicDampingRatio (ε / 2) ^ p.2) :=
    summable_mul_of_summable_norm hn.norm hj.norm
  have hmajor := hprod.mul_left C
  apply Summable.of_nonneg_of_le (fun p => norm_nonneg _) _ hmajor
  rintro ⟨m, j⟩
  have hcoef := dyadicRegularizationCoefficient_abs_le ε m j
  have hvec := hgrowth ((m + 1) * 3 ^ j) (by positivity)
  have hr : 0 ≤ triadicDampingRatio ε := (triadicDampingRatio_pos ε).le
  rw [dyadicRegularizedTerm, norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ ((m + 1 : ℝ) ^ (-(1 + ε)) * triadicDampingRatio ε ^ j) *
        (C * ((((m + 1) * 3 ^ j : ℕ) : ℝ) ^ (ε / 2))) :=
      mul_le_mul hcoef hvec (norm_nonneg _) (by positivity)
    _ = _ := regularization_power_majorant_identity ε C m j

/-- Unconditional actual Hilbert-valued convergence at positive damping. -/
theorem dyadicRegularizedTerm_summable {ε : ℝ} (hε : 0 < ε) :
    Summable (dyadicRegularizedTerm ε) :=
  (dyadicRegularizedTerm_norm_summable hε).of_norm

/-- The complete previously named scalar-plus-vector series obligation. -/
theorem dyadicRegularizedSeriesSummable_proved : DyadicRegularizedSeriesSummable := by
  intro ε hε _
  exact ⟨regularizationZetaSeries_summable hε, dyadicRegularizedTerm_summable hε⟩

/-- The genuine arithmetic columns are summable at every positive damping. -/
theorem dyadicRegularizedColumn_summable_of_pos {ε : ℝ} (hε : 0 < ε) :
    Summable (dyadicRegularizedColumn ε) :=
  dyadicRegularizedColumn_summable ε (dyadicRegularizedTerm_summable hε)

/-- Actual arithmetic regrouping, now with its convergence premise supplied. -/
theorem dyadicRegularizedFamily_eq_columns_of_pos {ε : ℝ} (hε : 0 < ε) :
    dyadicRegularizedFamily ε =
      dyadicRegularizationNormalization ε • ∑' j : ℕ, dyadicRegularizedColumn ε j :=
  dyadicRegularizedFamily_eq_columns ε (dyadicRegularizedTerm_summable hε)

/-- The exact infinite resolvent for the actual arithmetic family.
Its head is not identified with a normalization remainder. -/
theorem dyadicRegularizedFamily_resolvent_of_pos {ε : ℝ} (hε : 0 < ε) :
    dyadicRegularizedFamily ε -
        triadicDampingRatio ε •
          dyadicQuotientDilation 3 (by norm_num) (dyadicRegularizedFamily ε) =
      dyadicRegularizationNormalization ε • dyadicRegularizedColumn ε 0 :=
  dyadicRegularizedFamily_resolvent ε (dyadicRegularizedTerm_summable hε)

end
end RiemannResearch.RH.Pareto
