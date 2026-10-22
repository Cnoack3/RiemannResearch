import RiemannResearch.RH.LogarithmicCorrectionTarget
import RiemannResearch.Analysis.ResidualGainProduct
/-!
# Exact dyadic residual endpoints and flexible normalized costs

Source: user-provided RH_Dyadic_Two_Seed_Pareto_Residual_Gain_Work_Handoff_2026-09-18(1).md, Sections 7--10 (statements and reduction strategy). The actual budget residual and its existing Mellin-to-RH bridge are used throughout. All arithmetic gain or cost providers remain explicit hypotheses. No unconditional RH assertion or reverse RH-to-density provider is introduced.
-/

open Filter
open scoped Topology BigOperators
noncomputable section
namespace RiemannResearch.RH.Pareto.CoupledResidual
open RiemannResearch.Analysis.ResidualGain

def dyadicRelativeGain (J n : ℕ) : ℝ :=
  gain (2^(J+n)) / distance (2^(J+n))

theorem dyadicRelativeGain_nonneg (J n : ℕ) :
    0 ≤ dyadicRelativeGain J n :=
  div_nonneg (gain_nonneg _) (distance_pos _).le

theorem dyadicRelativeGain_lt_one (J n : ℕ) :
    dyadicRelativeGain J n < 1 := by
  unfold dyadicRelativeGain gain
  apply (div_lt_one (distance_pos _)).mpr
  linarith [distance_pos (2*2^(J+n))]

theorem dyadic_distance_recurrence (J n : ℕ) :
    distance (2^(J+(n+1))) =
      distance (2^(J+n)) * (1-dyadicRelativeGain J n) := by
  have hp : (2^(J+(n+1)) : ℕ) = 2*2^(J+n) := by
    rw [show J+(n+1) = (J+n)+1 by omega, pow_succ, Nat.mul_comm]
  rw [hp]
  unfold dyadicRelativeGain gain
  field_simp [ne_of_gt (distance_pos (2^(J+n)))]
  ring

theorem dyadic_distance_product (J N : ℕ) :
    distance (2^(J+N)) = distance (2^J) *
      ∏ n ∈ Finset.range N, (1-dyadicRelativeGain J n) := by
  simpa only [Nat.add_zero, survivalProduct] using
    recurrence_eq_mul_product (d := fun n => distance (2^(J+n)))
      (r := dyadicRelativeGain J) (dyadic_distance_recurrence J) N

theorem dyadic_distance_tendsto_zero_iff (J : ℕ) :
    Tendsto (fun n => distance (2^(J+n))) atTop (𝓝 0) ↔
      ¬ Summable (dyadicRelativeGain J) :=
  residual_tendsto_zero_iff_not_summable
    (distance_pos _) (dyadicRelativeGain_nonneg J)
    (dyadicRelativeGain_lt_one J) (dyadic_distance_recurrence J)

theorem riemannHypothesis_of_dyadic_gain_divergence (J : ℕ)
    (h : ¬ Summable (dyadicRelativeGain J)) : RiemannHypothesis :=
  riemannHypothesis_of_distance_convergence (fun n => 2^(J+n))
    ((dyadic_distance_tendsto_zero_iff J).mpr h)


theorem dyadic_distance_limit_of_summable (J : ℕ)
    (h : Summable (dyadicRelativeGain J)) :
    Tendsto (fun n => distance (2^(J+n))) atTop
      (𝓝 (distance (2^J) *
        Real.exp (∑' n, Real.log (1-dyadicRelativeGain J n)))) := by
  have hp := survivalProduct_tendsto_exp_log_of_summable
    (dyadicRelativeGain_lt_one J) h
  have hh := (tendsto_const_nhds.mul hp :
    Tendsto (fun n => distance (2^J) * survivalProduct (dyadicRelativeGain J) n)
      atTop (𝓝 (distance (2^J) *
        Real.exp (∑' n, Real.log (1-dyadicRelativeGain J n)))))
  simpa only [survivalProduct, ← dyadic_distance_product] using hh

theorem dyadic_surviving_energy_pos (J : ℕ) :
    0 < distance (2^J) *
      Real.exp (∑' n, Real.log (1-dyadicRelativeGain J n)) :=
  mul_pos (distance_pos _) (Real.exp_pos _)

open FiniteTwoSeedCompletion RamanujanLaguerre
theorem normalized_dyadic_cost_iff (J n : ℕ) (B : ℝ) (hB : 0 < B) :
    (∃ w : ThresholdHilbert, w ∈ budgetHilbert (2*2^(J+n)) ∧
      w ∈ (budgetHilbert (2^(J+n)))ᗮ ∧
      inner ℝ (error (2^(J+n))) w = distance (2^(J+n)) ∧
      ‖w‖^2 ≤ B*distance (2^(J+n))) ↔
      1/B ≤ dyadicRelativeGain J n := by
  rw [normalized_cost_iff_gain _ B hB]
  unfold dyadicRelativeGain
  rw [div_le_div_iff₀ hB (distance_pos _)]
  simp only [one_mul, mul_comm]

/-- A variable or sparse sufficient gain schedule; its arithmetic witnesses
and nonsummability are substantive hypotheses, not supplied providers. -/
theorem riemannHypothesis_of_dyadic_gain_schedule (J : ℕ) (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n) (hdiv : ¬ Summable a)
    (hgain : ∀ n, a n ≤ dyadicRelativeGain J n) : RiemannHypothesis := by
  apply riemannHypothesis_of_dyadic_gain_divergence J
  intro hs
  exact hdiv (Summable.of_nonneg_of_le ha hgain hs)

/-- Legal normalized corrections suffice whenever their reciprocal relative
costs have divergent sum. No fixed logarithmic rate is required. -/
theorem riemannHypothesis_of_dyadic_cost_schedule (J : ℕ) (B : ℕ → ℝ)
    (hB : ∀ n, 0 < B n) (hdiv : ¬ Summable (fun n => 1/B n))
    (hw : ∀ n, ∃ w : ThresholdHilbert,
      w ∈ budgetHilbert (2*2^(J+n)) ∧
      w ∈ (budgetHilbert (2^(J+n)))ᗮ ∧
      inner ℝ (error (2^(J+n))) w = distance (2^(J+n)) ∧
      ‖w‖^2 ≤ B n*distance (2^(J+n))) : RiemannHypothesis := by
  apply riemannHypothesis_of_dyadic_gain_schedule J (fun n => 1/B n)
    (fun n => (one_div_pos.mpr (hB n)).le) hdiv
  intro n
  exact (normalized_dyadic_cost_iff J n (B n) (hB n)).mp (hw n)

/-- The literal dyadic target in the 2026-09-18 handoff.
This is an open proposition, not an axiom or a proved estimate. -/
def DyadicLogarithmicGainBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ J : ℕ, ∀ k : ℕ, J ≤ k →
    c/(((k : ℝ)+1)*Real.log 2)*distance (2^k) ≤ gain (2^k)

theorem riemannHypothesis_of_dyadicLogarithmicGainBound
    (h : DyadicLogarithmicGainBound) : RiemannHypothesis := by
  obtain ⟨c, hc, J, h⟩ := h
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let a : ℝ := c/(((J : ℝ)+1)*Real.log 2)
  have ha : 0 < a := by dsimp [a]; positivity
  apply riemannHypothesis_of_dyadic_loss J a ha
  intro n
  have hden : (((J+n : ℕ) : ℝ)+1)*Real.log 2 ≤
      (((J : ℝ)+1)*Real.log 2)*((n : ℝ)+1) := by
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg J : (0:ℝ) ≤ J)
      (Nat.cast_nonneg n : (0:ℝ) ≤ n),
      mul_nonneg hl.le (mul_nonneg (Nat.cast_nonneg J : (0:ℝ) ≤ J)
        (Nat.cast_nonneg n : (0:ℝ) ≤ n))]
  have hcoeff : a/((n : ℝ)+1) ≤
      c/((((J+n : ℕ) : ℝ)+1)*Real.log 2) := by
    dsimp only [a]
    rw [div_div]
    exact div_le_div_of_nonneg_left hc.le (by positivity) hden
  exact (mul_le_mul_of_nonneg_right hcoeff (distance_pos _).le).trans
    (h (J+n) (Nat.le_add_right J n))

end RiemannResearch.RH.Pareto.CoupledResidual
