import RiemannResearch.RH.CoupledResidualAnalyticTargets
import RiemannResearch.RH.LogarithmicCorrectionTarget
import RiemannResearch.RH.DyadicResidualConstraints

/-!
# The conditional Burnol envelope feeds the checked dyadic obstruction

Source: user-provided `RH_Coupled_Residual_Corrections_2026-09-16.md`,
Section 7. This module transfers the explicitly hypothesized actual
distance lower envelope to the dyadic envelope and the sharp constant
restriction. It does not prove or postulate Burnol's external analytic
theorem or its comparison with the Pareto approximation spaces.
-/
noncomputable section
namespace RiemannResearch.RH.Pareto.CoupledResidual
open FiniteTwoSeedCompletion RamanujanLaguerre AdjacentPacket

private theorem index_le_two_pow (k : ℕ) : k ≤ 2^k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    have hp : 0 < 2^k := pow_pos (by omega) k
    omega

/-- The Burnol-type envelope implies the precise scalar input to the
sharp dyadic theorem; its positive constant is divided by `log 3`. -/
theorem dyadicEnvelope_of_burnolEnvelope
    (h : BurnolDistanceLowerEnvelope) : DyadicDistanceLowerEnvelope := by
  obtain ⟨c, hc, M₀, hlower⟩ := h
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hl23 : Real.log 2 ≤ Real.log 3 :=
    Real.log_le_log (by norm_num) (by norm_num)
  refine ⟨c/Real.log 3, div_pos hc hl3, M₀, ?_⟩
  intro j hj
  have hp : 1 ≤ 2^j := Nat.succ_le_of_lt (pow_pos (by omega) _)
  have hm : M₀ ≤ 2^j := hj.trans (index_le_two_pow j)
  have hb := hlower (2^j) hm hp
  have hpcast : (1 : ℝ) ≤ ((2^j : ℕ) : ℝ) := by exact_mod_cast hp
  have hdenpos : 0 < Real.log (3*((2^j : ℕ) : ℝ)) :=
    Real.log_pos (by linarith)
  have hlog : Real.log (3*((2^j : ℕ) : ℝ)) =
      Real.log 3+(j : ℝ)*Real.log 2 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_mul (by norm_num) (by positivity),
      Real.log_pow]
  have hden : Real.log (3*((2^j : ℕ) : ℝ)) ≤ Real.log 3*((j : ℝ)+1) := by
    rw [hlog]
    nlinarith [mul_le_mul_of_nonneg_left hl23 (Nat.cast_nonneg j)]
  calc
    (c/Real.log 3)/((j : ℝ)+1) = c/(Real.log 3*((j : ℝ)+1)) := div_div _ _ _
    _ ≤ c/Real.log (3*((2^j : ℕ) : ℝ)) := by
      apply (div_le_div_iff₀ (mul_pos hl3 (by positivity)) hdenpos).mpr
      exact mul_le_mul_of_nonneg_left hden hc.le
    _ ≤ distance (2^j) := hb

/-- Conditional sharp liminf statement for the actual distances. -/
theorem late_scaled_gain_of_burnolEnvelope
    (h : BurnolDistanceLowerEnvelope) (a : ℝ) (ha : 1 < a) (J : ℕ) :
    ∃ j, J ≤ j ∧ ((j : ℝ)+1)*(gain (2^j)/distance (2^j)) < a := by
  obtain ⟨c, hc, N₀, hlower⟩ := dyadicEnvelope_of_burnolEnvelope h
  exact conditional_dyadic_sharp_gain c hc N₀ hlower a ha J

/-- Every explicit eventual logarithmic witness bound has constant at
least `1/log 2`, conditional on the actual Burnol distance envelope.
Witness feasibility forces positive gain, so no zero denominator is
silently interpreted as a finite constrained optimum. -/
theorem cost_constant_ge_of_burnolEnvelope
    (h : BurnolDistanceLowerEnvelope) (C : ℝ) (hC : 0 < C) (M₀ : ℕ)
    (hcost : ∀ M : ℕ, M₀ ≤ M → 1 ≤ M →
      ∃ w : ThresholdHilbert, w ∈ budgetHilbert (2*M) ∧
        w ∈ (budgetHilbert M)ᗮ ∧ inner ℝ (error M) w = distance M ∧
        ‖w‖^2 ≤ (C*Real.log (2*(M : ℝ)))*distance M) :
    1/Real.log 2 ≤ C := by
  obtain ⟨c, hc, N₀, hlower⟩ := dyadicEnvelope_of_burnolEnvelope h
  apply RiemannResearch.Analysis.LogarithmicResidualBarrier.eventual_cost_constant_ge_inv_log_two
    (fun j => distance (2^j)) (fun j => distance_pos _) c hc N₀ hlower C hC M₀
  intro j hj
  have hp : 1 ≤ 2^j := Nat.succ_le_of_lt (pow_pos (by omega) _)
  have hm : M₀ ≤ 2^j := hj.trans (index_le_two_pow j)
  have hpcast : (1 : ℝ) ≤ ((2^j : ℕ) : ℝ) := by exact_mod_cast hp
  have hlogpos : 0 < Real.log (2*((2^j : ℕ) : ℝ)) :=
    Real.log_pos (by linarith)
  have hB : 0 < C*Real.log (2*((2^j : ℕ) : ℝ)) := mul_pos hC hlogpos
  have hd := (normalized_cost_iff_gain (2^j) _ hB).mp (hcost (2^j) hm hp)
  have hg : 0 < gain (2^j) := by
    by_contra hn
    have hz := mul_nonpos_of_nonneg_of_nonpos hB.le (le_of_not_gt hn)
    linarith [distance_pos (2^j)]
  have hlog : Real.log (2*((2^j : ℕ) : ℝ)) = ((j : ℝ)+1)*Real.log 2 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_mul (by norm_num) (by positivity),
      Real.log_pow]
    ring
  have hb : (distance (2^j))^2/gain (2^j) ≤
      C*distance (2^j)*(((j : ℝ)+1)*Real.log 2) := by
    apply (div_le_iff₀ hg).mpr
    rw [hlog] at hd
    have hh := mul_le_mul_of_nonneg_right hd (distance_pos (2^j)).le
    nlinarith
  have hnext : 2*2^j = 2^(j+1) := by rw [pow_succ]; omega
  simpa only [gain, hnext] using And.intro hg hb

end RiemannResearch.RH.Pareto.CoupledResidual
