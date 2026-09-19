import RiemannResearch.Analysis.SharpLogarithmicResidualBarrier

/-!
# Scalar transfer and rate obstruction for point-approximation energies

Source: user-provided
`RH_First_Coordinate_and_Tail_Capacity_Continuation_2026-09-19.md`, Section 19,
for the finite scalar estimates and rate-obstruction strategy. Every analytic
input is an explicit hypothesis. This general module neither invokes nor
postulates Burnol's external analytic theorem or an RH-specific provider.
-/

noncomputable section

namespace RiemannResearch.Analysis.LogarithmicResidualBarrier

/-- A finite exact-constant transfer step used before taking the logarithmic
liminf. The input `hcomparison` comes from point-to-constant synthesis. -/
theorem point_lower_of_sqrt_comparison
    (E δ L c b A : ℝ) (hδ : 0 ≤ δ) (hL : 0 ≤ L) (hA : 0 < A)
    (hlower : c ≤ L * E)
    (hcomparison : Real.sqrt E ≤ b + A * Real.sqrt δ)
    (hhead : Real.sqrt L * b ≤ Real.sqrt c) :
    ((Real.sqrt c - Real.sqrt L * b) / A) ^ 2 ≤ L * δ := by
  have hroot : Real.sqrt c ≤ Real.sqrt L * Real.sqrt E := by
    rw [← Real.sqrt_mul hL]
    exact Real.sqrt_le_sqrt hlower
  have hscaled := mul_le_mul_of_nonneg_left hcomparison (Real.sqrt_nonneg L)
  have hlin : (Real.sqrt c - Real.sqrt L * b) / A ≤
      Real.sqrt L * Real.sqrt δ := by
    apply (div_le_iff₀ hA).mpr
    nlinarith
  have hsq := (sq_le_sq₀
    (div_nonneg (sub_nonneg.mpr hhead) hA.le)
    (mul_nonneg (Real.sqrt_nonneg L) (Real.sqrt_nonneg δ))).mpr hlin
  simpa only [mul_pow, Real.sq_sqrt hL, Real.sq_sqrt hδ] using hsq

/-- The reciprocal capacity identity transfers an error lower bound to an
upper bound with the exact finite correction `-2`. -/
theorem capacity_upper_of_point_lower
    (τ δ L c : ℝ) (hc : 0 < c) (hτ : 0 < τ + 2)
    (hidentity : δ = 1 / (τ + 2)) (hlower : c ≤ L * δ) :
    τ ≤ L / c - 2 := by
  rw [hidentity, mul_one_div] at hlower
  have h := (le_div_iff₀ hτ).mp hlower
  have h' : τ + 2 ≤ L / c := by
    apply (le_div_iff₀ hc).mpr
    nlinarith
  linarith

/-- A positive reciprocal-index lower envelope excludes any eventual fixed
fractional improvement. This uses the already checked sharp logarithmic
barrier; no assumption about zeta zeros is added. -/
theorem exists_late_failure_of_fixed_contraction
    (d : ℕ → ℝ) (hd : ∀ j, 0 < d j)
    (c : ℝ) (hc : 0 < c) (N₀ : ℕ)
    (hlower : ∀ n, N₀ ≤ n → c / ((n : ℝ) + 1) ≤ d n)
    (η : ℝ) (hη : 0 < η) (J : ℕ) :
    ∃ j, J ≤ j ∧ (1 - η) * d j < d (j + 1) := by
  obtain ⟨K, hK⟩ := exists_nat_gt (2 / η)
  obtain ⟨j, hj, hsmall⟩ := exists_late_scaled_gain_lt_of_distance_lower
    d hd c hc N₀ hlower 2 (by norm_num) (max J K)
  refine ⟨j, le_trans (le_max_left J K) hj, ?_⟩
  by_contra hnot
  have hcontract : d (j + 1) ≤ (1 - η) * d j := le_of_not_gt hnot
  have hgain : η ≤ relativeGain d j := by
    unfold relativeGain
    apply (le_div_iff₀ (hd j)).mpr
    nlinarith
  have hKj : (K : ℝ) ≤ j := by
    exact_mod_cast (le_trans (le_max_right J K) hj)
  have hlarge : 2 < η * ((j : ℝ) + 1) := by
    have h := (div_lt_iff₀ hη).mp hK
    nlinarith
  have hgain' := mul_le_mul_of_nonneg_left hgain
    (show 0 ≤ (j : ℝ) + 1 by positivity)
  nlinarith

end RiemannResearch.Analysis.LogarithmicResidualBarrier
