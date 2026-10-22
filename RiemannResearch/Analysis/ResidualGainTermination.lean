import RiemannResearch.Analysis.ResidualGainProduct

/-!
# Finite termination in the exact residual-gain criterion

Appendix to the gain-product formalization of
`RH_Noise_Signal_Arithmetic_Repair_2026-09-07.pdf`, §8.3.
The report explicitly excludes finite zero residuals when stating the
nonsummability criterion. This module removes that exclusion: for gains in
`[0,1]`, exhaustion is equivalent to a full finite gain or nonsummability.
-/

open Filter
open scoped Topology

namespace RiemannResearch.Analysis.ResidualGain

theorem survivalProduct_eq_zero_of_full_gain {r : ℕ → ℝ} {k n : ℕ}
    (hk : r k = 1) (hkn : k < n) : survivalProduct r n = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_range.mpr hkn)
  simp [hk]

theorem survivalProduct_tendsto_zero_of_full_gain {r : ℕ → ℝ}
    (hfull : ∃ k, r k = 1) : Tendsto (survivalProduct r) atTop (𝓝 0) := by
  obtain ⟨k, hk⟩ := hfull
  apply tendsto_const_nhds.congr'
  filter_upwards [Filter.eventually_ge_atTop (k + 1)] with n hn
  exact (survivalProduct_eq_zero_of_full_gain hk
    (lt_of_lt_of_le (Nat.lt_succ_self k) hn)).symm

/-- The complete product criterion, including possible finite termination. -/
theorem survivalProduct_tendsto_zero_iff_full_gain_or_not_summable {r : ℕ → ℝ}
    (h0 : ∀ n, 0 ≤ r n) (h1 : ∀ n, r n ≤ 1) :
    Tendsto (survivalProduct r) atTop (𝓝 0) ↔
      (∃ n, r n = 1) ∨ ¬Summable r := by
  by_cases hfull : ∃ n, r n = 1
  · exact ⟨fun _ => Or.inl hfull,
      fun _ => survivalProduct_tendsto_zero_of_full_gain hfull⟩
  · have hstrict : ∀ n, r n < 1 := by
      intro n
      rcases lt_or_eq_of_le (h1 n) with hlt | heq
      · exact hlt
      · exact False.elim (hfull ⟨n, heq⟩)
    simpa only [hfull, false_or] using
      survivalProduct_tendsto_zero_iff_not_summable h0 hstrict

theorem residual_eq_zero_of_full_gain {d r : ℕ → ℝ}
    (hrec : ∀ n, d (n + 1) = d n * (1 - r n)) {k n : ℕ}
    (hk : r k = 1) (hkn : k < n) : d n = 0 := by
  rw [recurrence_eq_mul_product hrec,
    survivalProduct_eq_zero_of_full_gain hk hkn, mul_zero]

theorem residual_tendsto_zero_of_full_gain {d r : ℕ → ℝ}
    (hrec : ∀ n, d (n + 1) = d n * (1 - r n))
    (hfull : ∃ k, r k = 1) : Tendsto d atTop (𝓝 0) := by
  obtain ⟨k, hk⟩ := hfull
  apply tendsto_const_nhds.congr'
  filter_upwards [Filter.eventually_ge_atTop (k + 1)] with n hn
  exact (residual_eq_zero_of_full_gain hrec hk
    (lt_of_lt_of_le (Nat.lt_succ_self k) hn)).symm

/-- A finite zero residual occurs exactly when one relative gain equals one.
No sign assumptions on the gains are needed for this finite algebraic fact. -/
theorem finite_termination_iff_full_gain {d r : ℕ → ℝ} (hd : d 0 ≠ 0)
    (hrec : ∀ n, d (n + 1) = d n * (1 - r n)) :
    (∃ n, d n = 0) ↔ ∃ n, r n = 1 := by
  constructor
  · rintro ⟨n, hn⟩
    induction n with
    | zero => exact False.elim (hd hn)
    | succ n ih =>
      rw [hrec] at hn
      rcases mul_eq_zero.mp hn with hzero | hone
      · exact ih hzero
      · exact ⟨n, (sub_eq_zero.mp hone).symm⟩
  · rintro ⟨n, hn⟩
    exact ⟨n + 1, residual_eq_zero_of_full_gain hrec hn (Nat.lt_succ_self n)⟩

/-- The report's diagnostic with finite termination handled explicitly. -/
theorem residual_tendsto_zero_iff_full_gain_or_not_summable {d r : ℕ → ℝ}
    (hd : 0 < d 0) (h0 : ∀ n, 0 ≤ r n) (h1 : ∀ n, r n ≤ 1)
    (hrec : ∀ n, d (n + 1) = d n * (1 - r n)) :
    Tendsto d atTop (𝓝 0) ↔ (∃ n, r n = 1) ∨ ¬Summable r := by
  by_cases hfull : ∃ n, r n = 1
  · exact ⟨fun _ => Or.inl hfull,
      fun _ => residual_tendsto_zero_of_full_gain hrec hfull⟩
  · have hstrict : ∀ n, r n < 1 := by
      intro n
      rcases lt_or_eq_of_le (h1 n) with hlt | heq
      · exact hlt
      · exact False.elim (hfull ⟨n, heq⟩)
    simpa only [hfull, false_or] using
      residual_tendsto_zero_iff_not_summable hd h0 hstrict hrec

end RiemannResearch.Analysis.ResidualGain
