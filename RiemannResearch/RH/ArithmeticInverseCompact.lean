import RiemannResearch.RH.ArithmeticReturnSupport
import Mathlib.Topology.Order.Compact

/-!
# Compact support of the actual truncated arithmetic inverse potential

Source: user-provided argument, §9 of
`RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md`.

The finite inverse potential is supported in `[a, b + log M]` whenever its
input is supported in `[a,b]`; at `M = 0` it vanishes. This concerns the actual
translated inverse coefficients, with no abstract support-transfer hypothesis.
-/

open scoped BigOperators Topology

namespace RiemannResearch.RH

theorem nymanInversePotential_zero_below (n M : ℕ) (hn : 2 ≤ n)
    {v : ℝ → ℂ} {a y : ℝ} (ha : ∀ x < a, v x = 0) (hy : y < a) :
    nymanInversePotential n M hn v y = 0 := by
  rw [nymanInversePotential_eq_return]
  exact arithmeticReturn_zero_below _ ha hy

theorem nymanInversePotential_zero_above (n M : ℕ) (hn : 2 ≤ n)
    {v : ℝ → ℂ} {b y : ℝ} (hb : ∀ x > b, v x = 0)
    (hy : b + Real.log M < y) :
    nymanInversePotential n M hn v y = 0 := by
  unfold nymanInversePotential
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hk0 : k = 0
  · simp [hk0]
  have hkM : k ≤ M := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hl : Real.log k ≤ Real.log M := Real.log_le_log
    (by exact_mod_cast Nat.pos_of_ne_zero hk0) (by exact_mod_cast hkM)
  rw [hb (y - Real.log k) (by linarith), smul_zero]

/-- An explicit closed interval contains the actual inverse potential. -/
theorem nymanInversePotential_tsupport (n M : ℕ) (hn : 2 ≤ n)
    {v : ℝ → ℂ} {a b : ℝ}
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0) :
    tsupport (nymanInversePotential n M hn v) ⊆
      Set.Icc a (b + Real.log M) := by
  apply closure_minimal _ isClosed_Icc
  intro y hy
  constructor
  · by_contra h
    exact hy (nymanInversePotential_zero_below n M hn ha (lt_of_not_ge h))
  · by_contra h
    exact hy (nymanInversePotential_zero_above n M hn hb (lt_of_not_ge h))

/-- Compactness of the inverse potential is supplied, rather than assumed. -/
theorem nymanInversePotential_hasCompactSupport (n M : ℕ) (hn : 2 ≤ n)
    {v : ℝ → ℂ} {a b : ℝ}
    (ha : ∀ x < a, v x = 0) (hb : ∀ x > b, v x = 0) :
    HasCompactSupport (nymanInversePotential n M hn v) := by
  exact isCompact_Icc.of_isClosed_subset isClosed_closure
    (nymanInversePotential_tsupport n M hn ha hb)

end RiemannResearch.RH
