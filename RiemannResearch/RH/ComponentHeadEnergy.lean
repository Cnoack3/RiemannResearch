import RiemannResearch.RH.ParetoDilation

/-!
# Exact head-energy cancellation for finite arithmetic decompositions

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md,
Section 8, equation (41). Mixed energy is indexed by all ordered distinct
pairs, so it already equals twice the sum over unordered pairs. No sign,
mixed term, or Pareto weight is discarded. The analytic limit (40) and
the rough-component identification (39) are not asserted in this module.
-/

namespace RiemannResearch.RH.Pareto

open scoped BigOperators

noncomputable section

/-- Finite full Pareto energy, at coordinates 1 through N. -/
def headEnergy (N : ℕ) (F : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.Ico 1 (N + 1), positiveWeight k * (F k) ^ 2

/-- Sum of the individual component head energies. -/
def componentDiagonalHead (N : ℕ) (Q : Finset ℕ) (F : ℕ → ℕ → ℝ) : ℝ :=
  ∑ q ∈ Q, headEnergy N (F q)

/-- Every ordered off-diagonal product, with the original Pareto weights. -/
def componentMixedHead (N : ℕ) (Q : Finset ℕ) (F : ℕ → ℕ → ℝ) : ℝ :=
  ∑ q ∈ Q, ∑ r ∈ Q.erase q,
    ∑ k ∈ Finset.Ico 1 (N + 1), positiveWeight k * (F q k * F r k)

private theorem sum_square_split (Q : Finset ℕ) (f : ℕ → ℝ) :
    (∑ q ∈ Q, f q) ^ 2 =
      (∑ q ∈ Q, (f q) ^ 2) +
        ∑ q ∈ Q, ∑ r ∈ Q.erase q, f q * f r := by
  rw [pow_two, Finset.sum_mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  have h := Finset.sum_erase_add Q (fun r => f q * f r) hq
  simpa only [pow_two, add_comm] using h.symm

/-- The exact component Gram expansion, before any estimate. -/
theorem headEnergy_component_exact (N : ℕ) (Q : Finset ℕ)
    (F : ℕ → ℕ → ℝ) :
    headEnergy N (fun k => ∑ q ∈ Q, F q k) =
      componentDiagonalHead N Q F + componentMixedHead N Q F := by
  unfold headEnergy componentDiagonalHead componentMixedHead
  simp_rw [sum_square_split, mul_add, Finset.mul_sum]
  rw [Finset.sum_add_distrib]
  congr 1
  · exact Finset.sum_comm
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q hq
    exact Finset.sum_comm

/-- Telescoping gives the complete exact head mass, including N = 0. -/
theorem headEnergy_one (N : ℕ) :
    headEnergy N (fun _ => 1) = (N : ℝ) / ((N : ℝ) + 1) := by
  simp only [headEnergy, one_pow, mul_one]
  rw [positiveWeight_interval 1 (N + 1) (by omega) (by omega)]
  push_cast
  have hn : (N : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- Any finite decomposition of an exact head has this signed mixed energy.
The hypothesis is only pointwise decomposition on that finite head; it is
not a bound or an unproved asymptotic statement. -/
theorem exact_head_mixed_energy (N : ℕ) (Q : Finset ℕ)
    (F : ℕ → ℕ → ℝ)
    (hhead : ∀ k, 0 < k → k ≤ N → (∑ q ∈ Q, F q k) = 1) :
    componentMixedHead N Q F =
      (N : ℝ) / ((N : ℝ) + 1) - componentDiagonalHead N Q F := by
  have hh : headEnergy N (fun k => ∑ q ∈ Q, F q k) =
      headEnergy N (fun _ => 1) := by
    unfold headEnergy
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only
    rw [hhead k (Finset.mem_Ico.mp hk).1 (by
      have := (Finset.mem_Ico.mp hk).2
      omega)]
  rw [headEnergy_component_exact, headEnergy_one] at hh
  linarith

end
end RiemannResearch.RH.Pareto
