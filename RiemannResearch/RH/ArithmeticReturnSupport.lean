import RiemannResearch.RH.NymanConductorArithmetic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.Support
import Mathlib.Tactic.FunProp

/-!
# Actual arithmetic returns: local finiteness, smoothness, and remote support

Source: user-provided argument, §§4 and 9 of
`RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md`.
The sums below are the actual half-density translates on the real line.
The term at zero vanishes by the arithmetic-function convention.
-/

open scoped BigOperators Topology

namespace RiemannResearch.RH

/-- Actual half-density arithmetic synthesis, not an abstract linear map. -/
noncomputable def arithmeticReturn (c : ArithmeticFunction ℝ)
    (u : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∑' k : ℕ, (c k / Real.sqrt k : ℝ) • u (y - Real.log k)

/-- The concrete full return for the Nyman conductor. -/
noncomputable def nymanFullReturn (n : ℕ) (u : ℝ → ℂ) : ℝ → ℂ :=
  arithmeticReturn (nymanConductorBeta n) u

theorem arithmeticReturn_term_zero_of_bound (c : ArithmeticFunction ℝ)
    {u : ℝ → ℂ} {a Y y : ℝ} {N k : ℕ}
    (hu : ∀ x < a, u x = 0) (hy : y ≤ Y)
    (hN : Real.exp (Y - a) < (N + 1 : ℕ)) (hk : N < k) :
    (c k / Real.sqrt k : ℝ) • u (y - Real.log k) = 0 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hNk : (N + 1 : ℝ) ≤ k := by exact_mod_cast (Nat.succ_le_iff.mpr hk)
  have hY : Real.exp (y - a) ≤ Real.exp (Y - a) :=
    Real.exp_le_exp.mpr (sub_le_sub_right hy a)
  have he : Real.exp (y - a) < k :=
    lt_of_le_of_lt hY (lt_of_lt_of_le (by exact_mod_cast hN) hNk)
  have hl : y - a < Real.log k := (Real.lt_log_iff_exp_lt hkpos).mpr he
  rw [hu (y - Real.log k) (by linarith), smul_zero]

/-- On every left-bounded observation window the infinite return is exactly
one finite sum. No convergence estimate or arithmetic cancellation is used. -/
theorem arithmeticReturn_eq_sum (c : ArithmeticFunction ℝ)
    {u : ℝ → ℂ} {a Y y : ℝ} {N : ℕ}
    (hu : ∀ x < a, u x = 0) (hy : y ≤ Y)
    (hN : Real.exp (Y - a) < (N + 1 : ℕ)) :
    arithmeticReturn c u y =
      ∑ k ∈ Finset.range (N + 1), (c k / Real.sqrt k : ℝ) •
        u (y - Real.log k) := by
  apply tsum_eq_sum
  intro k hk
  exact arithmeticReturn_term_zero_of_bound c hu hy hN
    (by simp only [Finset.mem_range] at hk; omega)

theorem arithmeticReturn_summable (c : ArithmeticFunction ℝ)
    {u : ℝ → ℂ} {a y : ℝ} (hu : ∀ x < a, u x = 0) :
    Summable (fun k : ℕ => (c k / Real.sqrt k : ℝ) •
      u (y - Real.log k)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp (y - a))
  apply summable_of_ne_finset_zero (s := Finset.range (N + 1))
  intro k hk
  exact arithmeticReturn_term_zero_of_bound c hu le_rfl
    (lt_trans hN (by exact_mod_cast Nat.lt_succ_self N))
    (by simp only [Finset.mem_range] at hk; omega)

/-- Smoothness is proved from an exact locally finite description of the
actual arithmetic translates. The input only needs a lower support bound. -/
theorem arithmeticReturn_contDiff (c : ArithmeticFunction ℝ)
    {u : ℝ → ℂ} {a : ℝ} {r : WithTop ℕ∞}
    (hu : ContDiff ℝ r u) (ha : ∀ x < a, u x = 0) :
    ContDiff ℝ r (arithmeticReturn c u) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp (y + 1 - a))
  let F : ℝ → ℂ := fun x => ∑ k ∈ Finset.range (N + 1),
    (c k / Real.sqrt k : ℝ) • u (x - Real.log k)
  have hF : ContDiff ℝ r F := by
    dsimp [F]
    fun_prop
  apply hF.contDiffAt.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds (by linarith : y < y + 1)] with x hx
  exact arithmeticReturn_eq_sum c ha (le_of_lt hx)
    (lt_trans hN (by exact_mod_cast Nat.lt_succ_self N))

theorem arithmeticReturn_zero_below (c : ArithmeticFunction ℝ)
    {u : ℝ → ℂ} {a y : ℝ} (hu : ∀ x < a, u x = 0) (hy : y < a) :
    arithmeticReturn c u y = 0 := by
  calc
    arithmeticReturn c u y = ∑' _ : ℕ, (0 : ℂ) := by
      apply tsum_congr
      intro k
      by_cases hk : k = 0
      · simp [hk]
      have hl : 0 ≤ Real.log k := Real.log_nonneg
        (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk)
      rw [hu (y - Real.log k) (by linarith), smul_zero]
    _ = 0 := tsum_zero

/-- A vanished arithmetic prefix translates into a genuine physical support gap. -/
theorem arithmeticReturn_zero_below_log_gap (c : ArithmeticFunction ℝ)
    {u : ℝ → ℂ} {a y : ℝ} {M : ℕ}
    (hu : ∀ x < a, u x = 0) (hc : ∀ k ≤ M, c k = 0)
    (hy : y < a + Real.log (M + 1 : ℕ)) :
    arithmeticReturn c u y = 0 := by
  calc
    arithmeticReturn c u y = ∑' _ : ℕ, (0 : ℂ) := by
      apply tsum_congr
      intro k
      by_cases hk : k ≤ M
      · rw [hc k hk, zero_div, zero_smul]
      have hMk : M + 1 ≤ k := by omega
      have hl : Real.log (M + 1 : ℕ) ≤ Real.log k :=
        Real.log_le_log (by exact_mod_cast Nat.zero_lt_succ M)
          (by exact_mod_cast hMk)
      rw [hu (y - Real.log k) (by linarith), smul_zero]
    _ = 0 := tsum_zero

theorem arithmeticReturn_tsupport_gap (c : ArithmeticFunction ℝ)
    {u : ℝ → ℂ} {a : ℝ} {M : ℕ}
    (hu : ∀ x < a, u x = 0) (hc : ∀ k ≤ M, c k = 0) :
    tsupport (arithmeticReturn c u) ⊆ Set.Ici (a + Real.log (M + 1 : ℕ)) := by
  apply closure_minimal _ isClosed_Ici
  intro y hy
  by_contra h
  exact hy (arithmeticReturn_zero_below_log_gap c hu hc
    (by simpa only [Set.mem_Ici, not_le] using h))

/-- The finite inverse potential from §9, with the actual inverse coefficients. -/
noncomputable def nymanInversePotential (n M : ℕ) (hn : 2 ≤ n)
    (v : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∑ k ∈ Finset.range (M + 1),
    (nymanConductorInverse n hn k / Real.sqrt k : ℝ) • v (y - Real.log k)

theorem nymanInversePotential_contDiff (n M : ℕ) (hn : 2 ≤ n)
    {v : ℝ → ℂ} {r : WithTop ℕ∞} (hv : ContDiff ℝ r v) :
    ContDiff ℝ r (nymanInversePotential n M hn v) := by
  unfold nymanInversePotential
  fun_prop

theorem nymanInversePotential_eq_return (n M : ℕ) (hn : 2 ≤ n)
    (v : ℝ → ℂ) :
    nymanInversePotential n M hn v =
      arithmeticReturn (nymanConductorInversePrefix n M hn) v := by
  funext y
  symm
  calc
    arithmeticReturn (nymanConductorInversePrefix n M hn) v y =
        ∑ k ∈ Finset.range (M + 1),
          (nymanConductorInversePrefix n M hn k / Real.sqrt k : ℝ) •
            v (y - Real.log k) := by
      apply tsum_eq_sum
      intro k hk
      simp [nymanConductorInversePrefix, show ¬ k ≤ M by
        simp only [Finset.mem_range] at hk; omega]
    _ = nymanInversePotential n M hn v y := by
      unfold nymanInversePotential
      apply Finset.sum_congr rfl
      intro k hk
      simp [nymanConductorInversePrefix,
        Nat.le_of_lt_succ (Finset.mem_range.mp hk)]

/-- Actual coefficient-synthesized remote remainder. Identification with the
iterated return is a separate convolution theorem. -/
noncomputable def nymanArithmeticTailPotential (n M : ℕ) (hn : 2 ≤ n)
    (v : ℝ → ℂ) : ℝ → ℂ :=
  arithmeticReturn
    (nymanConductorBeta n * nymanConductorInversePrefix n M hn - 1) v

theorem nymanArithmeticTailPotential_tsupport (n M : ℕ) (hn : 2 ≤ n)
    {v : ℝ → ℂ} {a : ℝ} (hv : ∀ x < a, v x = 0) :
    tsupport (nymanArithmeticTailPotential n M hn v) ⊆
      Set.Ici (a + Real.log (M + 1 : ℕ)) := by
  apply arithmeticReturn_tsupport_gap _ hv
  intro k hk
  change (nymanConductorBeta n * nymanConductorInversePrefix n M hn) k -
    (1 : ArithmeticFunction ℝ) k = 0
  rw [nymanConductorInversePrefix_exact hn hk, ArithmeticFunction.one_apply, sub_self]

theorem nymanArithmeticTailPotential_contDiff (n M : ℕ) (hn : 2 ≤ n)
    {v : ℝ → ℂ} {a : ℝ} {r : WithTop ℕ∞}
    (hv : ContDiff ℝ r v) (ha : ∀ x < a, v x = 0) :
    ContDiff ℝ r (nymanArithmeticTailPotential n M hn v) :=
  arithmeticReturn_contDiff _ hv ha

end RiemannResearch.RH
