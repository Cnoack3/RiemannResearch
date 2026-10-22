import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import RiemannResearch.Analysis.SignedIncidenceEnergy
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Signed prime-only dyadic energy

Source: user-provided manuscript `Prime_Phases_Agenda_Proof_Attempts.tex`,
section "Removing higher prime powers without losing the RH scale".

The finite signed incidence expansion and algebraic prime-power correction below
are unconditional. The Hilbert space perturbation lemma is abstract and has an
explicit error-norm hypothesis. This module does not prove the PNT provider,
summability of the actual prime-power error, or the integrated explicit formula.
-/

noncomputable section

open scoped BigOperators

namespace RiemannResearch.RH.PrimeOnlyDyadicEnergy

open RiemannResearch.Analysis.SignedIncidence

/-- Pareto weight; the zero index is excluded from all energies. -/
def weight (m : ℕ) : ℝ := 1 / ((m : ℝ) * ((m : ℝ) + 1))

/-- All actual primes through the cutoff. -/
def primesThrough (N : ℕ) : Finset ℕ :=
  (Finset.range (N + 1)).filter Nat.Prime

/-- The actual full von Mangoldt counting sum. -/
noncomputable def psi (m : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 m, ArithmeticFunction.vonMangoldt n

/-- The actual finite Chebyshev theta sum. -/
def theta (m : ℕ) : ℝ := ∑ p ∈ primesThrough m, Real.log p

/-- Expressing theta in a larger prime ambient set changes no conductor. -/
theorem theta_eq_ambient (N m : ℕ) (hm : m ≤ N) :
    theta m = ∑ p ∈ primesThrough N, if p ≤ m then Real.log p else 0 := by
  have hsub : primesThrough m ⊆ primesThrough N := by
    intro p hp
    simp only [primesThrough, Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hzero : ∀ p ∈ primesThrough N, p ∉ primesThrough m →
      (if p ≤ m then Real.log p else 0) = 0 := by
    intro p hp hn
    apply if_neg
    intro hpm
    apply hn
    simp only [primesThrough, Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  have hsum := Finset.sum_subset hsub hzero
  calc
    theta m = ∑ p ∈ primesThrough m, if p ≤ m then Real.log p else 0 := by
      unfold theta
      apply Finset.sum_congr rfl
      intro p hp
      have hpm : p ≤ m := by
        simp only [primesThrough, Finset.mem_filter, Finset.mem_range] at hp
        omega
      simp [hpm]
    _ = _ := hsum

/-- The exact dyadic incidence, including both finite endpoints. -/
def incidence (m p : ℕ) : ℝ :=
  if m / 2 < p ∧ p ≤ m then 1 else 0

/-- The prime incidence is exactly the difference of actual theta sums. -/
theorem theta_window_eq_incidence (N m : ℕ) (hm : m ≤ N) :
    theta m - theta (m / 2) =
      ∑ p ∈ primesThrough N, Real.log p * incidence m p := by
  have hk : m / 2 ≤ m := Nat.div_le_self _ _
  rw [theta_eq_ambient N m hm, theta_eq_ambient N (m / 2) (hk.trans hm),
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  unfold incidence
  by_cases hpm : p ≤ m
  · by_cases hpk : p ≤ m / 2
    · simp [hpm, hpk, show ¬m / 2 < p by omega]
    · simp [hpm, hpk, show m / 2 < p by omega]
  · have hpk : ¬p ≤ m / 2 := by omega
    simp [hpm, hpk]

/-- The square-root corrected deterministic background. -/
def background (m : ℕ) : ℝ :=
  (m : ℝ) - (m / 2 : ℕ) - Real.sqrt m + Real.sqrt (m / 2 : ℕ)

/-- The corrected finite prime-only window residual. -/
def residual (N m : ℕ) : ℝ :=
  (∑ p ∈ primesThrough N, Real.log p * incidence m p) - background m

/-- The finite prime residual is the manuscript's corrected theta window. -/
theorem residual_eq_corrected_theta_window (N m : ℕ) (hm : m ≤ N) :
    residual N m = theta m - theta (m / 2) - (m : ℝ) +
      (m / 2 : ℕ) + Real.sqrt m - Real.sqrt (m / 2 : ℕ) := by
  unfold residual background
  rw [← theta_window_eq_incidence N m hm]
  ring

/-- Complete prime-only budget with signed distinct-prime terms and diagonal. -/
theorem exact_prime_only_budget (N : ℕ) :
    energy (Finset.Icc 1 N) weight (residual N) =
      energy (Finset.Icc 1 N) weight background +
      (∑ p ∈ primesThrough N, (Real.log p) ^ 2 *
        kernel (Finset.Icc 1 N) weight incidence p p) +
      2 * cross (primesThrough N) (fun p => Real.log p)
        (kernel (Finset.Icc 1 N) weight incidence) -
      2 * ∑ p ∈ primesThrough N,
        Real.log p * row (Finset.Icc 1 N) weight background incidence p := by
  unfold residual
  rw [energy_expansion, full_gram_eq_diagonal_add_cross]
  ring

/-- The exact higher-power remainder, retaining its deterministic square root. -/
noncomputable def higherPowerError (m : ℕ) : ℝ :=
  psi m - theta m - Real.sqrt m

/-- The actual full von Mangoldt dyadic residual. -/
noncomputable def psiWindowResidual (m : ℕ) : ℝ :=
  psi m - psi (m / 2) - (m : ℝ) + (m / 2 : ℕ)

/-- Exact signed reduction of the actual prime-power window to actual primes. -/
theorem actual_prime_power_window_identity (N m : ℕ) (hm : m ≤ N) :
    psiWindowResidual m = residual N m +
      higherPowerError m - higherPowerError (m / 2) := by
  rw [residual_eq_corrected_theta_window N m hm]
  unfold psiWindowResidual higherPowerError
  ring

/-- The identity separating prime counting from higher-power counting is exact,
with no estimate and no PNT hypothesis. -/
theorem corrected_window_identity (psi theta : ℕ → ℝ) (m : ℕ) :
    psi m - psi (m / 2) - (m : ℝ) + (m / 2 : ℕ) =
      (theta m - theta (m / 2) - (m : ℝ) + (m / 2 : ℕ) +
        Real.sqrt m - Real.sqrt (m / 2 : ℕ)) +
      (psi m - theta m - Real.sqrt m) -
      (psi (m / 2) - theta (m / 2) - Real.sqrt (m / 2 : ℕ)) := by
  ring

end RiemannResearch.RH.PrimeOnlyDyadicEnergy
