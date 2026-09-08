import RiemannResearch.RH.FiniteSeedComponentCharge
import RiemannResearch.RH.DivisorComponentArithmetic
import RiemannResearch.RH.DivisorComponentSignal

/-!
# A uniform signed obstruction when the complementary conductor is coprime to 6

Source: the exact component argument in the 8 September 2026 RH continuation.
For `M = D * r` with `r` coprime to 6, every legal two-seed edge enters the
divisor component of `D` at both endpoints or at neither endpoint. Thus the
same explicit finite functional works uniformly as all the other primes and
prime powers in `r` vary. No coefficient sign or size assumption is made.
-/

namespace RiemannResearch.RH.DivisorSeedComponentObstruction

open scoped BigOperators
open PositiveSeedCone TwoSeedThreshold FiniteSeedComponentCharge

noncomputable section

/-- Divisor-component charge is zero on every signed legal combination. -/
theorem divisorComponent_seedCombination_charge_zero {ι : Type*}
    (D r : ℕ) (hD : 0 < D) (hr : Nat.Coprime 6 r)
    (s : Finset ι) (a m : ι → ℕ) (c : ι → ℝ)
    (ha : ∀ i ∈ s, a i = 2 ∨ a i = 3)
    (hm : ∀ i ∈ s, 0 < m i)
    (hperiod : ∀ i ∈ s, a i * m i ∣ D * r) :
    componentCharge D.divisors (seedCombination s a m c) = 0 := by
  have ha0 : ∀ i ∈ s, 0 < a i := by
    intro i hi
    rcases ha i hi with h | h <;> omega
  apply seedCombination_componentCharge_eq_zero D.divisors s a m c
    (fun _ hn => Nat.pos_of_mem_divisors hn) ha0 hm
  intro i hi
  rw [Nat.mem_divisors, Nat.mem_divisors]
  exact and_congr (twoSeed_dvd_component_iff (hm i hi) (ha i hi) hr (hperiod i hi)) Iff.rfl

/-- The positive signal is exactly the totient ratio for every divisor component. -/
theorem divisorComponent_signal (D : ℕ) (hD : 0 < D) :
    componentSignal D.divisors = (Nat.totient D : ℝ) / (D : ℝ) :=
  divisor_moebius_signal_eq_totient_div hD

/-- The same finite component gives its full infinite lower bound for every
complementary conductor `r` coprime to 6. -/
theorem divisorComponent_seedCombination_fullError_lower {ι : Type*}
    (D r : ℕ) (hD : 0 < D) (hr : Nat.Coprime 6 r)
    (s : Finset ι) (a m : ι → ℕ) (c : ι → ℝ)
    (ha : ∀ i ∈ s, a i = 2 ∨ a i = 3)
    (hm : ∀ i ∈ s, 0 < m i)
    (hperiod : ∀ i ∈ s, a i * m i ∣ D * r) :
    0 < (componentSignal D.divisors) ^ 2 / componentDualNorm D.divisors D ∧
      (componentSignal D.divisors) ^ 2 / componentDualNorm D.divisors D ≤
        ∑' k : ℕ, weightedError (seedCombination s a m c) k := by
  have hT : componentSignal D.divisors ≠ 0 :=
    ne_of_gt (divisor_moebius_signal_pos hD)
  have hSD : ∀ n ∈ D.divisors, 0 < n ∧ n ≤ D := by
    intro n hn
    exact ⟨Nat.pos_of_mem_divisors hn,
      Nat.le_of_dvd hD (Nat.dvd_of_mem_divisors hn)⟩
  have ha0 : ∀ i ∈ s, 0 < a i := by
    intro i hi
    rcases ha i hi with h | h <;> omega
  apply closedComponent_seedCombination_fullError_lower D.divisors D s a m c
    hSD ha0 hm _ hT
  intro i hi
  rw [Nat.mem_divisors, Nat.mem_divisors]
  exact and_congr (twoSeed_dvd_component_iff (hm i hi) (ha i hi) hr (hperiod i hi)) Iff.rfl

end

end RiemannResearch.RH.DivisorSeedComponentObstruction
