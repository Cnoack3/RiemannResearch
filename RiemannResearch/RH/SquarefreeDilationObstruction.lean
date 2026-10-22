import RiemannResearch.RH.FiniteSeedComponentCharge
import RiemannResearch.RH.ParetoBoundedInteraction
import Mathlib.Tactic.NormNum

/-!
# Squarefree dilation indices do not suffice

Source: RH_Minimal_Seeds_Canonical_Basis_and_Arithmetic_Charge_20260914.md,
sections 7--8.  The finite separating component is the component rooted at 5.
This module proves a positive lower bound for the full actual Pareto error;
all coefficients may be signed and all other primes remain unrestricted.
-/

namespace RiemannResearch.RH.Pareto

open scoped BigOperators
open Filter FiniteSeedComponentCharge PositiveSeedCone TwoSeedThreshold

noncomputable section

/-- Every endpoint in the 5-component of a squarefree dilation lies here. -/
def squarefreeChargeSet : Finset ℕ := {5, 10, 15, 20, 30, 45, 60, 90}

theorem squarefreeChargeSet_pos_bound (n : ℕ) (hn : n ∈ squarefreeChargeSet) :
    0 < n ∧ n ≤ 90 := by
  simp only [squarefreeChargeSet, Finset.mem_insert, Finset.mem_singleton] at hn
  omega

/-- The two seed edges cannot cross this finite cut when their lower index
has neither a square factor 4 nor a square factor 9. -/
theorem squarefreeChargeSet_closed (a m : ℕ) (ha : a = 2 ∨ a = 3)
    (h4 : ¬ 4 ∣ m) (h9 : ¬ 9 ∣ m) :
    m ∈ squarefreeChargeSet ↔ a * m ∈ squarefreeChargeSet := by
  rw [Nat.dvd_iff_mod_eq_zero] at h4 h9
  rcases ha with rfl | rfl
  all_goals
    simp only [squarefreeChargeSet, Finset.mem_insert, Finset.mem_singleton]
    omega

theorem squarefree_not_four_dvd {m : ℕ} (hm : Squarefree m) : ¬ 4 ∣ m := by
  intro h
  have hu := hm 2 h
  norm_num at hu

theorem squarefree_not_nine_dvd {m : ℕ} (hm : Squarefree m) : ¬ 9 ∣ m := by
  intro h
  have hu := hm 3 h
  norm_num at hu

/-- The target has a nonzero arithmetic signal on the same finite cut. -/
theorem squarefreeChargeSet_signal : componentSignal squarefreeChargeSet = -1 / 15 := by
  have h5 : ArithmeticFunction.moebius 5 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by decide)
  have h2 : ArithmeticFunction.moebius 2 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by decide)
  have h3 : ArithmeticFunction.moebius 3 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by decide)
  have h10 := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
    (by decide : Nat.Coprime 2 5)
  have h15 := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
    (by decide : Nat.Coprime 3 5)
  have h30 := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
    (by decide : Nat.Coprime 2 15)
  norm_num [h2, h3, h5] at h10 h15
  norm_num [h2, h15] at h30
  have h20 : ArithmeticFunction.moebius 20 = 0 := by
    apply not_not.mp
    intro h
    have hs := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp h
    exact squarefree_not_four_dvd hs (by decide)
  have h45 : ArithmeticFunction.moebius 45 = 0 := by
    apply not_not.mp
    intro h
    have hs := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp h
    exact squarefree_not_nine_dvd hs (by decide)
  have h60 : ArithmeticFunction.moebius 60 = 0 := by
    apply not_not.mp
    intro h
    have hs := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp h
    exact squarefree_not_four_dvd hs (by decide)
  have h90 : ArithmeticFunction.moebius 90 = 0 := by
    apply not_not.mp
    intro h
    have hs := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp h
    exact squarefree_not_nine_dvd hs (by decide)
  norm_num [componentSignal, squarefreeChargeSet, h5, h10, h15, h20, h30, h45, h60, h90]

/-- The separating row has strictly positive finite Pareto dual norm. -/
theorem squarefreeChargeSet_dualNorm_pos :
    0 < componentDualNorm squarefreeChargeSet 90 :=
  componentDualNorm_pos _ _ squarefreeChargeSet_pos_bound (by
    rw [squarefreeChargeSet_signal]
    norm_num)

/-- Uniform positive full-error obstruction, already under the weaker
restriction excluding only the square factors 4 and 9 from dilation indices. -/
theorem squarefree_seed_dilation_fullError_lower {ι : Type*}
    (s : Finset ι) (a m : ι → ℕ) (c : ι → ℝ)
    (ha : ∀ i ∈ s, a i = 2 ∨ a i = 3)
    (hm : ∀ i ∈ s, 0 < m i)
    (h4 : ∀ i ∈ s, ¬ 4 ∣ m i) (h9 : ∀ i ∈ s, ¬ 9 ∣ m i) :
    0 < (1 / 225 : ℝ) / componentDualNorm squarefreeChargeSet 90 ∧
      (1 / 225 : ℝ) / componentDualNorm squarefreeChargeSet 90 ≤
        ∑' k : ℕ, weightedError (seedCombination s a m c) k := by
  have he := closedComponent_seedCombination_fullError_lower
    squarefreeChargeSet 90 s a m c squarefreeChargeSet_pos_bound
    (by intro i hi; rcases ha i hi with h | h <;> omega) hm
    (fun i hi => squarefreeChargeSet_closed (a i) (m i) (ha i hi) (h4 i hi) (h9 i hi))
    (by rw [squarefreeChargeSet_signal]; norm_num)
  norm_num [squarefreeChargeSet_signal] at he
  exact ⟨div_pos (by norm_num) he.1, he.2⟩

/-- In particular, allowing every squarefree dilation is still insufficient. -/
theorem squarefree_seed_dilation_fullError_lower_of_squarefree {ι : Type*}
    (s : Finset ι) (a m : ι → ℕ) (c : ι → ℝ)
    (ha : ∀ i ∈ s, a i = 2 ∨ a i = 3)
    (hm : ∀ i ∈ s, 0 < m i) (hs : ∀ i ∈ s, Squarefree (m i)) :
    0 < (1 / 225 : ℝ) / componentDualNorm squarefreeChargeSet 90 ∧
      (1 / 225 : ℝ) / componentDualNorm squarefreeChargeSet 90 ≤
        ∑' k : ℕ, weightedError (seedCombination s a m c) k :=
  squarefree_seed_dilation_fullError_lower s a m c ha hm
    (fun i hi => squarefree_not_four_dvd (hs i hi))
    (fun i hi => squarefree_not_nine_dvd (hs i hi))

end
end RiemannResearch.RH.Pareto
