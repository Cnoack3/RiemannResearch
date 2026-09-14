import RiemannResearch.RH.BalancedContinuousCoordinates
import Mathlib.Tactic.FieldSimp

/-!
# Exact Möbius targets of the balanced cut coordinates

Source: RH_Minimal_Seeds_Canonical_Basis_and_Arithmetic_Charge_20260914.md,
Section 4. Only four exponent pairs contribute: higher prime powers have zero
Möbius coefficient. All displayed values are exact real equalities.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
open RiemannResearch.LinearAlgebra
open RiemannResearch.RH.FiniteSeedComponentCharge
noncomputable section

theorem rough_coprime_two (u : ℕ) (hu : IsTwoThreeRough u) : Nat.Coprime 2 u :=
  Nat.prime_two.coprime_iff_not_dvd.mpr hu.2.1

theorem rough_coprime_three (u : ℕ) (hu : IsTwoThreeRough u) : Nat.Coprime 3 u :=
  Nat.prime_three.coprime_iff_not_dvd.mpr hu.2.2

theorem moebius_rough_two (u : ℕ) (hu : IsTwoThreeRough u) :
    ArithmeticFunction.moebius (2 * u) = -ArithmeticFunction.moebius u := by
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
    (rough_coprime_two u hu), ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  ring

theorem moebius_rough_three (u : ℕ) (hu : IsTwoThreeRough u) :
    ArithmeticFunction.moebius (3 * u) = -ArithmeticFunction.moebius u := by
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
    (rough_coprime_three u hu), ArithmeticFunction.moebius_apply_prime Nat.prime_three]
  ring

theorem moebius_rough_six (u : ℕ) (hu : IsTwoThreeRough u) :
    ArithmeticFunction.moebius (6 * u) = ArithmeticFunction.moebius u := by
  have hc : Nat.Coprime 2 (3 * u) :=
    (by decide : Nat.Coprime 2 3).mul_right (rough_coprime_two u hu)
  rw [show 6 * u = 2 * (3 * u) by ring,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two, moebius_rough_three u hu]
  ring

theorem moebius_grid_high_zero (u i j : ℕ) (h : 2 ≤ i ∨ 2 ≤ j) :
    ArithmeticFunction.moebius (2 ^ i * 3 ^ j * u) = 0 := by
  by_contra hne
  have hsf := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hne
  rcases h with hi | hj
  · have he : i = (i - 2) + 2 := by omega
    have hd : 2 * 2 ∣ 2 ^ i * 3 ^ j * u := by
      refine ⟨2 ^ (i - 2) * 3 ^ j * u, ?_⟩
      conv_lhs => rw [he, pow_add]
      ring
    have hh := hsf 2 hd
    norm_num at hh
  · have he : j = (j - 2) + 2 := by omega
    have hd : 3 * 3 ∣ 2 ^ i * 3 ^ j * u := by
      refine ⟨2 ^ i * 3 ^ (j - 2) * u, ?_⟩
      conv_lhs => rw [he, pow_add]
      ring
    have hh := hsf 3 hd
    norm_num at hh

private def cornerPairs : Finset (ℕ × ℕ) := {(0, 0), (1, 0), (0, 1), (1, 1)}

theorem balancedCut_signal_four_terms (u a b : ℕ) (hu : IsTwoThreeRough u) :
    componentSignal (balancedArithmeticCut u a b) =
      (if (0, 0) ∈ balancedGridCut a b then (ArithmeticFunction.moebius u : ℝ) / u else 0) +
      (if (1, 0) ∈ balancedGridCut a b then -(ArithmeticFunction.moebius u : ℝ) / (2 * u) else 0) +
      (if (0, 1) ∈ balancedGridCut a b then -(ArithmeticFunction.moebius u : ℝ) / (3 * u) else 0) +
      (if (1, 1) ∈ balancedGridCut a b then (ArithmeticFunction.moebius u : ℝ) / (6 * u) else 0) := by
  let g : ℕ × ℕ → ℝ := fun ij =>
    (ArithmeticFunction.moebius (2 ^ ij.1 * 3 ^ ij.2 * u) : ℝ) /
      (2 ^ ij.1 * 3 ^ ij.2 * u : ℕ)
  have hsum : componentSignal (balancedArithmeticCut u a b) =
      ∑ ij ∈ balancedGridCut a b, g ij := by
    unfold componentSignal balancedArithmeticCut
    rw [Finset.sum_image]
    intro x hx y hy he
    obtain ⟨huu, ha, hb⟩ := rough_grid_decomposition_unique
      u x.1 x.2 u y.1 y.2 hu hu he
    exact Prod.ext ha hb
  have hsmall : (∑ ij ∈ balancedGridCut a b, g ij) =
      ∑ ij ∈ cornerPairs, if ij ∈ balancedGridCut a b then g ij else 0 := by
    calc
      _ = ∑ ij ∈ (balancedGridCut a b).filter (fun ij => ij ∈ cornerPairs), g ij := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro ij hij hnot
        have hn : ij ∉ cornerPairs := by simpa [Finset.mem_filter, hij] using hnot
        have hh : 2 ≤ ij.1 ∨ 2 ≤ ij.2 := by
          rcases ij with ⟨i, j⟩
          simp only [cornerPairs, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hn
          omega
        simp [g, moebius_grid_high_zero u ij.1 ij.2 hh]
      _ = ∑ ij ∈ cornerPairs.filter (fun ij => ij ∈ balancedGridCut a b), g ij := by
        congr 1
        ext ij
        simp [and_comm]
      _ = _ := by rw [Finset.sum_filter]
  rw [hsum, hsmall]
  unfold cornerPairs
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [g, moebius_rough_two u hu, moebius_rough_three u hu,
    moebius_rough_six u hu, Nat.cast_mul, Int.cast_neg] <;> ring

theorem balancedCut_signal_diagonal (u k : ℕ) (hu : IsTwoThreeRough u) :
    componentSignal (balancedArithmeticCut u (k + 1) (k + 1)) =
      (ArithmeticFunction.moebius u : ℝ) / (3 * (u : ℝ)) := by
  rw [balancedCut_signal_four_terms u (k + 1) (k + 1) hu]
  simp [mem_balancedGridCut]
  have hu0 : (u : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hu.1
  field_simp [hu0] <;> ring

theorem balancedCut_signal_upper_diagonal (u k : ℕ) (hu : IsTwoThreeRough u) :
    componentSignal (balancedArithmeticCut u (k + 2) (k + 1)) =
      (ArithmeticFunction.moebius u : ℝ) / (3 * (u : ℝ)) := by
  rw [balancedCut_signal_four_terms u (k + 2) (k + 1) hu]
  simp [mem_balancedGridCut]
  have hu0 : (u : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hu.1
  field_simp [hu0] <;> ring

theorem balancedCut_signal_root (u : ℕ) (hu : IsTwoThreeRough u) :
    componentSignal (balancedArithmeticCut u 0 0) =
      (ArithmeticFunction.moebius u : ℝ) / (u : ℝ) := by
  rw [balancedCut_signal_four_terms u 0 0 hu]
  simp [mem_balancedGridCut]

theorem balancedCut_signal_two (u : ℕ) (hu : IsTwoThreeRough u) :
    componentSignal (balancedArithmeticCut u 1 0) =
      (ArithmeticFunction.moebius u : ℝ) / (2 * (u : ℝ)) := by
  rw [balancedCut_signal_four_terms u 1 0 hu]
  simp [mem_balancedGridCut]
  have hu0 : (u : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hu.1
  field_simp [hu0] <;> ring

theorem balancedCut_signal_three (u : ℕ) (hu : IsTwoThreeRough u) :
    componentSignal (balancedArithmeticCut u 0 1) =
      -(ArithmeticFunction.moebius u : ℝ) / (3 * (u : ℝ)) := by
  rw [balancedCut_signal_four_terms u 0 1 hu]
  simp [mem_balancedGridCut]

/-- Every off-spine cut except the first triadic edge has zero target. -/
theorem balancedCut_signal_off_spine (u a b : ℕ) (hu : IsTwoThreeRough u)
    (hab : a ≠ b) (hab1 : a ≠ b + 1) (h01 : ¬(a = 0 ∧ b = 1)) :
    componentSignal (balancedArithmeticCut u a b) = 0 := by
  rw [balancedCut_signal_four_terms u a b hu]
  have h00 : (0, 0) ∉ balancedGridCut a b := by
    rw [mem_balancedGridCut]
    omega
  have h10 : (1, 0) ∉ balancedGridCut a b := by
    rw [mem_balancedGridCut]
    omega
  have h11 : (1, 1) ∉ balancedGridCut a b := by
    rw [mem_balancedGridCut]
    omega
  have h01' : (0, 1) ∉ balancedGridCut a b := by
    rw [mem_balancedGridCut]
    omega
  simp [h00, h10, h11, h01']

/-- The nonzero coordinate support is exactly the source's proposed minimal family. -/
theorem balancedCut_signal_ne_zero_iff (u a b : ℕ) (hu : IsTwoThreeRough u) :
    componentSignal (balancedArithmeticCut u a b) ≠ 0 ↔
      ArithmeticFunction.moebius u ≠ 0 ∧
        (a = b ∨ a = b + 1 ∨ (a = 0 ∧ b = 1)) := by
  have hu0 : (u : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hu.1
  by_cases hab : a = b
  · subst a
    cases b with
    | zero =>
      rw [balancedCut_signal_root u hu]
      simp [hu0]
    | succ k =>
      rw [balancedCut_signal_diagonal u k hu]
      simp [hu0]
  · by_cases hab1 : a = b + 1
    · subst a
      cases b with
      | zero =>
        rw [balancedCut_signal_two u hu]
        simp [hu0]
      | succ k =>
        rw [balancedCut_signal_upper_diagonal u k hu]
        simp [hu0]
    · by_cases h01 : a = 0 ∧ b = 1
      · rcases h01 with ⟨rfl, rfl⟩
        rw [balancedCut_signal_three u hu]
        simp [hu0]
      · rw [balancedCut_signal_off_spine u a b hu hab hab1 h01]
        simp [hab, hab1, h01]

end
end RiemannResearch.RH.Pareto
