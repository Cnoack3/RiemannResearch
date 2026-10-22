/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.ParetoResidueDuality
import RiemannResearch.RH.ParetoAnchoredGreen

/-!
# Finite Möbius-potential energy

Source: user-provided argument RH_Pareto_CRT_Enlargement_and_Dual_Obstruction_2026-09-07.md,
§9, equations (9.6)-(9.7). The potential is the actual finite sum over
conductors divisible by the coordinate. Genuine Möbius witness coefficients
produce its discrete gradient. The finite weighted energy and the anchored
Laplacian energy agree; the last summand is retained. Reindexing as a sum
over multiples and Möbius inversion over multiples remain separate tasks.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

def mobiusPotential (s : Finset ℕ) (t : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ m ∈ s, if k ∣ m then (ArithmeticFunction.moebius (m/k) : ℝ)*t m else 0

theorem mobiusPotential_difference (s : Finset ℕ) (t : ℕ → ℝ) (k : ℕ) :
    (∑ m ∈ s, t m*(dualCoeff m k : ℝ)) = mobiusPotential s t k - mobiusPotential s t (k+1) := by
  unfold mobiusPotential
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  unfold dualCoeff
  split_ifs <;> push_cast <;> ring

theorem mobiusPotential_boundary (s : Finset ℕ) (t : ℕ → ℝ) (M : ℕ)
    (hs : ∀ m ∈ s, 0 < m ∧ m ≤ M) : mobiusPotential s t (M+1) = 0 := by
  unfold mobiusPotential
  apply Finset.sum_eq_zero
  intro m hm
  have hnot : ¬ M+1 ∣ m := by
    intro h
    have := Nat.le_of_dvd (hs m hm).1 h
    have := (hs m hm).2
    omega
  simp [hnot]

def finiteMobiusRiesz (s : Finset ℕ) (t : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ m ∈ s, t m*(greenWeight k*(dualCoeff m k : ℝ))

theorem finiteMobiusRiesz_eq_gradient (s : Finset ℕ) (t : ℕ → ℝ) (k : ℕ) :
    finiteMobiusRiesz s t k = greenWeight k*(mobiusPotential s t k-mobiusPotential s t (k+1)) := by
  rw [← mobiusPotential_difference, Finset.mul_sum]
  unfold finiteMobiusRiesz
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem mobiusPotential_energy (s : Finset ℕ) (t : ℕ → ℝ) (M : ℕ) :
    (∑ k ∈ Finset.range M, (finiteMobiusRiesz s t (k+1))^2 / greenWeight (k+1)) =
      ∑ k ∈ Finset.range M, greenWeight (k+1)*
        (mobiusPotential s t (k+1)-mobiusPotential s t (k+2))^2 := by
  simp_rw [finiteMobiusRiesz_eq_gradient]
  apply Finset.sum_congr rfl
  intro k _
  have hw : greenWeight (k+1) ≠ 0 := by unfold greenWeight; positivity
  field_simp

theorem mobiusPotential_laplacian_energy (s : Finset ℕ) (t : ℕ → ℝ) (M : ℕ)
    (hs : ∀ m ∈ s, 0 < m ∧ m ≤ M) :
    (∑ k ∈ Finset.range M, mobiusPotential s t (k+1)*
      anchoredLaplacian (mobiusPotential s t) (k+1)) =
        ∑ k ∈ Finset.range M, (finiteMobiusRiesz s t (k+1))^2 / greenWeight (k+1) := by
  rw [anchoredLaplacian_energy M _ (mobiusPotential_boundary s t M hs), mobiusPotential_energy]

end
end RiemannResearch.RH.Pareto
