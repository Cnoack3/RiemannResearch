/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Anchored Green inverse action and exact energy

Source: user-provided argument RH_Pareto_CRT_Enlargement_and_Dual_Obstruction_2026-09-07.md,
§9, equations (9.1)-(9.3). The inverse is formalized as a discrete operator:
the genuine max-kernel solves every finite Dirichlet problem, with right
boundary zero. Its expanded tridiagonal action has diagonal 2 i^2 and
neighbor weights -i(i+1). The energy identity first retains the right
boundary flux and only removes it under the explicit zero-boundary hypothesis.
No Matrix.inv API or infinite-dimensional closure claim is made.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

def anchoredGreen (M i j : ℕ) : ℝ := 1 / (max i j : ℕ) - 1 / ((M : ℝ)+1)
def greenWeight (i : ℕ) : ℝ := (i : ℝ)*(i+1)
def anchoredLaplacian (f : ℕ → ℝ) (i : ℕ) : ℝ :=
  greenWeight i * (f i-f (i+1)) - greenWeight (i-1) * (f (i-1)-f i)

theorem anchoredGreen_boundary (M j : ℕ) (hj : j ≤ M+1) :
    anchoredGreen M (M+1) j = 0 := by
  simp [anchoredGreen, max_eq_left hj]

theorem anchoredGreen_flux (M i j : ℕ) (hi : 0 < i) :
    greenWeight i * (anchoredGreen M i j - anchoredGreen M (i+1) j) =
      if j ≤ i then 1 else 0 := by
  by_cases hj : j ≤ i
  · rw [if_pos hj]
    simp only [anchoredGreen, max_eq_left hj, max_eq_left (show j ≤ i+1 by omega)]
    unfold greenWeight
    push_cast
    have hi0 : (i : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hi)
    have hi1 : (i : ℝ)+1 ≠ 0 := by positivity
    field_simp
    ring
  · have hj' : i+1 ≤ j := by omega
    simp [anchoredGreen, hj, max_eq_right (show i ≤ j by omega), max_eq_right hj']

theorem anchoredGreen_inverse (M i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
    anchoredLaplacian (fun k => anchoredGreen M k j) i =
      if i = j then 1 else 0 := by
  unfold anchoredLaplacian
  rw [anchoredGreen_flux M i j hi]
  by_cases h1 : i = 1
  · subst i
    simp only [Nat.sub_self, greenWeight, Nat.cast_zero, zero_mul, sub_zero]
    by_cases he : 1 = j
    · subst j; norm_num
    · have hnot : ¬ j ≤ 1 := by omega
      simp [he, hnot]
  · have hp : 0 < i-1 := by omega
    have hprev : greenWeight (i-1) *
        (anchoredGreen M (i-1) j - anchoredGreen M i j) =
          if j ≤ i-1 then 1 else 0 := by
      simpa only [Nat.sub_add_cancel (show 1 ≤ i by omega)] using
        anchoredGreen_flux M (i-1) j hp
    rw [hprev]
    by_cases he : i = j
    · subst j
      simp [show ¬ i ≤ i-1 by omega]
    · by_cases hle : j ≤ i
      · simp [hle, show j ≤ i-1 by omega, he]
      · simp [hle, show ¬ j ≤ i-1 by omega, he]

theorem anchoredLaplacian_tridiagonal (f : ℕ → ℝ) (i : ℕ) (hi : 0 < i) :
    anchoredLaplacian f i = 2*(i:ℝ)^2*f i -
      ((i:ℝ)-1)*i*f (i-1) - (i:ℝ)*(i+1)*f (i+1) := by
  unfold anchoredLaplacian greenWeight
  rw [Nat.cast_sub (show 1 ≤ i by omega)]
  push_cast
  ring

theorem anchoredLaplacian_energy_with_boundary (M : ℕ) (a : ℕ → ℝ) :
    (∑ k ∈ Finset.range M, a (k+1)*anchoredLaplacian a (k+1)) =
      (∑ k ∈ Finset.range M, greenWeight (k+1)*(a (k+1)-a (k+2))^2) +
        greenWeight M*(a M-a (M+1))*a (M+1) := by
  induction M with
  | zero => simp [greenWeight]
  | succ M ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
    simp only [anchoredLaplacian, Nat.add_sub_cancel]
    ring

theorem anchoredLaplacian_energy (M : ℕ) (a : ℕ → ℝ) (hboundary : a (M+1) = 0) :
    (∑ k ∈ Finset.range M, a (k+1)*anchoredLaplacian a (k+1)) =
      ∑ k ∈ Finset.range M, greenWeight (k+1)*(a (k+1)-a (k+2))^2 := by
  rw [anchoredLaplacian_energy_with_boundary, hboundary]
  ring

theorem anchoredLaplacian_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (f : ι → ℕ → ℝ) (i : ℕ) :
    anchoredLaplacian (fun k => ∑ j ∈ s, c j*f j k) i =
      ∑ j ∈ s, c j*anchoredLaplacian (f j) i := by
  unfold anchoredLaplacian
  simp_rw [← Finset.sum_sub_distrib, ← mul_sub, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

def anchoredGreenSolution (M : ℕ) (b : Fin M → ℝ) (k : ℕ) : ℝ :=
  ∑ j, b j*anchoredGreen M k (j.val+1)

theorem anchoredGreenSolution_boundary (M : ℕ) (b : Fin M → ℝ) :
    anchoredGreenSolution M b (M+1) = 0 := by
  unfold anchoredGreenSolution
  apply Finset.sum_eq_zero
  intro j _
  rw [anchoredGreen_boundary M (j.val+1) (by omega), mul_zero]

theorem anchoredGreen_solves_dirichlet (M : ℕ) (b : Fin M → ℝ) (i : Fin M) :
    anchoredLaplacian (anchoredGreenSolution M b) (i.val+1) = b i := by
  unfold anchoredGreenSolution
  rw [anchoredLaplacian_sum]
  have h (j : Fin M) := anchoredGreen_inverse M (i.val+1) (j.val+1)
    (Nat.zero_lt_succ _) (Nat.zero_lt_succ _)
  simp_rw [h]
  have he (j : Fin M) : (i.val+1 = j.val+1) ↔ i = j := by
    simp [Fin.ext_iff]
  simp_rw [he, mul_ite, mul_one, mul_zero]
  simp

end
end RiemannResearch.RH.Pareto
