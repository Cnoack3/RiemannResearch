/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoPolygammaResidues
import RiemannResearch.Analysis.PeriodicWeightedMean
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-!
# Complete inverse-square residue-weight enclosures

Source: user-provided Minimum_Energy_Exact_Head_Research_Agenda_2026-10-28.md,
priority 3 (statements and proposed certification strategy). The proof uses
finite telescoping identities and their limits instead of an integral API.
The exact shifted progression tail is retained before either bound is applied.
No asymptotic or arithmetic RH provider is assumed.
-/

open Filter
open scoped BigOperators Topology
noncomputable section
namespace RiemannResearch.RH.ZetaTwoProbability
open RiemannResearch.Analysis.PeriodicWeightedMean

theorem residueSquareWeight_integral_lower {L a : ℝ} (hL : 0 < L) (ha : 0 < a) :
    1 / (zetaTwo * L * a) ≤ residuePowerWeight 0 L a := by
  let u : ℕ → ℝ := fun n => 1 / (zetaTwo * L * (a + (n : ℝ) * L))
  have hz := zetaTwo_pos
  have hstep (n : ℕ) :
      u n - u (n + 1) ≤ 1 / (zetaTwo * (a + (n : ℝ) * L) ^ 2) := by
    have hx : 0 < a + (n : ℝ) * L := by positivity
    have hid : u n - u (n + 1) =
        1 / (zetaTwo * (a + (n : ℝ) * L) * (a + (n : ℝ) * L + L)) := by
      dsimp [u]
      push_cast
      field_simp
      <;> ring
    rw [hid]
    apply one_div_le_one_div_of_le (by positivity)
    calc
      _ = (zetaTwo * (a + (n : ℝ) * L)) * (a + (n : ℝ) * L) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hsum (n : ℕ) : u 0 - u n ≤ residuePowerWeight 0 L a := by
    calc
      _ = ∑ k ∈ Finset.range n, (u k - u (k + 1)) := (telescoping_weights u n).symm
      _ ≤ ∑ k ∈ Finset.range n, 1 / (zetaTwo * (a + (k : ℝ) * L) ^ 2) :=
        Finset.sum_le_sum (fun k _ => hstep k)
      _ ≤ _ := (residuePowerWeight_summable 0 hL ha).sum_le_tsum _
        (fun k _ => by positivity)
  have hi : Tendsto (fun n : ℕ => a + (n : ℝ) * L) atTop atTop :=
    tendsto_atTop_mono (fun n => le_add_of_nonneg_left ha.le)
      (tendsto_natCast_atTop_atTop.atTop_mul_const hL)
  have hu : Tendsto u atTop (𝓝 0) := by
    have h := (hi.const_div_atTop 1).const_mul (1 / (zetaTwo * L))
    simpa [u, mul_assoc, mul_comm, mul_left_comm, div_eq_mul_inv] using h
  have h := le_of_tendsto' (hu.const_sub (u 0)) hsum
  simpa [u] using h

theorem residueSquareWeight_integral_upper {L a : ℝ} (hL : 0 < L) (ha : 0 < a) :
    residuePowerWeight 0 L (a + L) ≤ 1 / (zetaTwo * L * a) := by
  let u : ℕ → ℝ := fun n => 1 / (zetaTwo * L * (a + (n : ℝ) * L))
  have hz := zetaTwo_pos
  have hstep (n : ℕ) :
      1 / (zetaTwo * (a + L + (n : ℝ) * L) ^ 2) ≤ u n - u (n + 1) := by
    have hx : 0 < a + (n : ℝ) * L := by positivity
    have hid : u n - u (n + 1) =
        1 / (zetaTwo * (a + (n : ℝ) * L) * (a + (n : ℝ) * L + L)) := by
      dsimp [u]
      push_cast
      field_simp
      <;> ring
    rw [hid]
    apply one_div_le_one_div_of_le (by positivity)
    calc
      _ ≤ zetaTwo * (a + (n : ℝ) * L + L) * (a + (n : ℝ) * L + L) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) hz.le) (by positivity)
      _ = _ := by ring
  apply (residuePowerWeight_summable 0 hL (by positivity : 0 < a + L)).tsum_le_of_sum_range_le
  intro n
  calc
    _ ≤ ∑ k ∈ Finset.range n, (u k - u (k + 1)) :=
      Finset.sum_le_sum (fun k _ => hstep k)
    _ = u 0 - u n := telescoping_weights u n
    _ ≤ _ := by
      have hu : 0 ≤ u n := by dsimp [u]; positivity
      simpa [u] using sub_le_self (u 0) hu

theorem residueSquareWeight_prefix_bounds {L a : ℝ} (hL : 0 < L) (ha : 0 < a)
    (K : ℕ) :
    (∑ k ∈ Finset.range (K + 1), 1 / (zetaTwo * (a + (k : ℝ) * L) ^ 2)) +
        1 / (zetaTwo * L * (a + (K + 1 : ℝ) * L)) ≤ residuePowerWeight 0 L a ∧
    residuePowerWeight 0 L a ≤
      (∑ k ∈ Finset.range (K + 1), 1 / (zetaTwo * (a + (k : ℝ) * L) ^ 2)) +
        1 / (zetaTwo * L * (a + (K : ℝ) * L)) := by
  rw [residuePowerWeight_prefix_exact 0 hL ha (K + 1)]
  simp only [Nat.zero_add, Nat.cast_add, Nat.cast_one]
  constructor
  · exact add_le_add le_rfl (residueSquareWeight_integral_lower
      (a := a + ((K : ℝ) + 1) * L) hL (by positivity))
  · have he : a + ((K : ℝ) + 1) * L = (a + (K : ℝ) * L) + L := by ring
    rw [he]
    exact add_le_add le_rfl (residueSquareWeight_integral_upper
      (a := a + (K : ℝ) * L) hL (by positivity))

/-- Exact periodic energy after a finite prefix in each residue class.
The remaining term is still the complete shifted progression mass. -/
theorem periodic_square_prefix_exact (L : ℕ) (hL : 0 < L) (R : ℕ → ℝ)
    {C : ℝ} (hR : ∀ n, |R n| ≤ C) (hp : ∀ n, R (n + L) = R n)
    (K : ℕ) :
    inversePowerMean 0 (fun n => R n ^ 2) =
      ∑ r : Fin L,
        ((∑ k ∈ Finset.range (K + 1),
          1 / (zetaTwo * ((r.val : ℝ) + 1 + (k : ℝ) * L) ^ 2)) +
          residuePowerWeight 0 L ((r.val : ℝ) + 1 + (K + 1 : ℝ) * L)) * R (r.val + 1) ^ 2 := by
  have hC : 0 ≤ C := (abs_nonneg (R 0)).trans (hR 0)
  have hsq : ∀ n, |R n ^ 2| ≤ C ^ 2 := by
    intro n
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [abs_le.mp (hR n)]
  rw [periodic_inversePowerMean 0 L hL _ hsq (by intro n; rw [hp])]
  apply Finset.sum_congr rfl
  intro r _
  rw [residuePowerWeight_prefix_exact 0 (by exact_mod_cast hL) (by positivity) (K + 1)]
  simp only [Nat.zero_add, Nat.cast_add, Nat.cast_one]

/-- Finite rational-expression enclosures include every omitted Q atom. -/
theorem periodic_square_prefix_bounds (L : ℕ) (hL : 0 < L) (R : ℕ → ℝ)
    {C : ℝ} (hR : ∀ n, |R n| ≤ C) (hp : ∀ n, R (n + L) = R n)
    (K : ℕ) :
    (∑ r : Fin L,
      ((∑ k ∈ Finset.range (K + 1),
        1 / (zetaTwo * ((r.val : ℝ) + 1 + (k : ℝ) * L) ^ 2)) +
        1 / (zetaTwo * L * ((r.val : ℝ) + 1 + (K + 1 : ℝ) * L))) * R (r.val + 1) ^ 2) ≤
      inversePowerMean 0 (fun n => R n ^ 2) ∧
    inversePowerMean 0 (fun n => R n ^ 2) ≤
      ∑ r : Fin L,
      ((∑ k ∈ Finset.range (K + 1),
        1 / (zetaTwo * ((r.val : ℝ) + 1 + (k : ℝ) * L) ^ 2)) +
        1 / (zetaTwo * L * ((r.val : ℝ) + 1 + (K : ℝ) * L))) * R (r.val + 1) ^ 2 := by
  have hC : 0 ≤ C := (abs_nonneg (R 0)).trans (hR 0)
  have hsq : ∀ n, |R n ^ 2| ≤ C ^ 2 := by
    intro n
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [abs_le.mp (hR n)]
  rw [periodic_inversePowerMean 0 L hL _ hsq (by intro n; rw [hp])]
  constructor
  · apply Finset.sum_le_sum
    intro r _
    exact mul_le_mul_of_nonneg_right
      (residueSquareWeight_prefix_bounds (by exact_mod_cast hL) (by positivity) K).1
      (sq_nonneg _)
  · apply Finset.sum_le_sum
    intro r _
    exact mul_le_mul_of_nonneg_right
      (residueSquareWeight_prefix_bounds (by exact_mod_cast hL) (by positivity) K).2
      (sq_nonneg _)

end RiemannResearch.RH.ZetaTwoProbability
