/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.OrderedPrimitiveAbel
import RiemannResearch.RH.DampedMobiusPrimitiveVariation

/-!
# Natural-order physical pairings of power-damped Möbius sums

This is the ordered Abel step in the attached power-damping handoff.
No Hilbert membership or absolute physical summability is asserted for the
infinite damped approximant. The double-series interchange with the legal
vectors and the actual residual regularity remain separate obligations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto

theorem dampedPhysicalWeight_abs_le {ε c : ℝ} (hε : 0 ≤ ε)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (n : ℕ) (hn : 1 ≤ n) :
    |dampedPhysicalWeight ε c n| ≤ 1 / ((n : ℝ) + 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hA : |dampedPhysicalSum ε c n| ≤ (n : ℝ) :=
    abs_le.mpr (dampedPhysicalSum_bounds hε hc0 hc1 n)
  rw [dampedPhysicalWeight, abs_div,
    abs_of_pos (show 0 < (n : ℝ) * ((n : ℝ) + 1) by positivity)]
  calc
    _ ≤ (n : ℝ) / ((n : ℝ) * ((n : ℝ) + 1)) :=
      div_le_div_of_nonneg_right hA (by positivity)
    _ = _ := by field_simp

/-- Sublinear centered primitives remove the physical endpoint. -/
theorem dampedPhysicalWeight_primitive_boundary
    (H : ℕ → ℝ) {ε c : ℝ} (hε : 0 ≤ ε)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hH : Tendsto (fun N => H N / ((N : ℝ) + 2)) atTop (𝓝 0)) :
    Tendsto (fun N => H N * dampedPhysicalWeight ε c (N + 1))
      atTop (𝓝 0) := by
  have hnorm : Tendsto (fun N => ‖H N / ((N : ℝ) + 2)‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using hH.norm
  apply squeeze_zero_norm _ hnorm
  intro N
  rw [Real.norm_eq_abs, abs_mul]
  have hw : |dampedPhysicalWeight ε c (N + 1)| ≤ 1 / ((N : ℝ) + 2) := by
    simpa only [Nat.cast_add, Nat.cast_one,
      show (N : ℝ) + 1 + 1 = (N : ℝ) + 2 by ring] using
      dampedPhysicalWeight_abs_le hε hc0 hc1 (N + 1) (by omega)
  calc
    _ ≤ |H N| * (1 / ((N : ℝ) + 2)) :=
      mul_le_mul_of_nonneg_left hw (abs_nonneg _)
    _ = ‖H N / ((N : ℝ) + 2)‖ := by
      rw [Real.norm_eq_abs, abs_div,
        abs_of_pos (show 0 < (N : ℝ) + 2 by positivity)]
      ring

/-- The natural-order damped physical pairing exists under the exact
primitive-side majorant already used by the power-damping limit theorem. -/
theorem dampedPhysical_ordered_pairing_tendsto
    (H : ℕ → ℝ) (hzero : H 0 = 0)
    {ε c : ℝ} (hε : 0 ≤ ε) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hH : Summable (fun n : ℕ => |H (n + 1)| *
      (2 / (((n : ℝ) + 2) * ((n : ℝ) + 3)))))
    (hboundary : Tendsto (fun N => H N / ((N : ℝ) + 2)) atTop (𝓝 0)) :
    Tendsto (fun N => ∑ k ∈ Finset.range N,
      (H (k + 1) - H k) * dampedPhysicalWeight ε c (k + 1)) atTop
      (𝓝 (∑' k : ℕ, H (k + 1) *
        (dampedPhysicalWeight ε c (k + 1) -
         dampedPhysicalWeight ε c (k + 2)))) := by
  have hv (k : ℕ) :
      |dampedPhysicalWeight ε c (k + 1) - dampedPhysicalWeight ε c (k + 2)| ≤
        2 / (((k : ℝ) + 2) * ((k : ℝ) + 3)) := by
    rw [abs_sub_comm]
    simpa only [Nat.cast_add, Nat.cast_one,
      show (k : ℝ) + 1 + 1 = (k : ℝ) + 2 by ring,
      show (k : ℝ) + 1 + 2 = (k : ℝ) + 3 by ring,
      show k + 1 + 1 = k + 2 by omega] using
      dampedPhysicalWeight_variation_le hε hc0 hc1 (k + 1) (by omega)
  have ht := RiemannResearch.Analysis.primitive_abel_partialSum_tendsto_of_bound
    H (fun k => dampedPhysicalWeight ε c (k + 1))
    (fun k => 2 / (((k : ℝ) + 2) * ((k : ℝ) + 3))) hH hv
    (dampedPhysicalWeight_primitive_boundary H hε hc0 hc1 hboundary)
  simpa only [hzero, neg_zero, zero_mul, zero_add,
    show ∀ k : ℕ, k + 1 + 1 = k + 2 by omega] using ht

/-- The physical cutoff is removed first for each fixed damping, and only
then is the damping removed. No interchange of these limits is asserted.
The output explicitly records the inner limit, avoiding a `tsum` for a
potentially conditionally convergent physical pairing. -/
theorem dampedPhysical_iterated_ordered_pairing_tendsto
    (H : ℕ → ℝ) (hzero : H 0 = 0) (ε c : ℕ → ℝ)
    (hε : ∀ j, 0 ≤ ε j) (hc0 : ∀ j, 0 ≤ c j) (hc1 : ∀ j, c j ≤ 1)
    (hlim : Tendsto ε atTop (𝓝 0)) (hc : Tendsto c atTop (𝓝 0))
    (hH : Summable (fun n : ℕ => |H (n + 1)| *
      (2 / (((n : ℝ) + 2) * ((n : ℝ) + 3)))))
    (hboundary : Tendsto (fun N => H N / ((N : ℝ) + 2)) atTop (𝓝 0)) :
    (∀ j, Tendsto (fun N => ∑ k ∈ Finset.range N,
      (H (k + 1) - H k) * dampedPhysicalWeight (ε j) (c j) (k + 1)) atTop
      (𝓝 (∑' k : ℕ, H (k + 1) *
        (dampedPhysicalWeight (ε j) (c j) (k + 1) -
         dampedPhysicalWeight (ε j) (c j) (k + 2))))) ∧
    Tendsto (fun j => ∑' k : ℕ, H (k + 1) *
      (dampedPhysicalWeight (ε j) (c j) (k + 1) -
       dampedPhysicalWeight (ε j) (c j) (k + 2))) atTop
      (𝓝 (∑' k : ℕ, H (k + 1) *
        (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) -
         1 / (((k : ℝ) + 2) * ((k : ℝ) + 3))))) := by
  constructor
  · intro j
    exact dampedPhysical_ordered_pairing_tendsto H hzero
      (hε j) (hc0 j) (hc1 j) hH hboundary
  · exact dampedPhysicalPrimitive_pairing_tendsto H ε c hε hc0 hc1 hlim hc hH

/-- Uniform boundary control permits the damping and physical cutoff to vary
simultaneously, with no relation between their rates. -/
theorem dampedPhysicalWeight_diagonal_primitive_boundary
    (H ε c : ℕ → ℝ) (N : ℕ → ℕ)
    (hε : ∀ j, 0 ≤ ε j) (hc0 : ∀ j, 0 ≤ c j) (hc1 : ∀ j, c j ≤ 1)
    (hN : Tendsto N atTop atTop)
    (hH : Tendsto (fun n => H n / ((n : ℝ) + 2)) atTop (𝓝 0)) :
    Tendsto (fun j => H (N j) *
      dampedPhysicalWeight (ε j) (c j) (N j + 1)) atTop (𝓝 0) := by
  have hnorm : Tendsto (fun n => ‖H n / ((n : ℝ) + 2)‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using hH.norm
  apply squeeze_zero_norm _ (hnorm.comp hN)
  intro j
  rw [Real.norm_eq_abs, abs_mul]
  have hw : |dampedPhysicalWeight (ε j) (c j) (N j + 1)| ≤
      1 / ((N j : ℝ) + 2) := by
    simpa only [Nat.cast_add, Nat.cast_one,
      show (N j : ℝ) + 1 + 1 = (N j : ℝ) + 2 by ring] using
      dampedPhysicalWeight_abs_le (hε j) (hc0 j) (hc1 j) (N j + 1) (by omega)
  calc
    _ ≤ |H (N j)| * (1 / ((N j : ℝ) + 2)) :=
      mul_le_mul_of_nonneg_left hw (abs_nonneg _)
    _ = ‖H (N j) / ((N j : ℝ) + 2)‖ := by
      rw [Real.norm_eq_abs, abs_div,
        abs_of_pos (show 0 < (N j : ℝ) + 2 by positivity)]
      ring

/-- Joint scalar pairing convergence along every diverging physical cutoff.
This strengthens the iterated-limit theorem under its existing hypotheses.
The exact primitive-side target is retained, rather than replacing a
possibly conditionally convergent physical series by a `tsum`. -/
theorem dampedPhysical_joint_ordered_pairing_tendsto
    (H : ℕ → ℝ) (hzero : H 0 = 0) (ε c : ℕ → ℝ) (N : ℕ → ℕ)
    (hε : ∀ j, 0 ≤ ε j) (hc0 : ∀ j, 0 ≤ c j) (hc1 : ∀ j, c j ≤ 1)
    (hlim : Tendsto ε atTop (𝓝 0)) (hc : Tendsto c atTop (𝓝 0))
    (hN : Tendsto N atTop atTop)
    (hH : Summable (fun n : ℕ => |H (n + 1)| *
      (2 / (((n : ℝ) + 2) * ((n : ℝ) + 3)))))
    (hboundary : Tendsto (fun n => H n / ((n : ℝ) + 2)) atTop (𝓝 0)) :
    Tendsto (fun j => ∑ k ∈ Finset.range (N j),
      (H (k + 1) - H k) * dampedPhysicalWeight (ε j) (c j) (k + 1)) atTop
      (𝓝 (∑' k : ℕ, H (k + 1) *
        (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) -
         1 / (((k : ℝ) + 2) * ((k : ℝ) + 3))))) := by
  have hv (j k : ℕ) :
      |dampedPhysicalWeight (ε j) (c j) (k + 1) -
        dampedPhysicalWeight (ε j) (c j) (k + 1 + 1)| ≤
      2 / (((k : ℝ) + 2) * ((k : ℝ) + 3)) := by
    rw [abs_sub_comm]
    simpa only [Nat.cast_add, Nat.cast_one,
      show (k : ℝ) + 1 + 1 = (k : ℝ) + 2 by ring,
      show (k : ℝ) + 1 + 2 = (k : ℝ) + 3 by ring] using
        dampedPhysicalWeight_variation_le (hε j) (hc0 j) (hc1 j) (k + 1) (by omega)
  have hp (k : ℕ) : Tendsto
      (fun j => dampedPhysicalWeight (ε j) (c j) (k + 1)) atTop
      (𝓝 (1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)))) := by
    simpa only [Nat.cast_add, Nat.cast_one,
      show (k : ℝ) + 1 + 1 = (k : ℝ) + 2 by ring] using
        dampedPhysicalWeight_tendsto ε c hε hlim hc (k + 1) (by omega)
  have ht := RiemannResearch.Analysis.primitive_abel_diagonal_partialSum_tendsto
    H (fun j k => dampedPhysicalWeight (ε j) (c j) (k + 1))
    (fun k => 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)))
    (fun k => 2 / (((k : ℝ) + 2) * ((k : ℝ) + 3)))
    N hN hH hv hp
    (dampedPhysicalWeight_diagonal_primitive_boundary H ε c N
      hε hc0 hc1 hN hboundary)
  simpa only [hzero, neg_zero, zero_mul, zero_add, Nat.cast_add, Nat.cast_one,
    show ∀ k : ℕ, (k : ℝ) + 1 + 1 = (k : ℝ) + 2 by intro k; ring,
    show ∀ k : ℕ, (k : ℝ) + 1 + 2 = (k : ℝ) + 3 by intro k; ring] using ht

end RiemannResearch.RH.Pareto
