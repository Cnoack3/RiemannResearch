/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Sparse coercivity and collective cancellation

Source: user-provided argument, RH layer-cake continuation, sections 33--35 and
39 (September 2026). This module verifies finite-dimensional algebra only.
Its concrete RH consumer is the nested hat-function Gram-matrix program.

The actual uniform prime/archimedean entry estimate, the actual hat mass-matrix
bound, and identification with the completed Weil form are NOT proved here.
They occur as explicit hypotheses of the application theorem. The collective
identities likewise require exact refinement to supply preservation of the
form and mass. No RH assertion follows from these finite-dimensional facts.
-/

namespace RiemannResearch.LinearAlgebra

open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι]

/-- The complex sesquilinear expression, with conjugation in its first slot. -/
def complexFiniteQuadratic (Z : ι → ι → ℂ) (c : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, star (c i) * Z i j * c j

/-- The squared coefficient norm used in the effective coefficient count. -/
def coefficientSquareMass (c : ι → ℂ) : ℝ := ∑ i, ‖c i‖ ^ 2

/-- Defined for all vectors; the coercivity theorem assumes a nonzero vector. -/
def effectiveCoefficientCount (c : ι → ℂ) : ℝ :=
  (∑ i, ‖c i‖) ^ 2 / coefficientSquareMass c

theorem effectiveCoefficientCount_nonneg (c : ι → ℂ) :
    0 ≤ effectiveCoefficientCount c := by
  unfold effectiveCoefficientCount coefficientSquareMass
  positivity

/-- Complex entrywise bounds control the full signed quadratic expression. -/
theorem norm_complexFiniteQuadratic_le (Z : ι → ι → ℂ) (c : ι → ℂ)
    {b : ℝ} (hZ : ∀ i j, ‖Z i j‖ ≤ b) :
    ‖complexFiniteQuadratic Z c‖ ≤ b * (∑ i, ‖c i‖) ^ 2 := by
  unfold complexFiniteQuadratic
  calc
    _ ≤ ∑ i, ∑ j, ‖star (c i) * Z i j * c j‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
    _ ≤ ∑ i, ∑ j, ‖c i‖ * b * ‖c j‖ := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      simp only [norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hZ i j) (norm_nonneg _)) (norm_nonneg _)
    _ = _ := by
      simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
      ring

theorem abs_re_complexFiniteQuadratic_le (Z : ι → ι → ℂ) (c : ι → ℂ)
    {b : ℝ} (hZ : ∀ i j, ‖Z i j‖ ≤ b) :
    |(complexFiniteQuadratic Z c).re| ≤ b * (∑ i, ‖c i‖) ^ 2 :=
  (Complex.abs_re_le_norm _).trans (norm_complexFiniteQuadratic_le Z c hZ)

/-- On a chosen finite collection of coefficients, the effective count does not
exceed the size of that collection. One may index just the nonzero coefficients. -/
theorem effectiveCoefficientCount_le_card (c : ι → ℂ)
    (hc : 0 < coefficientSquareMass c) :
    effectiveCoefficientCount c ≤ (Fintype.card ι : ℝ) := by
  unfold effectiveCoefficientCount
  apply (div_le_iff₀ hc).2
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : ι => ‖c i‖) (fun _ : ι => (1 : ℝ))
  simpa [coefficientSquareMass, mul_comm] using h

/-- Section 34's coercivity implication. The substantive analytic inputs remain
visible: `hZ` is the uniform entry estimate and `hmass` is the hat mass bound.
No Hermitian assumption is needed because the conclusion concerns real parts. -/
theorem sparse_coercivity_of_entrywise_bound
    (Z : ι → ι → ℂ) (c : ι → ℂ) {C h ell mass q : ℝ}
    (hC : 0 ≤ C) (hc : 0 < coefficientSquareMass c)
    (hZ : ∀ i j, ‖Z i j‖ ≤ C * h)
    (hmass : h / 3 * coefficientSquareMass c ≤ mass)
    (hdecomp : q = ell * mass + (complexFiniteQuadratic Z c).re) :
    (ell - 3 * C * effectiveCoefficientCount c) * mass ≤ q := by
  have heff := effectiveCoefficientCount_nonneg c
  have heq : effectiveCoefficientCount c * coefficientSquareMass c =
      (∑ i, ‖c i‖) ^ 2 := by
    unfold effectiveCoefficientCount
    exact div_mul_cancel₀ _ (ne_of_gt hc)
  have hm : h * coefficientSquareMass c ≤ 3 * mass := by linarith
  have hmul := mul_le_mul_of_nonneg_left hm (mul_nonneg hC heff)
  have hb : C * h * (∑ i, ‖c i‖) ^ 2 ≤
      3 * C * effectiveCoefficientCount c * mass := by
    calc
      _ = C * effectiveCoefficientCount c * (h * coefficientSquareMass c) := by
        rw [← heq]
        ring
      _ ≤ _ := by nlinarith [hmul]
  have hz := (abs_le.mp (abs_re_complexFiniteQuadratic_le Z c hZ)).1
  nlinarith [hdecomp]

/-- A concrete cardinality condition gives half of the leading coercive term. -/
theorem sparse_half_coercivity_of_card
    (Z : ι → ι → ℂ) (c : ι → ℂ) {C h ell mass q : ℝ}
    (hC : 0 ≤ C) (hh : 0 ≤ h) (hc : 0 < coefficientSquareMass c)
    (hZ : ∀ i j, ‖Z i j‖ ≤ C * h)
    (hmass : h / 3 * coefficientSquareMass c ≤ mass)
    (hdecomp : q = ell * mass + (complexFiniteQuadratic Z c).re)
    (hcard : 6 * C * (Fintype.card ι : ℝ) ≤ ell) :
    ell / 2 * mass ≤ q := by
  have hm : 0 ≤ mass :=
    (mul_nonneg (div_nonneg hh (by norm_num)) (le_of_lt hc)).trans hmass
  have heff := effectiveCoefficientCount_le_card c hc
  have hmul := mul_le_mul_of_nonneg_left heff (by positivity : 0 ≤ 3 * C)
  have hcoef : ell / 2 ≤ ell - 3 * C * effectiveCoefficientCount c := by
    linarith
  exact (mul_le_mul_of_nonneg_right hcoef hm).trans
    (sparse_coercivity_of_entrywise_bound Z c hC hc hZ hmass hdecomp)

/-- Any genuinely negative direction must exceed the effective-count threshold. -/
theorem effective_count_large_of_negative
    {ell C mass q effective : ℝ} (hC : 0 < C) (hm : 0 ≤ mass)
    (hlower : (ell - 3 * C * effective) * mass ≤ q) (hq : q < 0) :
    ell / (3 * C) < effective := by
  have hcoef : ell - 3 * C * effective < 0 := by
    by_contra hn
    have hh : 0 ≤ ell - 3 * C * effective := le_of_not_gt hn
    have hp := mul_nonneg hh hm
    linarith
  apply (div_lt_iff₀ (by positivity : 0 < 3 * C)).2
  nlinarith

/-- Exact refinement gives this identity by preserving `q` and `mass`.
It explains why a bounded entry error need not give a bounded normalized error. -/
theorem normalized_remainder_of_decomposition {ell mass q z : ℝ}
    (hm : mass ≠ 0) (hq : q = ell * mass + z) :
    z / mass = -ell + q / mass := by
  field_simp [hm]
  nlinarith [hq]

/-- If the artificial leading scale grows without bound and a nonzero vector is
preserved exactly, its normalized remainder has no uniform lower bound. -/
theorem normalized_remainder_unbounded_below
    (ell z : ℕ → ℝ) {mass q : ℝ} (hm : mass ≠ 0)
    (hq : ∀ j, q = ell j * mass + z j)
    (hell : ∀ B : ℝ, ∃ j, B < ell j) :
    ∀ B : ℝ, ∃ j, z j / mass < B := by
  intro B
  obtain ⟨j, hj⟩ := hell (q / mass - B)
  refine ⟨j, ?_⟩
  rw [normalized_remainder_of_decomposition hm (hq j)]
  linarith

/-- The corresponding mesh-normalized Rayleigh expression is exactly `1-r/ell`.
This is an identity of a specified direction, not a spectral theorem. -/
theorem mesh_normalized_remainder {ell mass q z : ℝ}
    (he : ell ≠ 0) (hm : mass ≠ 0) (hq : q = ell * mass + z) :
    -(z / mass) / ell = 1 - (q / mass) / ell := by
  rw [normalized_remainder_of_decomposition hm hq]
  field_simp [he, hm]
  ring

/-- In particular these Rayleigh expressions cannot all be below `1-delta`.
The spectral corollary additionally needs the actual operator/Rayleigh linkage. -/
theorem mesh_normalized_no_uniform_gap
    (ell z : ℕ → ℝ) {mass q delta : ℝ} (hm : mass ≠ 0)
    (hq : ∀ j, q = ell j * mass + z j)
    (hell : ∀ B : ℝ, ∃ j, B < ell j) (hd : 0 < delta) :
    ∃ j, 0 < ell j ∧ 1 - delta < -(z j / mass) / ell j := by
  obtain ⟨j, hj⟩ := hell (max 0 ((q / mass) / delta))
  have he : 0 < ell j := lt_of_le_of_lt (le_max_left _ _) hj
  have hqdiv : (q / mass) / delta < ell j :=
    lt_of_le_of_lt (le_max_right _ _) hj
  have hqmul : q / mass < ell j * delta := (div_lt_iff₀ hd).1 hqdiv
  have hsmall : (q / mass) / ell j < delta := by
    apply (div_lt_iff₀ he).2
    simpa [mul_comm] using hqmul
  refine ⟨j, he, ?_⟩
  rw [mesh_normalized_remainder (ne_of_gt he) hm (hq j)]
  linarith

/-- The effective-count formula once the two elementary refinement moments
`sum alpha = N` and `sum alpha^2 = (2*N^2+1)/(3*N)` have been supplied. -/
theorem coarse_hat_effective_count_algebra {N : ℝ} (hN : 0 < N) :
    N ^ 2 / ((2 * N ^ 2 + 1) / (3 * N)) = 3 * N ^ 3 / (2 * N ^ 2 + 1) := by
  have hden : 2 * N ^ 2 + 1 ≠ 0 := by positivity
  field_simp [ne_of_gt hN, hden]

/-- Thus the exact coarse-hat effective count is at least the refinement ratio,
which is much larger than a logarithmic sparse threshold at fine scales. -/
theorem coarse_hat_effective_count_ge_refinement {N : ℝ} (hN : 1 ≤ N) :
    N ≤ 3 * N ^ 3 / (2 * N ^ 2 + 1) := by
  have hd : 0 < 2 * N ^ 2 + 1 := by positivity
  apply (le_div_iff₀ hd).2
  nlinarith [mul_nonneg (by linarith : 0 ≤ N) (by nlinarith : 0 ≤ N ^ 2 - 1)]

end
end RiemannResearch.LinearAlgebra
