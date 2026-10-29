/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.AffineEnergyMinimum
import Mathlib.Tactic.Abel
import RiemannResearch.Analysis.CenteredAffineDisplacement
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import RiemannResearch.RH.QFiniteSupportDualCriterion
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Exact-head Q/P energy-minimizer comparison

Source: the attached CRT/Ramanujan/Pareto agenda. The head-dependent centered
multiplier estimate yields a sharp squared displacement comparison. Actual
energy minima supply the normal equations and the exact projected fixed point.
This does not bound the energies of a cofinal family.
-/

noncomputable section
namespace RiemannResearch.RH.QExactHeadOptimizerComparison
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QShiftedReciprocal QFiniteSupportDualCriterion

theorem centered_tail_norm_le (H : ℕ) (f : QHilbert)
    (hf : ∀ n < H, f n = 0) :
    ‖(2 * ((H : ℝ) + 2)) • B f - f‖ ≤ ‖f‖ := by
  have hsq : ‖(2 * ((H : ℝ) + 2)) • B f - f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [qNorm_sq, qNorm_sq]
    apply Summable.tsum_le_tsum _ (qCoordinate_square_summable _)
      (qCoordinate_square_summable _)
    intro n
    change (2 * ((H : ℝ) + 2) * (f n / ((n : ℝ) + 2)) - f n) ^ 2 ≤ (f n) ^ 2
    by_cases hn : n < H
    · simp [hf n hn]
    · have hHn : (H : ℝ) ≤ n := by exact_mod_cast (show H ≤ n by omega)
      have hd : 0 < (n : ℝ) + 2 := by positivity
      have hlo : 0 ≤ (2 * ((H : ℝ) + 2)) / ((n : ℝ) + 2) := by positivity
      have hhi : (2 * ((H : ℝ) + 2)) / ((n : ℝ) + 2) ≤ 2 := by
        apply (div_le_iff₀ hd).mpr
        linarith
      have hc : ((2 * ((H : ℝ) + 2)) / ((n : ℝ) + 2) - 1) ^ 2 ≤ 1 := by
        nlinarith
      have hm := mul_le_mul_of_nonneg_right hc (sq_nonneg (f n))
      convert hm using 1 <;> ring
  nlinarith [norm_nonneg f, norm_nonneg ((2 * ((H : ℝ) + 2)) • B f - f)]

theorem sharp_tail_displacement_bound (H : ℕ) (x d : QHilbert)
    (hx : ∀ n < H, x n = 0) (hd : ∀ n < H, d n = 0)
    (horth : inner ℝ d x = 0)
    (hnormal : inner ℝ d (B (x + d)) = ‖d‖ ^ 2) :
    4 * ((H : ℝ) + 1) * ((H : ℝ) + 2) * ‖d‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  have hsum : ∀ n < H, (x + d) n = 0 := by
    intro n hn
    change x n + d n = 0
    rw [hx n hn, hd n hn, add_zero]
  have hb := RiemannResearch.Analysis.CenteredAffineDisplacement.sharp_displacement_energy_bound
    B ((H : ℝ) + 2) x d horth hnormal (centered_tail_norm_le H (x + d) hsum)
  convert hb using 1 <;> ring

end RiemannResearch.RH.QExactHeadOptimizerComparison



noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QExactHeadOptimizerComparison
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QShiftedReciprocal QFiniteSupportDualCriterion
open RiemannResearch.Analysis.AffineEnergyMinimum

theorem inner_head_zero_of_head_zero (H : ℕ) (u f : QHilbert)
    (hu : ∀ n < H, u n = 0) : inner ℝ u (finiteHead H f) = 0 := by
  rw [inner_finiteHead_eq_sum]
  apply Finset.sum_eq_zero
  intro n hn
  rw [hu n (Finset.mem_range.mp hn), mul_zero]

theorem inner_B_head_zero_of_head_zero (H : ℕ) (u f : QHilbert)
    (hu : ∀ n < H, u n = 0) : inner ℝ u (B (finiteHead H f)) = 0 := by
  rw [← B_symmetric]
  apply inner_head_zero_of_head_zero
  intro n hn
  rw [B_apply, hu n hn, zero_div]

/-- Every actual affine energy minimum satisfies its metric's normal equations.
The hypotheses are the minimization properties themselves, not additional
arithmetic estimates. -/
theorem affine_minimizers_normal_equations
    (U : Submodule ℝ QHilbert) (FQ FP : QHilbert)
    (hQ : ∀ u ∈ U, ‖FQ‖ ^ 2 ≤ ‖FQ + u‖ ^ 2)
    (hP : ∀ u ∈ U, ‖toPareto FP‖ ^ 2 ≤ ‖toPareto (FP + u)‖ ^ 2) :
    (∀ u ∈ U, inner ℝ u FQ = 0) ∧
      (∀ u ∈ U, inner ℝ (toPareto u) (toPareto FP) = 0) := by
  constructor
  · exact (minimum_iff_normal U FQ).mp hQ
  · intro u hu
    apply inner_eq_zero_of_line_minimum (toPareto FP) (toPareto u)
    intro t
    change ‖toParetoLinear FP‖ ^ 2 ≤
      ‖toParetoLinear FP + t • toParetoLinear u‖ ^ 2
    rw [← map_smul, ← map_add]
    exact hP (t • u) (U.smul_mem t hu)

/-- The exact Q and P Pythagorean comparisons between minimizers in a common
affine feasible set. -/
theorem affine_minimizers_pythagoras
    (U : Submodule ℝ QHilbert) (FQ FP : QHilbert)
    (hcoset : FP - FQ ∈ U)
    (hQ : ∀ u ∈ U, ‖FQ‖ ^ 2 ≤ ‖FQ + u‖ ^ 2)
    (hP : ∀ u ∈ U, ‖toPareto FP‖ ^ 2 ≤ ‖toPareto (FP + u)‖ ^ 2) :
    ‖FP‖ ^ 2 = ‖FQ‖ ^ 2 + ‖FP - FQ‖ ^ 2 ∧
      ‖toPareto FQ‖ ^ 2 = ‖toPareto FP‖ ^ 2 + ‖toPareto (FP - FQ)‖ ^ 2 := by
  obtain ⟨hqn, hpn⟩ := affine_minimizers_normal_equations U FQ FP hQ hP
  have hqd := hqn (FP - FQ) hcoset
  have hpd := hpn (FP - FQ) hcoset
  constructor
  · have he : FQ + (FP - FQ) = FP := by abel
    have hp := norm_add_sq_real FQ (FP - FQ)
    rw [he, real_inner_comm, hqd] at hp
    linarith
  · have he : toPareto FQ = toPareto FP - toPareto (FP - FQ) := by
      change toParetoLinear FQ = toParetoLinear FP - toParetoLinear (FP - FQ)
      rw [map_sub]
      abel
    rw [he, norm_sub_sq_real, real_inner_comm, hpd]
    ring

/-- The sharp tail comparison for actual constrained minimizers. The tangent
space can be any submodule whose vectors vanish on the prescribed head; hence
the result applies to every finite legal exact-head feasible set. -/
theorem affine_minimizers_sharp_bound
    (H : ℕ) (U : Submodule ℝ QHilbert) (FQ FP : QHilbert)
    (hU : ∀ u ∈ U, ∀ n < H, u n = 0)
    (hcoset : FP - FQ ∈ U)
    (hQ : ∀ u ∈ U, ‖FQ‖ ^ 2 ≤ ‖FQ + u‖ ^ 2)
    (hP : ∀ u ∈ U, ‖toPareto FP‖ ^ 2 ≤ ‖toPareto (FP + u)‖ ^ 2) :
    4 * ((H : ℝ) + 1) * ((H : ℝ) + 2) * ‖FP - FQ‖ ^ 2 ≤
      ‖FQ - finiteHead H FQ‖ ^ 2 := by
  obtain ⟨hqn, hpn⟩ := affine_minimizers_normal_equations U FQ FP hQ hP
  have hd := hU (FP - FQ) hcoset
  have hqd := hqn (FP - FQ) hcoset
  have hpd := hpn (FP - FQ) hcoset
  have hhead := inner_head_zero_of_head_zero H (FP - FQ) FQ hd
  have hBhead := inner_B_head_zero_of_head_zero H (FP - FQ) FQ hd
  have horth : inner ℝ (FP - FQ) (FQ - finiteHead H FQ) = 0 := by
    rw [inner_sub_right, hqd, hhead, sub_self]
  have hnormal : inner ℝ (FP - FQ)
      (B ((FQ - finiteHead H FQ) + (FP - FQ))) = ‖FP - FQ‖ ^ 2 := by
    have he : (FQ - finiteHead H FQ) + (FP - FQ) = FP - finiteHead H FQ := by abel
    rw [he, map_sub, inner_sub_right, hBhead, sub_zero]
    have hpmetric := pareto_inner_identity (FP - FQ) FP
    rw [hpd] at hpmetric
    have heq : inner ℝ (FP - FQ) FP = inner ℝ (FP - FQ) (B FP) := by
      have hz : inner ℝ (FP - FQ) FP - inner ℝ (FP - FQ) (B FP) = 0 :=
        (mul_eq_zero.mp hpmetric.symm).resolve_left (ne_of_gt zetaTwo_pos)
      exact sub_eq_zero.mp hz
    have hself : inner ℝ (FP - FQ) (FP - FQ) = ‖FP - FQ‖ ^ 2 :=
      real_inner_self_eq_norm_sq _
    rw [inner_sub_right, hqd, sub_zero] at hself
    rw [← heq]
    exact hself
  apply sharp_tail_displacement_bound H (FQ - finiteHead H FQ) (FP - FQ) _ hd horth hnormal
  intro n hn
  change FQ n - finiteHead H FQ n = 0
  rw [finiteHead_apply_of_lt H FQ n hn, sub_self]

/-- Any feasible comparison vector supplies a complete-energy upper bound for
the displacement. No bound on an unconstructed minimizer is assumed. -/
theorem affine_minimizers_bound_of_competitor
    (H : ℕ) (U : Submodule ℝ QHilbert) (FQ FP C : QHilbert)
    (hU : ∀ u ∈ U, ∀ n < H, u n = 0)
    (hcoset : FP - FQ ∈ U) (hC : C - FQ ∈ U)
    (hQ : ∀ u ∈ U, ‖FQ‖ ^ 2 ≤ ‖FQ + u‖ ^ 2)
    (hP : ∀ u ∈ U, ‖toPareto FP‖ ^ 2 ≤ ‖toPareto (FP + u)‖ ^ 2) :
    4 * ((H : ℝ) + 1) * ((H : ℝ) + 2) * ‖FP - FQ‖ ^ 2 ≤ ‖C‖ ^ 2 := by
  have hs := affine_minimizers_sharp_bound H U FQ FP hU hcoset hQ hP
  have hmin := hQ (C - FQ) hC
  have he : FQ + (C - FQ) = C := by abel
  rw [he] at hmin
  have hsplit := finiteHead_norm_sq_split H FQ
  nlinarith [sq_nonneg ‖finiteHead H FQ‖]

/-- The displacement satisfies the exact compressed fixed-point equation on
the common zero-head tangent space. -/
theorem affine_minimizers_fixed_point
    (H : ℕ) (U : Submodule ℝ QHilbert) [U.HasOrthogonalProjection]
    (FQ FP : QHilbert)
    (hU : ∀ u ∈ U, ∀ n < H, u n = 0)
    (hcoset : FP - FQ ∈ U)
    (hQ : ∀ u ∈ U, ‖FQ‖ ^ 2 ≤ ‖FQ + u‖ ^ 2)
    (hP : ∀ u ∈ U, ‖toPareto FP‖ ^ 2 ≤ ‖toPareto (FP + u)‖ ^ 2) :
    FP - FQ = U.starProjection (B ((FQ - finiteHead H FQ) + (FP - FQ))) := by
  obtain ⟨hqn, hpn⟩ := affine_minimizers_normal_equations U FQ FP hQ hP
  let y := B ((FQ - finiteHead H FQ) + (FP - FQ))
  have htest : ∀ u ∈ U, inner ℝ u (FP - FQ) = inner ℝ u y := by
    intro u hu
    have hq := hqn u hu
    have hp := hpn u hu
    have hBhead := inner_B_head_zero_of_head_zero H u FQ (hU u hu)
    have he : (FQ - finiteHead H FQ) + (FP - FQ) = FP - finiteHead H FQ := by abel
    dsimp only [y]
    rw [he, map_sub]
    simp only [inner_sub_right, hq, hBhead, sub_zero]
    rw [pareto_inner_identity] at hp
    exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left (ne_of_gt zetaTwo_pos))
  let z := (FP - FQ) - U.starProjection y
  have hz : z ∈ U := U.sub_mem hcoset (U.starProjection_apply_mem y)
  have hp := Submodule.inner_right_of_mem_orthogonal hz
    (Submodule.sub_starProjection_mem_orthogonal (K := U) y)
  have hzero : inner ℝ z z = 0 := by
    change inner ℝ z ((FP - FQ) - U.starProjection y) = 0
    rw [inner_sub_right, htest z hz]
    simpa only [inner_sub_right] using hp
  have hzn : ‖z‖ = 0 := by
    rw [real_inner_self_eq_norm_sq] at hzero
    nlinarith [norm_nonneg z]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzn)

theorem affine_minimizers_response_equation
    (H : ℕ) (U : Submodule ℝ QHilbert) [U.HasOrthogonalProjection]
    (FQ FP : QHilbert)
    (hU : ∀ u ∈ U, ∀ n < H, u n = 0)
    (hcoset : FP - FQ ∈ U)
    (hQ : ∀ u ∈ U, ‖FQ‖ ^ 2 ≤ ‖FQ + u‖ ^ 2)
    (hP : ∀ u ∈ U, ‖toPareto FP‖ ^ 2 ≤ ‖toPareto (FP + u)‖ ^ 2) :
    FP - FQ = U.starProjection (B (FQ - finiteHead H FQ)) +
      U.starProjection (B (FP - FQ)) := by
  simpa only [map_add] using affine_minimizers_fixed_point H U FQ FP hU hcoset hQ hP

end RiemannResearch.RH.QExactHeadOptimizerComparison
