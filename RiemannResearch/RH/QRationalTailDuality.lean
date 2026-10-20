/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteClassDirichlet
import RiemannResearch.RH.QRationalTailPoincare
import RiemannResearch.RH.QRationalCoprimeMinimum
import RiemannResearch.RH.QRationalMinimumLimit
import RiemannResearch.RH.QRationalCoprimeLegality
import RiemannResearch.RH.ArithmeticCumulativeBasic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sharp finite dual problem for the endpoint-removed rational minimum

Source: direct finite weighted square completion, developed for the
user-directed signed-tail investigation, 20 October 2026. Admissibility
is the exact full-divisor homogeneous normal system. Its optimal dual
constant equals the original remaining energy; it is not an independent
arithmetic decay estimate.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QRationalCoprimeTail
open RiemannResearch.Analysis.FiniteClassDirichlet
open ArithmeticCumulative

def tailDualAdmissible (L : ℕ) (x : ℕ → ℝ) : Prop :=
  ∀ d ∈ L.divisors,
    (∑ a ∈ (sites L).erase L, weight L a * x a * residueFraction d a) = 0

def tailDualMass (L : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ a ∈ (sites L).erase L, weight L a * x a

def tailDualEnergy (L : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ a ∈ (sites L).erase L, weight L a * x a ^ 2

theorem actual_residual_tailDualAdmissible (L : ℕ) (hL : 0 < L) :
    tailDualAdmissible L (fun a => 1 - divisorFit L (rationalCoefficients L) a) := by
  intro d hd
  have he := Finset.sum_erase_add (s := sites L)
    (f := fun a => weight L a * (1 - divisorFit L (rationalCoefficients L) a) *
      residueFraction d a) (Finset.mem_Icc.mpr ⟨hL, le_rfl⟩)
  have hz : residueFraction d L = 0 := by
    simp [residueFraction, Nat.mod_eq_zero_of_dvd (Nat.dvd_of_mem_divisors hd)]
  rw [hz, mul_zero, add_zero, rationalCoefficients_normal L d hd] at he
  exact he

theorem tailDual_cross (L : ℕ) (x : ℕ → ℝ) (hx : tailDualAdmissible L x) :
    (∑ a ∈ (sites L).erase L,
      weight L a * (1 - divisorFit L (rationalCoefficients L) a) * x a) =
      tailDualMass L x := by
  have hz : (∑ a ∈ (sites L).erase L,
      weight L a * x a * divisorFit L (rationalCoefficients L) a) = 0 := by
    calc
      _ = ∑ d ∈ L.divisors, rationalCoefficients L d *
          ∑ a ∈ (sites L).erase L, weight L a * x a * residueFraction d a := by
        simp only [divisorFit, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro d hd
        apply Finset.sum_congr rfl
        intro a ha
        ring
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro d hd
        rw [hx d hd, mul_zero]
  have he : (∑ a ∈ (sites L).erase L,
      weight L a * (1 - divisorFit L (rationalCoefficients L) a) * x a) =
      tailDualMass L x - (∑ a ∈ (sites L).erase L,
        weight L a * x a * divisorFit L (rationalCoefficients L) a) := by
    unfold tailDualMass
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    ring
  rw [he, hz, sub_zero]

/-- The full nonnegative dual gap, with the endpoint removed exactly. -/
theorem rational_tail_dual_gap (L : ℕ) (hL : 0 < L)
    (x : ℕ → ℝ) (hx : tailDualAdmissible L x) :
    rationalMinimum L - commonAverage L -
        (2 * tailDualMass L x - tailDualEnergy L x) =
      ∑ a ∈ (sites L).erase L, weight L a *
        (1 - divisorFit L (rationalCoefficients L) a - x a) ^ 2 := by
  have hh := dual_square_identity ((sites L).erase L) (weight L)
    (fun a => 1 - divisorFit L (rationalCoefficients L) a) x (tailDual_cross L x hx)
  rw [residual_edge_energy L hL (divisorFit L (rationalCoefficients L))
    (divisor_synthesis_endpoint L _ (rationalCoefficients L) (fun _ => rfl))] at hh
  exact hh

theorem rational_tail_dual_objective_le (L : ℕ) (hL : 0 < L)
    (x : ℕ → ℝ) (hx : tailDualAdmissible L x) :
    2 * tailDualMass L x - tailDualEnergy L x ≤
      rationalMinimum L - commonAverage L := by
  have he := rational_tail_dual_gap L hL x hx
  have hn := Finset.sum_nonneg (s := (sites L).erase L)
    (fun a _ => mul_nonneg (weight_nonneg L a)
      (sq_nonneg (1 - divisorFit L (rationalCoefficients L) a - x a)))
  linarith

/-- The sharp Cauchy--Schwarz constant is the actual remaining minimum. -/
theorem rational_tail_dual_cauchy (L : ℕ) (hL : 0 < L)
    (x : ℕ → ℝ) (hx : tailDualAdmissible L x) :
    tailDualMass L x ^ 2 ≤
      (rationalMinimum L - commonAverage L) * tailDualEnergy L x := by
  have hc := weighted_cauchy ((sites L).erase L) (weight L)
    (fun a => 1 - divisorFit L (rationalCoefficients L) a) x
    (fun a _ => weight_nonneg L a)
  rw [tailDual_cross L x hx, residual_edge_energy L hL (divisorFit L (rationalCoefficients L))
    (divisor_synthesis_endpoint L _ (rationalCoefficients L) (fun _ => rfl))] at hc
  exact hc

/-- The dual maximum is attained by the actual residual. -/
theorem actual_residual_dual_objective (L : ℕ) (hL : 0 < L) :
    2 * tailDualMass L (fun a => 1 - divisorFit L (rationalCoefficients L) a) -
        tailDualEnergy L (fun a => 1 - divisorFit L (rationalCoefficients L) a) =
      rationalMinimum L - commonAverage L := by
  have he := rational_tail_dual_gap L hL _ (actual_residual_tailDualAdmissible L hL)
  have hz : (∑ a ∈ (sites L).erase L, weight L a *
      (1 - divisorFit L (rationalCoefficients L) a -
        (1 - divisorFit L (rationalCoefficients L) a)) ^ 2) = 0 := by simp
  rw [hz] at he
  linarith

/-- A uniform dual upper bound is exactly the original minimum bound.
Thus optimizing all homogeneous constraints does not supply that bound for free. -/
theorem rational_tail_bound_iff_dual_bound (L : ℕ) (hL : 0 < L) (K : ℝ) :
    rationalMinimum L - commonAverage L ≤ K ↔
      ∀ x : ℕ → ℝ, tailDualAdmissible L x →
        2 * tailDualMass L x - tailDualEnergy L x ≤ K := by
  constructor
  · intro h x hx
    exact (rational_tail_dual_objective_le L hL x hx).trans h
  · intro h
    have hh := h _ (actual_residual_tailDualAdmissible L hL)
    rwa [actual_residual_dual_objective L hL] at hh

end RiemannResearch.RH.QRationalCoprimeTail
