/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QRationalGcdTail
import RiemannResearch.RH.QRationalMinimumLimit
import RiemannResearch.RH.QRationalCoprimeTail
import RiemannResearch.RH.QRationalCoprimeLegality
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Dirichlet energy of the actual rational residual tails

Source: the finite tail-difference identity and the user's CRT signed-tail
research agenda, 20 October 2026. The retained endpoint has exactly the
weight `commonAverage L`. The path Dirichlet energy is therefore the
actual rational residual energy minus this endpoint. No asymptotic
variance estimate or squarefree-closure hypothesis is used.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QRationalCoprimeTail
open RiemannResearch.Analysis.FiniteWeightedTailCharge

/-- The exact first difference of the concrete finite weighted tail. -/
theorem residualTail_step (L : ℕ) (f : ℕ → ℝ) (k : ℕ)
    (hk : k ∈ sites L) :
    residualTail L f k - residualTail L f (k + 1) =
      weight L k * (1 - f k) := by
  unfold residualTail tail
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ a ∈ sites L,
        ((if k ≤ a then weight L a * (1 - f a) else 0) -
          (if k + 1 ≤ a then weight L a * (1 - f a) else 0))) =
        ∑ a ∈ sites L, if a = k then weight L a * (1 - f a) else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      by_cases hak : a = k
      · subst a
        simp
      · by_cases hka : k ≤ a
        · have hsucc : k + 1 ≤ a := by omega
          simp [hak, hka, hsucc]
        · have hsucc : ¬ k + 1 ≤ a := by omega
          simp [hak, hka, hsucc]
    _ = weight L k * (1 - f k) := by simp [hk]

/-- Every actual site has strictly positive rational weight. -/
theorem weight_pos_of_mem_sites (L a : ℕ) (ha : a ∈ sites L) :
    0 < weight L a := by
  have haR : (0 : ℝ) < a := by
    exact_mod_cast (show 0 < a from (Finset.mem_Icc.mp ha).1)
  unfold weight
  apply add_pos_of_pos_of_nonneg
  · positivity
  · positivity

/-- The finite path energy excludes only the retained endpoint `L`.
The same identity holds with centered tails, since taking a first
difference cancels their common average. -/
theorem residualTail_dirichlet_energy (L : ℕ) (hL : 0 < L)
    (f : ℕ → ℝ) (hfL : f L = 0) :
    (∑ k ∈ (sites L).erase L,
      (residualTail L f k - residualTail L f (k + 1))^2 / weight L k) =
      rationalError L f - commonAverage L := by
  have hmem : L ∈ sites L := Finset.mem_Icc.mpr ⟨hL, le_rfl⟩
  have hsum := Finset.sum_erase_add (s := sites L)
    (f := fun k => weight L k * (1 - f k)^2) hmem
  have hend : weight L L * (1 - f L)^2 = commonAverage L := by
    rw [hfL, sub_zero, one_pow, mul_one, weight_endpoint L hL]
    rfl
  rw [hend] at hsum
  change (∑ k ∈ (sites L).erase L, weight L k * (1 - f k)^2) +
      commonAverage L = rationalError L f at hsum
  calc
    (∑ k ∈ (sites L).erase L,
        (residualTail L f k - residualTail L f (k + 1))^2 / weight L k) =
        ∑ k ∈ (sites L).erase L, weight L k * (1 - f k)^2 := by
      apply Finset.sum_congr rfl
      intro k hk
      have hks : k ∈ sites L := (Finset.mem_erase.mp hk).2
      rw [residualTail_step L f k hks]
      have hw : weight L k ≠ 0 := ne_of_gt (weight_pos_of_mem_sites L k hks)
      field_simp [hw]
    _ = rationalError L f - commonAverage L := by linarith

/-- A normal solution satisfies an exact nonlinear path identity:
its initial centered tail equals the complete Dirichlet energy. -/
theorem residualTail_initial_gap_eq_dirichlet (L : ℕ) (hL : 0 < L)
    (c : ℕ → ℝ)
    (hdiv : ∀ d ∈ L.divisors,
      (∑ a ∈ sites L, weight L a * (1 - divisorFit L c a) *
        ArithmeticCumulative.residueFraction d a) = 0) :
    residualTail L (divisorFit L c) 1 - commonAverage L =
      ∑ k ∈ (sites L).erase L,
        (residualTail L (divisorFit L c) k -
          residualTail L (divisorFit L c) (k + 1))^2 / weight L k := by
  rw [residualTail_one_eq_error L c hdiv]
  exact (residualTail_dirichlet_energy L hL (divisorFit L c)
    (divisor_synthesis_endpoint L _ c (fun _ => rfl))).symm

/-- Every individual tail increment is controlled by the full remaining
Dirichlet energy. This is a finite local bound, with the endpoint removed. -/
theorem residualTail_step_sq_le (L : ℕ) (hL : 0 < L)
    (f : ℕ → ℝ) (hfL : f L = 0) (k : ℕ)
    (hk : k ∈ (sites L).erase L) :
    (residualTail L f k - residualTail L f (k + 1))^2 ≤
      weight L k * (rationalError L f - commonAverage L) := by
  have hks : k ∈ sites L := (Finset.mem_erase.mp hk).2
  have hw := weight_pos_of_mem_sites L k hks
  have hterm :
      (residualTail L f k - residualTail L f (k + 1))^2 / weight L k ≤
        rationalError L f - commonAverage L := by
    rw [← residualTail_dirichlet_energy L hL f hfL]
    apply Finset.single_le_sum _ hk
    intro j hj
    exact div_nonneg (sq_nonneg _) (weight_nonneg L j)
  have h := (div_le_iff₀ hw).mp hterm
  simpa only [mul_comm] using h

/-- Specialization to the actual selected rational minimizer. Its normal
equations have the existing unconditional finite provider. -/
theorem rationalMinimum_tail_dirichlet (L : ℕ) (hL : 0 < L) :
    (∑ k ∈ (sites L).erase L,
      (residualTail L (divisorFit L (rationalCoefficients L)) k -
        residualTail L (divisorFit L (rationalCoefficients L)) (k + 1))^2 /
          weight L k) = rationalMinimum L - commonAverage L := by
  exact residualTail_dirichlet_energy L hL _
    (divisor_synthesis_endpoint L _ (rationalCoefficients L) (fun _ => rfl))

end RiemannResearch.RH.QRationalCoprimeTail
