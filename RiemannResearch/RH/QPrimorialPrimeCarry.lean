/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QPrimorialMatchedDisplacement
import RiemannResearch.RH.QPrimeCarryProjection
import RiemannResearch.Analysis.NestedOrthogonalDecomposition
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Complete prime/carry elimination on the matched primorial tower

Source: *Squarefree projection displacement and infinite CRT carries*,
9 November 2026, Sections 11 and 12.2. Pareto projection onto the Q carry
complement gives the exact Schur test lift. This retains the signed contribution
from the carry block in both the form and its forcing.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QPrimorialPrimeCarry

open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open Pareto.SquarefreeStageExhaustion QParetoEquivalence QParetoClosedProjectionComparison
open QPrimeCarryProjection QSimultaneousCRT QPrimorialMatchedDisplacement
open QSquarefreePrimorialCofinality QSquarefreeFiniteDisplacement QShiftedReciprocal
open RiemannResearch.Analysis.NestedOrthogonalDecomposition

/-- Every prime divisor of the primorial, with no composite conductors. -/
def primeStage (n : ℕ) : Submodule ℝ QHilbert :=
  Submodule.span ℝ (qResidue '' (Nat.primesLE (n + 3) : Set ℕ))

instance (n : ℕ) : FiniteDimensional ℝ (primeStage n) :=
  FiniteDimensional.span_of_finite ℝ ((Nat.primesLE (n + 3)).finite_toSet.image qResidue)

theorem primeStage_mono : Monotone primeStage := by
  intro n m h
  apply Submodule.span_mono
  rintro _ ⟨p, hp, rfl⟩
  exact ⟨p, by
    change p ∈ Nat.primesLE (m + 3)
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primesLE hp).trans (Nat.add_le_add_right h 3),
      Nat.prime_of_mem_primesLE hp⟩, rfl⟩

theorem iSup_primeStage : (⨆ n, primeStage n) = primeSpan := by
  apply le_antisymm
  · apply iSup_le
    intro n
    apply Submodule.span_le.mpr
    rintro _ ⟨p, hp, rfl⟩
    exact Submodule.subset_span ⟨⟨p, Nat.prime_of_mem_primesLE hp⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨p, rfl⟩
    apply le_iSup primeStage p.val
    apply Submodule.subset_span
    exact ⟨p.val, Nat.mem_primesLE.mpr ⟨by omega, p.property⟩, rfl⟩

theorem primeStage_le (n : ℕ) : primeStage n ≤ primorialStage n := by
  apply Submodule.span_le.mpr
  rintro _ ⟨p, hp, rfl⟩
  have hp' := Nat.prime_of_mem_primesLE hp
  exact conductor_mem n p hp'.one_lt (hp'.dvd_primorial_iff.mpr (Nat.le_of_mem_primesLE hp))

/-- The carry subspace is Q-orthogonal to the finite prime dictionary. -/
abbrev carryStage (n : ℕ) := primorialStage n ⊓ (primeStage n)ᗮ

instance (n : ℕ) : (carryStage n).HasOrthogonalProjection :=
  carry_hasOrthogonalProjection (primeStage_le n)

def primeComponent (n : ℕ) : QHilbert :=
  (primeStage n).starProjection (stageDisplacement n)

theorem primeComponent_tendsto :
    Tendsto primeComponent atTop (𝓝 primeDisplacement) := by
  change Tendsto (fun n => (primeStage n).starProjection (stageDisplacement n)) atTop
    (𝓝 primeDisplacement)
  apply projection_moving_input_tendsto primeStage stageDisplacement_tendsto
  simpa only [iSup_primeStage, primeDisplacement] using
    Submodule.starProjection_tendsto_closure_iSup primeStage primeStage_mono
      QSquarefreeDisplacementRigidity.displacement

def paretoCarryStage (n : ℕ) : Submodule ℝ ThresholdHilbert :=
  (carryStage n).map paretoEquiv.toLinearMap

theorem toPareto_mem_paretoCarryStage_iff (n : ℕ) (x : QHilbert) :
    toPareto x ∈ paretoCarryStage n ↔ x ∈ carryStage n := by
  constructor
  · rintro ⟨y, hy, he⟩
    have h : y = x := paretoEquiv.injective he
    exact h ▸ hy
  · exact fun h => ⟨x, h, rfl⟩

instance (n : ℕ) : (paretoCarryStage n).HasOrthogonalProjection := by
  let _ : FiniteDimensional ℝ (carryStage n) :=
    FiniteDimensional.of_injective
      (Submodule.inclusion (inf_le_left : carryStage n ≤ primorialStage n))
      (Submodule.inclusion_injective _)
  unfold paretoCarryStage
  infer_instance

/-- Lift a prime test to the Pareto-orthogonal complement of the Q carry space.
Subtracting the Pareto carry fit implements the full carry block solve. -/
def schurLift (n : ℕ) (x : QHilbert) : QHilbert :=
  x - pFit (paretoCarryStage n) x

private theorem carryFit_mem (n : ℕ) (x : QHilbert) :
    pFit (paretoCarryStage n) x ∈ carryStage n :=
  pFit_mem _ _ (toPareto_mem_paretoCarryStage_iff n) x

theorem schurLift_mem (n : ℕ) {x : QHilbert} (hx : x ∈ primeStage n) :
    schurLift n x ∈ primorialStage n :=
  (primorialStage n).sub_mem (primeStage_le n hx) (carryFit_mem n x).1

theorem schurLift_orthogonal (n : ℕ) (x : QHilbert) :
    toPareto (schurLift n x) ∈ (paretoCarryStage n)ᗮ := by
  rw [schurLift, toPareto_sub, toPareto_pFit]
  exact Submodule.sub_starProjection_mem_orthogonal _

def schurForm (n : ℕ) (x y : QHilbert) : ℝ :=
  inner ℝ (toPareto (schurLift n x)) (toPareto (schurLift n y))

/-- This is the complete Schur forcing multiplied by zeta(2). -/
def schurForcing (n : ℕ) (x : QHilbert) : ℝ :=
  zetaTwo * inner ℝ (schurLift n x) (B (qOne - primorialOptimizer n))

theorem schurForcing_exact (n : ℕ) (x : QHilbert) :
    schurForcing n x =
      zetaTwo * (inner ℝ x (B (qOne - primorialOptimizer n)) -
        inner ℝ (pFit (paretoCarryStage n) x) (B (qOne - primorialOptimizer n))) := by
  rw [schurForcing, schurLift, inner_sub_left]

theorem schurForm_coercive (n : ℕ) {x : QHilbert} (hx : x ∈ primeStage n) :
    zetaTwo * ‖x‖ ^ 2 ≤ 2 * schurForm n x x := by
  have h := Submodule.inner_right_of_mem_orthogonal hx (carryFit_mem n x).2
  have h' : inner ℝ (pFit (paretoCarryStage n) x) x = 0 := by
    rw [real_inner_comm]
    exact h
  have he : ‖schurLift n x‖ ^ 2 = ‖x‖ ^ 2 + ‖pFit (paretoCarryStage n) x‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, schurLift, inner_sub_left, inner_sub_right,
      inner_sub_right, h, h', real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    ring
  have hg := zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq (schurLift n x)
  rw [he] at hg
  rw [schurForm, real_inner_self_eq_norm_sq]
  nlinarith only [hg, mul_nonneg zetaTwo_pos.le (sq_nonneg ‖pFit (paretoCarryStage n) x‖)]

/-- The finite Schur equation on all prime tests, after exact carry elimination. -/
theorem schur_equation (n : ℕ) {x : QHilbert} (hx : x ∈ primeStage n) :
    schurForm n (primeComponent n) x = schurForcing n x := by
  let y := schurLift n x
  let d := stageDisplacement n
  let r := qOne - primorialOptimizer n
  have hy : y ∈ primorialStage n := schurLift_mem n hx
  have hr : r ∈ (primorialStage n)ᗮ :=
    Submodule.sub_starProjection_mem_orthogonal _
  have hq := Submodule.inner_right_of_mem_orthogonal hy hr
  have hp : inner ℝ (toPareto y) (toPareto (r + d)) = 0 := by
    have he : r + d = qOne - pOptimizer n := by
      dsimp [r, d, stageDisplacement]
      abel
    rw [he]
    change inner ℝ (toPareto y) (toPareto (qOne - pFit (QPrimorialMatchedDisplacement.paretoStage n) qOne)) = 0
    rw [toPareto_sub, toPareto_pFit]
    exact Submodule.inner_right_of_mem_orthogonal ((toPareto_mem_stage_iff n _).mpr hy)
      (Submodule.sub_starProjection_mem_orthogonal _)
  have hpr : inner ℝ (toPareto y) (toPareto d) = zetaTwo * inner ℝ y (B r) := by
    change inner ℝ (toPareto y) (toParetoLinear (r + d)) = 0 at hp
    rw [map_add, inner_add_right] at hp
    change inner ℝ (toPareto y) (toPareto r) + inner ℝ (toPareto y) (toPareto d) = 0 at hp
    rw [pareto_inner_identity y r, hq, zero_sub] at hp
    linarith only [hp]
  have hcd : d - primeComponent n ∈ carryStage n := by
    refine ⟨(primorialStage n).sub_mem (stageDisplacement_mem n)
      (primeStage_le n ((primeStage n).starProjection_apply_mem d)), ?_⟩
    exact Submodule.sub_starProjection_mem_orthogonal d
  have hc : d - schurLift n (primeComponent n) ∈ carryStage n := by
    have he : d - schurLift n (primeComponent n) =
        (d - primeComponent n) + pFit (paretoCarryStage n) (primeComponent n) := by
      unfold schurLift
      abel
    rw [he]
    exact (carryStage n).add_mem hcd (carryFit_mem n _)
  have hz := Submodule.inner_right_of_mem_orthogonal
    ((toPareto_mem_paretoCarryStage_iff n _).mpr hc) (schurLift_orthogonal n x)
  rw [toPareto_sub, inner_sub_left] at hz
  change inner ℝ (toPareto d) (toPareto y) -
    inner ℝ (toPareto (schurLift n (primeComponent n))) (toPareto y) = 0 at hz
  rw [real_inner_comm (toPareto y) (toPareto d), hpr] at hz
  exact (sub_eq_zero.mp hz).symm

theorem primeComponent_eq_zero_of_schurForcing_zero (n : ℕ)
    (h : ∀ x ∈ primeStage n, schurForcing n x = 0) :
    primeComponent n = 0 := by
  have hw : primeComponent n ∈ primeStage n := (primeStage n).starProjection_apply_mem _
  have hc := schurForm_coercive n hw
  rw [schur_equation n hw, h _ hw, mul_zero] at hc
  have hz : ‖primeComponent n‖ ^ 2 = 0 :=
    le_antisymm (nonpos_of_mul_nonpos_right hc zetaTwo_pos) (sq_nonneg _)
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

theorem primeComponent_norm_le_of_schurForcing_bound (n : ℕ) (ε : ℝ) (hε : 0 ≤ ε)
    (h : ∀ x ∈ primeStage n, schurForcing n x ≤ zetaTwo * ε * ‖x‖) :
    ‖primeComponent n‖ ≤ 2 * ε := by
  have hw : primeComponent n ∈ primeStage n := (primeStage n).starProjection_apply_mem _
  have hc := schurForm_coercive n hw
  rw [schur_equation n hw] at hc
  have hb := (hc.trans (mul_le_mul_of_nonneg_left (h _ hw) (by norm_num : (0 : ℝ) ≤ 2)))
  by_contra! hg
  have hn : 0 < ‖primeComponent n‖ := by linarith
  have hz := mul_pos zetaTwo_pos hn
  have hlt := mul_lt_mul_of_pos_left hg hz
  nlinarith only [hlt, hb]

/-- Cofinal control of the complete Schur forcing closes the displacement test. -/
theorem displacement_zero_of_cofinal_schurForcing
    (h : ∀ ε : ℝ, 0 < ε → ∃ᶠ n in atTop,
      ∀ x ∈ primeStage n, schurForcing n x ≤ zetaTwo * ε * ‖x‖) :
    QSquarefreeDisplacementRigidity.displacement = 0 := by
  apply primeDisplacement_eq_zero_iff.mp
  by_contra hn
  have hp : 0 < ‖primeDisplacement‖ := norm_pos_iff.mpr hn
  have hh : ‖primeDisplacement‖ / 2 < ‖primeDisplacement‖ := by linarith
  have hlarge := primeComponent_tendsto.norm.eventually (Ioi_mem_nhds hh)
  obtain ⟨n, hbound, hgt⟩ :=
    ((h (‖primeDisplacement‖ / 4) (by positivity)).and_eventually hlarge).exists
  have hle := primeComponent_norm_le_of_schurForcing_bound n _ (by positivity) hbound
  exact (not_lt_of_ge (by linarith only [hle] : ‖primeComponent n‖ ≤ ‖primeDisplacement‖ / 2)) hgt

end RiemannResearch.RH.QPrimorialPrimeCarry
