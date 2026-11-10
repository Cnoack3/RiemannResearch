/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QPrimorialSchurEnergy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
/-!
# Certified approximate solves for the actual primorial Schur energy

Source: user-provided *Squarefree projection displacement and infinite CRT
carries*, 9 November 2026, Sections 11 and 12.2, supplies the canonical
Schur problem. Completion of the square and the checked arithmetic
coercivity bound give the variational identity and a posteriori interval.
All forms use the complete norms and the full carry solve.
The cofinal small-upper-endpoint provider is an Open arithmetic obligation.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QPrimorialPrimeCarry
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QParetoClosedProjectionComparison

theorem toPareto_schurLift (n : ℕ) (x : QHilbert) :
    toPareto (schurLift n x) = (paretoCarryStage n)ᗮ.starProjection (toPareto x) := by
  rw [schurLift, toPareto_sub, toPareto_pFit, Submodule.starProjection_orthogonal]
  rfl

def trialEnergy (n : ℕ) (x : QHilbert) : ℝ :=
  2 * schurForcing n x - schurForm n x x

def forcingResidual (n : ℕ) (x y : QHilbert) : ℝ :=
  schurForcing n y - schurForm n x y

/-- Exact variational equality before estimating the solve error. -/
theorem schurVariational_exact (n : ℕ) {x : QHilbert} (hx : x ∈ primeStage n) :
    selfForcing n = trialEnergy n x +
      schurForm n (primeComponent n - x) (primeComponent n - x) := by
  have hw : primeComponent n ∈ primeStage n := (primeStage n).starProjection_apply_mem _
  rw [selfForcing, ← schur_equation n hw, trialEnergy, ← schur_equation n hx]
  simp only [schurForm, toPareto_schurLift, toPareto_sub, map_sub,
    inner_sub_left, inner_sub_right]
  rw [real_inner_comm ((paretoCarryStage n)ᗮ.starProjection (toPareto x))
    ((paretoCarryStage n)ᗮ.starProjection (toPareto (primeComponent n)))]
  ring

theorem forcingResidual_energy (n : ℕ) {x : QHilbert} (hx : x ∈ primeStage n) :
    schurForm n (primeComponent n - x) (primeComponent n - x) =
      forcingResidual n x (primeComponent n - x) := by
  have he : primeComponent n - x ∈ primeStage n :=
    (primeStage n).sub_mem ((primeStage n).starProjection_apply_mem _) hx
  rw [forcingResidual, ← schur_equation n he]
  simp only [schurForm, toPareto_schurLift, toPareto_sub, map_sub,
    inner_sub_left, inner_sub_right]
  ring

/-- An approximate solve and a certified dual residual bound enclose the
actual canonical scalar energy. The error uses the improved 59/30 constant. -/
theorem selfForcing_interval (n : ℕ) {x : QHilbert} (hx : x ∈ primeStage n)
    (ε : ℝ) (hε : 0 ≤ ε)
    (hres : ∀ y ∈ primeStage n, forcingResidual n x y ≤ zetaTwo * ε * ‖y‖) :
    trialEnergy n x ≤ selfForcing n ∧
      selfForcing n ≤ trialEnergy n x + (59 / 30 : ℝ) * zetaTwo * ε ^ 2 := by
  let e := primeComponent n - x
  have he : e ∈ primeStage n :=
    (primeStage n).sub_mem ((primeStage n).starProjection_apply_mem _) hx
  have hc := schurForm_coercive_arithmetic n he
  have hr := hres e he
  rw [← forcingResidual_energy n hx] at hr
  change schurForm n e e ≤ zetaTwo * ε * ‖e‖ at hr
  have hn : ‖e‖ ≤ (59 / 30 : ℝ) * ε := by
    by_contra! hgt
    have hp : 0 < ‖e‖ := by linarith
    have hlt := mul_lt_mul_of_pos_left hgt (mul_pos zetaTwo_pos hp)
    nlinarith only [hlt, hc, hr]
  have hu := hr.trans (mul_le_mul_of_nonneg_left hn (mul_nonneg zetaTwo_pos.le hε))
  have h0 : 0 ≤ schurForm n e e := by
    rw [schurForm, real_inner_self_eq_norm_sq]
    positivity
  have hv := schurVariational_exact n hx
  change selfForcing n = trialEnergy n x + schurForm n e e at hv
  constructor <;> nlinarith only [hv, h0, hu]

/-- Conditional RH certificate using any computable trial prime components.
All bounds concern the complete forms, including the carry solve. -/
theorem riemannHypothesis_of_cofinal_schurCertificate
    (x : ℕ → QHilbert) (ε : ℕ → ℝ)
    (hx : ∀ n, x n ∈ primeStage n) (hε : ∀ n, 0 ≤ ε n)
    (hres : ∀ n, ∀ y ∈ primeStage n,
      forcingResidual n (x n) y ≤ zetaTwo * ε n * ‖y‖)
    (hbound : ∀ δ : ℝ, 0 < δ → ∃ᶠ n in atTop,
      trialEnergy n (x n) + (59 / 30 : ℝ) * zetaTwo * (ε n) ^ 2 ≤ δ) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_selfForcing
  intro δ hδ
  exact (hbound δ hδ).mono fun n hn =>
    (selfForcing_interval n (hx n) (ε n) (hε n) (hres n)).2.trans hn

end RiemannResearch.RH.QPrimorialPrimeCarry
