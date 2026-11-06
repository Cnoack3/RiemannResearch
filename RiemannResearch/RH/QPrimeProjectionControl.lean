/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFiniteForcingData
import RiemannResearch.RH.QConductorCoefficientMass
import RiemannResearch.RH.QSquarefreeSchurCoercivity
import RiemannResearch.RH.ParetoCompactCutoffLimits
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import RiemannResearch.NumberTheory.PrimeScaleBounds

/-!
# Quantitative prime control of the actual matched finite projections

Source: the 5 November 2026 audit of *Projection Displacement, Prime Atoms,
and Carries*, page 3. The complete signed forcing identity is retained in
`QFiniteForcingData.full_conductor_forcing_deficit`. Its tail estimate,
Cauchy--Schwarz, and Bertrand's postulate give the cubic bound below.
Both fits use the same finite squarefree space and the target is `qOne`.
The bound is unconditional. Vanishing of the prime projection is a separate
arithmetic obligation.
-/

noncomputable section

namespace RiemannResearch.RH.QSquarefreeFiniteDisplacement

open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open ZetaTwoOptimizerStage QAnnihilatorTailEscape QFiniteSupportDualCriterion
open RiemannResearch.NumberTheory.PrimeScaleBounds

/-- The physical tail agrees under the two Hilbert representations. -/
theorem toPareto_tail_eq_compactTail (T : ℕ) (f : QHilbert) :
    toPareto (tail T f) = toPareto f - compactHead T (toPareto f) := by
  apply hilbertSequence_injective
  funext k
  change hilbertSequence (toPareto (tail T f)) k =
    hilbertSequenceLinear (toPareto f - compactHead T (toPareto f)) k
  rw [map_sub]
  change hilbertSequence (toPareto (tail T f)) k =
    hilbertSequence (toPareto f) k - hilbertSequence (compactHead T (toPareto f)) k
  simp only [toPareto_sequence, compactHead_sequence]
  cases k with
  | zero => simp
  | succ n =>
      by_cases hn : n < T
      · rw [if_pos (by omega : n + 1 ≤ T)]
        change (f n - finiteHead T f n) / Real.sqrt (qWeight n) =
          f n / Real.sqrt (qWeight n) - f n / Real.sqrt (qWeight n)
        rw [finiteHead_apply_of_lt T f n hn]
        simp
      · rw [if_neg (by omega : ¬ n + 1 ≤ T)]
        change (f n - finiteHead T f n) / Real.sqrt (qWeight n) =
          f n / Real.sqrt (qWeight n) - 0
        rw [finiteHead_apply_eq_zero T f n (by omega)]
        simp

theorem toPareto_tail_norm_le (T : ℕ) (f : QHilbert) :
    ‖toPareto (tail T f)‖ ≤ ‖toPareto f‖ := by
  rw [toPareto_tail_eq_compactTail]
  exact compactHead_tail_norm_le T (toPareto f)

/-- The common residual energy is bounded by the squared norm of the target. -/
theorem finitePResidual_energy_le_one (N : ℕ) :
    ‖toPareto (qOne - finitePFit N)‖ ^ 2 ≤ 1 := by
  have hunit : ‖hilbertOne‖ = 1 := by
    nlinarith [hilbertOne_norm_sq, norm_nonneg hilbertOne]
  have hcs := abs_real_inner_le_norm hilbertOne (toPareto (qOne - finitePFit N))
  rw [finitePResidual_mean, abs_of_nonneg (sq_nonneg _), hunit, one_mul] at hcs
  nlinarith [norm_nonneg (toPareto (qOne - finitePFit N))]

theorem scaled_qResidue_norm_le (m : ℕ) (hm : 2 ≤ m) :
    (zetaTwo * (m : ℝ)) * ‖qResidue m‖ ≤ Real.sqrt (2 * zetaTwo * (m : ℝ)) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hden : 0 < zetaTwo * (m : ℝ) := mul_pos zetaTwo_pos hmpos
  apply Real.le_sqrt_of_sq_le
  calc
    ((zetaTwo * (m : ℝ)) * ‖qResidue m‖) ^ 2 =
        (zetaTwo * (m : ℝ)) ^ 2 * ‖qResidue m‖ ^ 2 := by ring
    _ ≤ (zetaTwo * (m : ℝ)) ^ 2 * (2 / (zetaTwo * (m : ℝ))) :=
      mul_le_mul_of_nonneg_left (qResidue_norm_sq_le_two_div m hm) (sq_nonneg _)
    _ = 2 * zetaTwo * (m : ℝ) := by
      field_simp [hden.ne']

/-- An included conductor controls the actual residual through any closed
subspace containing its atom. In particular this applies to the prime span. -/
theorem finite_residual_le_projected_displacement
    (N p : ℕ) (hp : 2 ≤ p) (hv : qResidue p ∈ stage N)
    (W : Submodule ℝ QHilbert) [W.HasOrthogonalProjection]
    (hW : qResidue p ∈ W) :
    ‖toPareto (qOne - finitePFit N)‖ ^ 2 ≤
      Real.sqrt (2 * zetaTwo * (p : ℝ)) * ‖W.starProjection (finiteDisplacement N)‖ +
        Real.sqrt (‖toPareto (qOne - finitePFit N)‖ ^ 2 / (p : ℝ)) := by
  have hp0 : 0 < p := by omega
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hrow := Submodule.inner_right_of_mem_orthogonal hW
    (Submodule.sub_starProjection_mem_orthogonal (K := W) (finiteDisplacement N))
  rw [inner_sub_right] at hrow
  have heq : inner ℝ (qResidue p) (finiteDisplacement N) =
      inner ℝ (qResidue p) (W.starProjection (finiteDisplacement N)) :=
    sub_eq_zero.mp hrow
  have hinner : (zetaTwo * (p : ℝ)) * inner ℝ (qResidue p) (finiteDisplacement N) ≤
      Real.sqrt (2 * zetaTwo * (p : ℝ)) * ‖W.starProjection (finiteDisplacement N)‖ := by
    rw [heq]
    calc
      _ ≤ (zetaTwo * (p : ℝ)) *
          (‖qResidue p‖ * ‖W.starProjection (finiteDisplacement N)‖) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg zetaTwo_pos.le hpR.le)
        exact (le_abs_self _).trans (abs_real_inner_le_norm _ _)
      _ = ((zetaTwo * (p : ℝ)) * ‖qResidue p‖) *
          ‖W.starProjection (finiteDisplacement N)‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (scaled_qResidue_norm_le p hp) (norm_nonneg _)
  have herr := full_conductor_forcing_error N p hp0 hv
  have htail := toPareto_tail_norm_le (p - 1) (qOne - finitePFit N)
  have herr' : |‖toPareto (qOne - finitePFit N)‖ ^ 2 -
      (zetaTwo * (p : ℝ)) * inner ℝ (qResidue p) (finiteDisplacement N)| ≤
      Real.sqrt (1 / (p : ℝ)) * ‖toPareto (qOne - finitePFit N)‖ :=
    herr.trans (mul_le_mul_of_nonneg_left htail (Real.sqrt_nonneg _))
  have hsqrt : Real.sqrt (1 / (p : ℝ)) * ‖toPareto (qOne - finitePFit N)‖ =
      Real.sqrt (‖toPareto (qOne - finitePFit N)‖ ^ 2 / (p : ℝ)) := by
    calc
      _ = Real.sqrt (1 / (p : ℝ)) *
          Real.sqrt (‖toPareto (qOne - finitePFit N)‖ ^ 2) := by
        rw [Real.sqrt_sq (norm_nonneg _)]
      _ = Real.sqrt ((1 / (p : ℝ)) * ‖toPareto (qOne - finitePFit N)‖ ^ 2) :=
        (Real.sqrt_mul (by positivity) _).symm
      _ = _ := by congr 1; ring
  rw [hsqrt] at herr'
  have herr'' := (le_abs_self (‖toPareto (qOne - finitePFit N)‖ ^ 2 -
    (zetaTwo * (p : ℝ)) * inner ℝ (qResidue p) (finiteDisplacement N))).trans herr'
  linarith

/-- The finite matched residual is controlled by its displacement visible in
any projected subspace containing all included prime atoms. -/
theorem finitePResidual_cube_le_prime_projection
    (N : ℕ) (W : Submodule ℝ QHilbert) [W.HasOrthogonalProjection]
    (hW : ∀ p : ℕ, p.Prime → p ≤ N + 1 → qResidue p ∈ W) :
    (‖toPareto (qOne - finitePFit N)‖ ^ 2) ^ 3 ≤
      max ((8 / ((N : ℝ) + 1)) ^ 3)
        (64 * zetaTwo * ‖W.starProjection (finiteDisplacement N)‖ ^ 2) := by
  let e : ℝ := ‖toPareto (qOne - finitePFit N)‖ ^ 2
  have he : 0 ≤ e := sq_nonneg _
  have heone : e ≤ 1 := finitePResidual_energy_le_one N
  have hHpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  by_cases hscale : 8 ≤ e * ((N : ℝ) + 1)
  · have hepos : 0 < e := by
      by_contra hn
      have hz : e = 0 := le_antisymm (le_of_not_gt hn) he
      norm_num [hz] at hscale
    obtain ⟨p, hp, hpN, hlo, hhi⟩ := exists_prime_at_residual_scale e (N + 1)
      hepos heone (by simpa only [Nat.cast_add, Nat.cast_one] using hscale)
    have hmem : qResidue p ∈ stage N :=
      QSquarefreeSchurCoercivity.qResidue_mem_stage N p hp.two_le hpN hp.squarefree
    have hpair := finite_residual_le_projected_displacement N p hp.two_le hmem W (hW p hp hpN)
    have hc := cube_le_of_prime_scale e ‖W.starProjection (finiteDisplacement N)‖
      zetaTwo (p : ℝ) hepos (norm_nonneg _) zetaTwo_pos
      (by exact_mod_cast hp.pos) hlo hhi hpair
    exact hc.trans (le_max_right _ _)
  · have hel : e ≤ 8 / ((N : ℝ) + 1) := by
      apply (le_div_iff₀ hHpos).mpr
      exact (lt_of_not_ge hscale).le
    have hecube : e ^ 3 ≤ (8 / ((N : ℝ) + 1)) ^ 3 := by
      gcongr
    exact hecube.trans (le_max_left _ _)

end RiemannResearch.RH.QSquarefreeFiniteDisplacement
