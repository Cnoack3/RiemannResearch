/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFullDisplacement
import RiemannResearch.RH.QFloorDilation
import RiemannResearch.RH.QPrimeProjectionControl
import RiemannResearch.RH.QFiniteForcingData
import RiemannResearch.NumberTheory.PrimeScaleBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Prime control of the full-conductor matched displacement

Source: user-provided Full_Conductor_RH_Projection_Machinery.pdf, Sections 4.2
and 10.3, and the subsequent prime-component argument of 13 November 2026.
The signed forcing deficit is retained before its tail estimate.
The quantitative bound uses the repository's Bertrand scale lemma.

These declarations concern QFullDisplacement.displacement and its actual
all-conductor Pareto residual. They do not substitute the distinct squarefree
displacement. Only the generic matched-projection estimates and atom norm
bounds from QPrimeProjectionControl/QFiniteForcingData are reused.

The prime projection and target membership are equivalent unconditionally.
Neither is proved to vanish or hold here. The RH implication is assembled
separately; its classical converse still needs the repository's analytic
Baez-Duarte provider.
-/

noncomputable section
namespace RiemannResearch.RH.QFullDisplacement
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QParetoClosedProjectionComparison QFullResidueProjection
open QAnnihilatorTailEscape QFiniteSupportDualCriterion
open RiemannResearch.NumberTheory.PrimeScaleBounds

private theorem residue_mem (m : ℕ) (hm : 2 ≤ m) : qResidue m ∈ closure :=
  legalSpan.le_topologicalClosure
    (QFloorDilation.qResidue_mem_legalSpan m (by omega))

/-- Exact signed forcing deficit, with every physical site retained. -/
theorem conductor_forcing_deficit (m : ℕ) (hm : 2 ≤ m) :
    ‖toPareto pResidual‖ ^ 2 -
      (zetaTwo * m) * inner ℝ (qResidue m) displacement =
      ∑' k : ℕ, positiveWeight k *
        ((1 - (((k % m : ℕ) : ℝ) / k)) * qSequence pResidual k) := by
  exact QSquarefreeFiniteDisplacement.matched_conductor_forcing_deficit
    closure paretoClosure m (by omega) (residue_mem m hm)
    ((toPareto_mem_iff _).mpr (residue_mem m hm))

/-- Only the actual Pareto residual tail above the conductor enters the error. -/
theorem conductor_forcing_error (m : ℕ) (hm : 2 ≤ m) :
    |‖toPareto pResidual‖ ^ 2 -
      (zetaTwo * m) * inner ℝ (qResidue m) displacement| ≤
      Real.sqrt (1 / (m : ℝ)) * ‖toPareto (tail (m - 1) pResidual)‖ := by
  exact QSquarefreeFiniteDisplacement.matched_conductor_forcing_error
    closure paretoClosure m (by omega) (residue_mem m hm)
    ((toPareto_mem_iff _).mpr (residue_mem m hm))

/-- The projection residual has energy at most the unit target energy. -/
theorem pResidual_energy_le_one : ‖toPareto pResidual‖ ^ 2 ≤ 1 := by
  have hunit : ‖hilbertOne‖ = 1 := by
    nlinarith [hilbertOne_norm_sq, norm_nonneg hilbertOne]
  have hcs := abs_real_inner_le_norm hilbertOne (toPareto pResidual)
  have hmean : inner ℝ hilbertOne (toPareto pResidual) =
      ‖toPareto pResidual‖ ^ 2 :=
    QSquarefreeFiniteDisplacement.matched_pResidual_mean paretoClosure
  rw [hmean, abs_of_nonneg (sq_nonneg _), hunit, one_mul] at hcs
  nlinarith [norm_nonneg (toPareto pResidual)]

/-- Every included conductor controls the residual through any projection seeing its atom. -/
theorem residual_le_projected_displacement
    (m : ℕ) (hm : 2 ≤ m)
    (W : Submodule ℝ QHilbert) [W.HasOrthogonalProjection]
    (hW : qResidue m ∈ W) :
    ‖toPareto pResidual‖ ^ 2 ≤
      Real.sqrt (2 * zetaTwo * (m : ℝ)) * ‖W.starProjection displacement‖ +
        Real.sqrt (‖toPareto pResidual‖ ^ 2 / (m : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hrow := Submodule.inner_right_of_mem_orthogonal hW
    (Submodule.sub_starProjection_mem_orthogonal (K := W) displacement)
  rw [inner_sub_right] at hrow
  have heq : inner ℝ (qResidue m) displacement =
      inner ℝ (qResidue m) (W.starProjection displacement) := sub_eq_zero.mp hrow
  have hinner : (zetaTwo * (m : ℝ)) * inner ℝ (qResidue m) displacement ≤
      Real.sqrt (2 * zetaTwo * (m : ℝ)) * ‖W.starProjection displacement‖ := by
    rw [heq]
    calc
      _ ≤ (zetaTwo * (m : ℝ)) *
          (‖qResidue m‖ * ‖W.starProjection displacement‖) :=
        mul_le_mul_of_nonneg_left
          ((le_abs_self _).trans (abs_real_inner_le_norm _ _))
          (mul_nonneg zetaTwo_pos.le hmR.le)
      _ = ((zetaTwo * (m : ℝ)) * ‖qResidue m‖) *
          ‖W.starProjection displacement‖ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (QSquarefreeFiniteDisplacement.scaled_qResidue_norm_le m hm) (norm_nonneg _)
  have herr := conductor_forcing_error m hm
  have htail := QSquarefreeFiniteDisplacement.toPareto_tail_norm_le (m - 1) pResidual
  have herr' : |‖toPareto pResidual‖ ^ 2 -
      (zetaTwo * (m : ℝ)) * inner ℝ (qResidue m) displacement| ≤
      Real.sqrt (1 / (m : ℝ)) * ‖toPareto pResidual‖ :=
    herr.trans (mul_le_mul_of_nonneg_left htail (Real.sqrt_nonneg _))
  have hsqrt : Real.sqrt (1 / (m : ℝ)) * ‖toPareto pResidual‖ =
      Real.sqrt (‖toPareto pResidual‖ ^ 2 / (m : ℝ)) := by
    calc
      _ = Real.sqrt (1 / (m : ℝ)) * Real.sqrt (‖toPareto pResidual‖ ^ 2) := by
        rw [Real.sqrt_sq (norm_nonneg _)]
      _ = Real.sqrt ((1 / (m : ℝ)) * ‖toPareto pResidual‖ ^ 2) :=
        (Real.sqrt_mul (by positivity) _).symm
      _ = _ := by congr 1; ring
  rw [hsqrt] at herr'
  have herr'' := (le_abs_self (‖toPareto pResidual‖ ^ 2 -
    (zetaTwo * (m : ℝ)) * inner ℝ (qResidue m) displacement)).trans herr'
  linarith

/-- Full-conductor residual energy cubed is controlled by the squared prime-visible displacement. -/
theorem pResidual_cube_le_prime_projection
    (W : Submodule ℝ QHilbert) [W.HasOrthogonalProjection]
    (hW : ∀ p : ℕ, p.Prime → qResidue p ∈ W) :
    (‖toPareto pResidual‖ ^ 2) ^ 3 ≤
      64 * zetaTwo * ‖W.starProjection displacement‖ ^ 2 := by
  let e : ℝ := ‖toPareto pResidual‖ ^ 2
  by_cases he : e = 0
  · simp only [show ‖toPareto pResidual‖ ^ 2 = 0 from he, zero_pow (by decide : 3 ≠ 0)]
    positivity [zetaTwo_pos]
  have hepos : 0 < e := lt_of_le_of_ne (sq_nonneg _) (Ne.symm he)
  obtain ⟨H, hH⟩ := exists_nat_gt (8 / e)
  have hscale : 8 ≤ e * (H : ℝ) := by
    have hh := (div_lt_iff₀ hepos).mp hH
    nlinarith
  obtain ⟨p, hp, _, hlo, hhi⟩ := exists_prime_at_residual_scale e H hepos
    pResidual_energy_le_one hscale
  exact cube_le_of_prime_scale e ‖W.starProjection displacement‖
    zetaTwo (p : ℝ) hepos (norm_nonneg _) zetaTwo_pos
    (by exact_mod_cast hp.pos) hlo hhi
    (residual_le_projected_displacement p hp.two_le W (hW p hp))

/-- The equivalent norm form of the complete prime-component bound. -/
theorem pResidual_norm_cube_le_prime_projection
    (W : Submodule ℝ QHilbert) [W.HasOrthogonalProjection]
    (hW : ∀ p : ℕ, p.Prime → qResidue p ∈ W) :
    ‖toPareto pResidual‖ ^ 3 ≤
      8 * Real.sqrt zetaTwo * ‖W.starProjection displacement‖ := by
  have h := pResidual_cube_le_prime_projection W hW
  have hs : (‖toPareto pResidual‖ ^ 3) ^ 2 ≤
      (8 * Real.sqrt zetaTwo * ‖W.starProjection displacement‖) ^ 2 := by
    calc
      _ = (‖toPareto pResidual‖ ^ 2) ^ 3 := by ring
      _ ≤ _ := h
      _ = _ := by rw [mul_pow, mul_pow, Real.sq_sqrt zetaTwo_pos.le]; ring
  exact (sq_le_sq₀ (by positivity) (by positivity)).mp hs

/-- Prime-component vanishing forces the actual full Pareto residual to vanish. -/
theorem pResidual_eq_zero_of_prime_projection_eq_zero
    (W : Submodule ℝ QHilbert) [W.HasOrthogonalProjection]
    (hW : ∀ p : ℕ, p.Prime → qResidue p ∈ W)
    (hz : W.starProjection displacement = 0) : pResidual = 0 := by
  have h := pResidual_cube_le_prime_projection W hW
  simp only [hz, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] at h
  have hn : ‖toPareto pResidual‖ = 0 := by
    apply le_antisymm _ (norm_nonneg _)
    by_contra hnot
    have hpos : 0 < ‖toPareto pResidual‖ := lt_of_not_ge hnot
    have hpow : 0 < (‖toPareto pResidual‖ ^ 2) ^ 3 := by positivity
    exact (not_lt_of_ge h) hpow
  apply QParetoEquivalence.paretoEquiv.injective
  change toPareto pResidual = toPareto (0 : QHilbert)
  rw [show toPareto (0 : QHilbert) = 0 from toParetoLinear.map_zero]
  exact norm_eq_zero.mp hn

/-- Exact target-membership criterion, with prime-component vanishing still open. -/
theorem prime_projection_eq_zero_iff_one_mem
    (W : Submodule ℝ QHilbert) [W.HasOrthogonalProjection]
    (hW : ∀ p : ℕ, p.Prime → qResidue p ∈ W) :
    W.starProjection displacement = 0 ↔ qOne ∈ closure := by
  constructor
  · intro hz
    have hp := pResidual_eq_zero_of_prime_projection_eq_zero W hW hz
    change qOne - pFit paretoClosure qOne = 0 at hp
    rw [sub_eq_zero.mp hp]
    exact pFit_mem closure paretoClosure toPareto_mem_iff qOne
  · intro h
    rw [displacement_eq_zero_of_qResidual_eq_zero (qResidual_eq_zero_iff.mpr h), map_zero]

/-- The full matched displacement cannot be nonzero with a zero prime component. -/
theorem prime_projection_eq_zero_iff_displacement_eq_zero
    (W : Submodule ℝ QHilbert) [W.HasOrthogonalProjection]
    (hW : ∀ p : ℕ, p.Prime → qResidue p ∈ W) :
    W.starProjection displacement = 0 ↔ displacement = 0 := by
  constructor
  · intro hz
    exact displacement_eq_zero_of_qResidual_eq_zero
      (qResidual_eq_zero_iff.mpr ((prime_projection_eq_zero_iff_one_mem W hW).mp hz))
  · intro hd
    simp only [hd, map_zero]

#print axioms pResidual_cube_le_prime_projection
#print axioms prime_projection_eq_zero_iff_one_mem
end RiemannResearch.RH.QFullDisplacement
