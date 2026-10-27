/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPrimeResamplingFormula
import RiemannResearch.RH.QSquarefreeDilationObstruction
import RiemannResearch.RH.QSquarefreeJumpDistance
import RiemannResearch.RH.PrimePowerTwoTargetCriterion
import RiemannResearch.RH.SquarefreeRadicalDifference
import RiemannResearch.RH.PrimeResamplingGeometric
import RiemannResearch.RH.PrimeResamplingCore
import RiemannResearch.RH.ZetaTwoOptimizerStage
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import Lean.Elab.Tactic.Omega

/-!
# Dyadic resampling does not preserve the actual squarefree closure

The genuine legal atom g_3 has dyadic conditional mean with four-site
square-jump defect 2/5. Thus its conditional mean lies a fixed positive
distance from the squarefree closure even after constants are added.
The resulting commutator lower bound applies to every legal stage
containing g_3. This rules out blanket commutation arguments; it does
not refute a moment estimate on the special inputs B r_N.

Source: direct arithmetic continuation of DyadicResamplingMomentResearch20261026.md.
The complete infinite geometric conditional average is retained.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeResamplingObstruction
open ZetaTwoHilbert ZetaTwoProbability PrimeResampling QPrimeResampling
open ArithmeticCumulative SquarefreeRadicalDifference QSquarefreeJumpDistance
open PrimePowerTarget

private theorem two_pow_mod_three (k : ℕ) :
    2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rcases ih with hk | hk
      · right
        norm_num [pow_succ, Nat.mul_mod, hk]
      · left
        norm_num [pow_succ, Nat.mul_mod, hk]

private theorem ternary_orbit_pair (k : ℕ) :
    residueFraction 3 (2 ^ k) + residueFraction 3 (2 ^ (k + 1)) = 1 := by
  rcases two_pow_mod_three k with hk | hk <;>
    norm_num [residueFraction, pow_succ, Nat.mul_mod, hk]

private def ternaryOrbitTerm (k : ℕ) : ℝ :=
  geometricMass 2 k * residueFraction 3 (2 ^ k)

private theorem ternaryOrbitTerm_summable : Summable ternaryOrbitTerm := by
  have h := geometricAverage_summable 2 1 (by norm_num) (by norm_num) (qResidue 3)
  change Summable (fun k : ℕ => geometricMass 2 k * residueFraction 3 (2 ^ k))
  simpa [replaceValuation, primeCore, qSequence_qResidue] using h

private theorem ternaryOrbitTerm_succ (k : ℕ) :
    ternaryOrbitTerm (k + 1) =
      (1 / 4 : ℝ) * (geometricMass 2 k - ternaryOrbitTerm k) := by
  have hp : residueFraction 3 (2 ^ (k + 1)) =
      1 - residueFraction 3 (2 ^ k) := by
    linarith [ternary_orbit_pair k]
  have hg : geometricMass 2 (k + 1) = (1 / 4 : ℝ) * geometricMass 2 k := by
    simp only [geometricMass, geometricParameter, pow_succ]
    norm_num
    ring
  simp only [ternaryOrbitTerm, hg, hp]
  ring

private theorem ternaryOrbitTerm_tsum : (∑' k, ternaryOrbitTerm k) = (2 / 5 : ℝ) := by
  have ht := ternaryOrbitTerm_summable.tsum_eq_zero_add
  have htail : (∑' k, ternaryOrbitTerm (k + 1)) =
      (1 / 4 : ℝ) * (1 - ∑' k, ternaryOrbitTerm k) := by
    simp_rw [ternaryOrbitTerm_succ]
    rw [tsum_mul_left,
      (geometricMass_hasSum 2 (by norm_num)).summable.tsum_sub ternaryOrbitTerm_summable,
      geometricMass_tsum 2 (by norm_num)]
  have hzero : ternaryOrbitTerm 0 = (1 / 4 : ℝ) := by
    norm_num [ternaryOrbitTerm, geometricMass, geometricParameter, residueFraction]
  rw [hzero, htail] at ht
  linarith

/-- Exact complete geometric conditional average at the first integer. -/
theorem C_two_qResidue_three_at_one :
    qSequence (C 2 (qResidue 3)) 1 = (2 / 5 : ℝ) := by
  rw [qSequence_C 2 1 (by norm_num) (by norm_num)]
  simpa [ternaryOrbitTerm, replaceValuation, primeCore, qSequence_qResidue] using
    ternaryOrbitTerm_tsum

/-- The entire dyadic fiber through three consists of multiples of three. -/
theorem C_two_qResidue_three_at_three :
    qSequence (C 2 (qResidue 3)) 3 = 0 := by
  rw [qSequence_C 2 3 (by norm_num) (by norm_num)]
  have hc : primeCore 2 3 = 3 :=
    primeCore_eq_self_of_not_dvd 2 3 (by norm_num)
  calc
    _ = ∑' k : ℕ, (0 : ℝ) := by
      apply tsum_congr
      intro k
      rw [qSequence_qResidue]
      simp [replaceValuation, hc, residueFraction]
    _ = 0 := tsum_zero

/-- Conditional averaging destroys the squarefree radical-difference identity. -/
theorem C_two_qResidue_three_squareJump :
    squareJumpFunctional 2 (C 2 (qResidue 3)) = (2 / 5 : ℝ) := by
  have h2 : qSequence (C 2 (qResidue 3)) 2 =
      qSequence (C 2 (qResidue 3)) 1 := by
    simpa using (C_mem 2 (qResidue 3)) 1
  have h4 : qSequence (C 2 (qResidue 3)) 4 =
      qSequence (C 2 (qResidue 3)) 2 := by
    simpa using (C_mem 2 (qResidue 3)) 2
  rw [squareJumpFunctional_apply 2 (by decide)]
  change (qSequence (C 2 (qResidue 3)) 4 - qSequence (C 2 (qResidue 3)) 3) -
    (qSequence (C 2 (qResidue 3)) 2 - qSequence (C 2 (qResidue 3)) 1) = (2 / 5 : ℝ)
  rw [h4, h2, C_two_qResidue_three_at_one, C_two_qResidue_three_at_three]
  norm_num

/-- A positive distance remains even after arbitrary real constants are added. -/
theorem C_two_qResidue_three_error_energy_exact (f : QHilbert)
    (hf : f ∈ closureWithConstants) :
    ‖C 2 (qResidue 3) - f‖ ^ 2 = 2 / (375 * zetaTwo) +
      ‖C 2 (qResidue 3) - f -
        (1 / (75 * zetaTwo)) • squareJumpWitness 2‖ ^ 2 := by
  rw [closureWithConstants_error_energy_exact 2 (by decide) _ f hf,
    C_two_qResidue_three_squareJump]
  have hZ : zetaTwo ≠ 0 := ne_of_gt zetaTwo_pos
  have hden : 2 * zetaTwo * (((2 : ℕ) : ℝ) ^ 4 - (2 : ℕ) + 1) =
      30 * zetaTwo := by norm_num; ring
  rw [hden]
  have hfirst : (2 / 5 : ℝ) ^ 2 / (30 * zetaTwo) = 2 / (375 * zetaTwo) := by
    field_simp [hZ]
    ring
  have hsecond : (2 / 5 : ℝ) / (30 * zetaTwo) = 1 / (75 * zetaTwo) := by
    field_simp [hZ]
    ring
  rw [hfirst, hsecond]

theorem C_two_qResidue_three_error_sq_lower_bound (f : QHilbert)
    (hf : f ∈ closureWithConstants) :
    2 / (375 * zetaTwo) ≤ ‖C 2 (qResidue 3) - f‖ ^ 2 := by
  rw [C_two_qResidue_three_error_energy_exact f hf]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem C_two_qResidue_three_not_mem_closureWithConstants :
    C 2 (qResidue 3) ∉ closureWithConstants := by
  intro h
  have hz := squareJumpFunctional_zero_on_closureWithConstants 2 (by decide) h
  rw [C_two_qResidue_three_squareJump] at hz
  norm_num at hz

theorem qResidue_three_mem_closure :
    qResidue 3 ∈ ZetaTwoOptimizerStage.closure := by
  change qResidue 3 ∈ (Submodule.span ℝ
    (Set.range ZetaTwoOptimizerStage.squarefreeAtom)).topologicalClosure
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  refine ⟨1, ?_⟩
  simp [ZetaTwoOptimizerStage.squarefreeAtom, (by norm_num : Nat.Prime 3).squarefree]

/-- Actual prime resampling fails to preserve the complete squarefree closure,
even with constants allowed in the image. -/
theorem C_two_not_preserve_squarefreeClosure_even_with_constants :
    ¬ ∀ f ∈ ZetaTwoOptimizerStage.closure, C 2 f ∈ closureWithConstants := by
  intro h
  exact C_two_qResidue_three_not_mem_closureWithConstants
    (h (qResidue 3) qResidue_three_mem_closure)

/-- Uniform quantitative noncommutation for every legal projector containing g_3. -/
theorem C_two_projection_commutator_sq_lower_bound (W : Submodule ℝ QHilbert)
    [W.HasOrthogonalProjection] (hW : W ≤ closureWithConstants)
    (hthree : qResidue 3 ∈ W) :
    2 / (375 * zetaTwo) ≤
      ‖C 2 (W.starProjection (qResidue 3)) -
        W.starProjection (C 2 (qResidue 3))‖ ^ 2 := by
  rw [Submodule.starProjection_eq_self_iff.mpr hthree]
  exact C_two_qResidue_three_error_sq_lower_bound _
    (hW (W.starProjection_apply_mem _))

theorem C_two_closure_projection_commutator_sq_lower_bound :
    2 / (375 * zetaTwo) ≤
      ‖C 2 (ZetaTwoOptimizerStage.closure.starProjection (qResidue 3)) -
        ZetaTwoOptimizerStage.closure.starProjection (C 2 (qResidue 3))‖ ^ 2 :=
  C_two_projection_commutator_sq_lower_bound _ closure_le_closureWithConstants
    qResidue_three_mem_closure


/-- Every canonical stage from the inclusion of g_3 onward has a fixed
nonzero dyadic commutator on that legal atom. -/
theorem C_two_stage_projection_commutator_sq_lower_bound (N : ℕ) (hN : 2 ≤ N) :
    2 / (375 * zetaTwo) ≤
      ‖C 2 ((ZetaTwoOptimizerStage.stage N).starProjection (qResidue 3)) -
        (ZetaTwoOptimizerStage.stage N).starProjection (C 2 (qResidue 3))‖ ^ 2 := by
  apply C_two_projection_commutator_sq_lower_bound
  · apply le_trans _ closure_le_closureWithConstants
    change RiemannResearch.Analysis.ExhaustiveWalk.walkSpan
      ZetaTwoOptimizerStage.squarefreeAtom id N ≤
      (Submodule.span ℝ (Set.range ZetaTwoOptimizerStage.squarefreeAtom)).topologicalClosure
    exact (RiemannResearch.Analysis.ExhaustiveWalk.walkSpan_le _ _ _).trans
      (Submodule.le_topologicalClosure _)
  · change qResidue 3 ∈ Submodule.span ℝ
      (Set.range (fun i : Fin N => ZetaTwoOptimizerStage.squarefreeAtom (id i)))
    apply Submodule.subset_span
    refine ⟨⟨1, by omega⟩, ?_⟩
    norm_num [ZetaTwoOptimizerStage.squarefreeAtom, Nat.prime_three.squarefree]

end RiemannResearch.RH.QSquarefreeResamplingObstruction
