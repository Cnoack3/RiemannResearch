/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeBoundary
import RiemannResearch.RH.QSquarefreeReciprocalObstruction
import RiemannResearch.RH.QDivisibilityDensity
import RiemannResearch.RH.QResidueFirstNormalization
import RiemannResearch.Analysis.CStarCompressionDefect
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Concrete squarefree leakage and failure of multiplicative closure

Source: the user-provided `Pasted text(9).txt`, final paper, sections 4 and 6,
November 4, 2026. Four physical coordinates certify the nonzero leakage and
the fact that g_2 g_3 is outside the legal closure. The complete operator
defect has the positive lower bound 1/(90 zeta(2)).
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeCompressionLeakage
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open QShiftedReciprocal QSquarefreeBoundary QSquarefreeReciprocalObstruction
open QResidueFirstNormalization ArithmeticCumulative

theorem primeProduct23_bounded (n : ℕ) :
    |residueFraction 2 n * residueFraction 3 n| ≤ 1 := by
  have h2 := Nat.mod_lt n (by decide : 0 < 2)
  have h3 := Nat.mod_lt n (by decide : 0 < 3)
  have hc2 : n%2=0 ∨ n%2=1 := by omega
  have hc3 : n%3=0 ∨ n%3=1 ∨ n%3=2 := by omega
  rcases hc2 with h | h <;> rcases hc3 with h' | h' | h' <;>
    norm_num [residueFraction, h, h']

def primeProduct23 : QHilbert :=
  encodeQ (fun n => residueFraction 2 n * residueFraction 3 n)
    (boundedQ_square_summable _ 1 (by norm_num) primeProduct23_bounded)

theorem primeProduct23_sequence (n : ℕ) :
    qSequence primeProduct23 n = residueFraction 2 n * residueFraction 3 n := by
  exact congrFun (qSequence_encodeQ _ _ (by norm_num [residueFraction])) n

theorem fourSiteFunctional_primeProduct23 :
    fourSiteFunctional primeProduct23 = (1/6 : ℝ) := by
  rw [fourSiteFunctional_apply]
  simp only [primeProduct23_sequence]
  norm_num [residueFraction]

theorem primeProduct23_not_mem_closure : primeProduct23 ∉ closure := by
  intro h
  have hz := fourSiteFunctional_zero_on_closure h
  rw [fourSiteFunctional_primeProduct23] at hz
  norm_num at hz

/-- The exact four-coordinate representation of the continuous annihilator. -/
theorem fourSiteFunctional_normalized (f : QHilbert) :
    fourSiteFunctional f = Real.sqrt zetaTwo *
      (f 0 - 2*f 1 - 3*f 2 + 4*f 3) := by
  have hs (n : ℕ) : qSequence f (n+1) =
      Real.sqrt zetaTwo * ((n+1 : ℕ) : ℝ) * f n := by
    rw [qSequence_succ]
    apply (div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr (qWeight_pos n)))).mpr
    have hw : (Real.sqrt (qWeight n)*Real.sqrt zetaTwo)*((n+1 : ℕ) : ℝ) = 1 := by
      rw [QDivisibilityDensity.sqrt_qWeight_mul_sqrt_zetaTwo]
      field_simp
    calc
      f n = f n * ((Real.sqrt (qWeight n)*Real.sqrt zetaTwo)*((n+1 : ℕ) : ℝ)) := by
        rw [hw, mul_one]
      _ = _ := by ring
  rw [fourSiteFunctional_apply, hs 3, hs 2, hs 1, hs 0]
  norm_num
  ring

/-- The squared functional estimate, avoiding square-root normalization choices. -/
theorem fourSiteFunctional_sq_le (f : QHilbert) :
    (fourSiteFunctional f)^2 ≤ 30*zetaTwo*‖f‖^2 := by
  have hhead := Summable.sum_le_tsum (Finset.range 4)
    (fun n _ => sq_nonneg (f n)) (qCoordinate_square_summable f)
  norm_num [Finset.sum_range_succ] at hhead
  rw [← qNorm_sq f] at hhead
  have hcs : (f 0-2*f 1-3*f 2+4*f 3)^2 ≤
      30*((f 0)^2+(f 1)^2+(f 2)^2+(f 3)^2) := by
    nlinarith [sq_nonneg (2*f 0+f 1), sq_nonneg (3*f 0+f 2),
      sq_nonneg (4*f 0-f 3), sq_nonneg (3*f 1-2*f 2),
      sq_nonneg (4*f 1+2*f 3), sq_nonneg (4*f 2+3*f 3)]
  have hshape : (f 0-2*f 1-3*f 2+4*f 3)^2 ≤ 30*‖f‖^2 := by
    linarith
  rw [fourSiteFunctional_normalized, mul_pow, Real.sq_sqrt zetaTwo_pos.le]
  nlinarith [mul_le_mul_of_nonneg_left hshape zetaTwo_pos.le]

def twiceB : QHilbert →L[ℝ] QHilbert := (2 : ℝ) • B

def leakage : QHilbert →L[ℝ] QHilbert :=
  (1 - closure.starProjection) * twiceB * closure.starProjection

theorem leakage_apply (f : QHilbert) :
    leakage f = (2 : ℝ) • B (closure.starProjection f) -
      closure.starProjection ((2 : ℝ) • B (closure.starProjection f)) := rfl

theorem fourSiteFunctional_leakage_qResidue_two :
    fourSiteFunctional (leakage (qResidue 2)) = (1/4 : ℝ) := by
  rw [leakage_apply, Submodule.starProjection_eq_self_iff.mpr qResidue_two_mem,
    map_sub, fourSiteFunctional_zero_on_closure (closure.starProjection_apply_mem _),
    sub_zero, map_smul, fourSiteFunctional_B_qResidue_two]
  norm_num

/-- A quantitative, unconditional obstruction to multiplier invariance. -/
theorem leakage_norm_sq_lower :
    1/(90*zetaTwo) ≤ ‖leakage‖^2 := by
  have hf := fourSiteFunctional_sq_le (leakage (qResidue 2))
  rw [fourSiteFunctional_leakage_qResidue_two] at hf
  have ho := leakage.le_opNorm (qResidue 2)
  have hs : ‖leakage (qResidue 2)‖^2 ≤
      ‖leakage‖^2 * ‖qResidue 2‖^2 := by
    have hmul := mul_le_mul ho ho (norm_nonneg (leakage (qResidue 2)))
      (mul_nonneg (norm_nonneg leakage) (norm_nonneg (qResidue 2)))
    simpa only [← pow_two, mul_pow] using hmul
  rw [qResidue_two_norm_sq] at hs
  have hm := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ 30*zetaTwo from mul_nonneg (by norm_num) zetaTwo_pos.le)
  apply (div_le_iff₀ (show 0 < 90*zetaTwo from mul_pos (by norm_num) zetaTwo_pos)).mpr
  nlinarith

def compressionDefect : QHilbert →L[ℝ] QHilbert :=
  closure.starProjection * star twiceB * twiceB * closure.starProjection -
    star (closure.starProjection * twiceB * closure.starProjection) *
      (closure.starProjection * twiceB * closure.starProjection)

theorem compressionDefect_norm_eq : ‖compressionDefect‖ = ‖leakage‖^2 := by
  exact CStarRing.norm_compression_square_defect closure.starProjection twiceB
    (Submodule.isIdempotentElem_starProjection closure)
    (isSelfAdjoint_starProjection closure)

theorem compressionDefect_norm_lower :
    1/(90*zetaTwo) ≤ ‖compressionDefect‖ := by
  rw [compressionDefect_norm_eq]
  exact leakage_norm_sq_lower

theorem compressionDefect_ne_zero : compressionDefect ≠ 0 := by
  intro h
  have hbound := compressionDefect_norm_lower
  rw [h, norm_zero] at hbound
  have hp : 0 < 1/(90*zetaTwo) := div_pos zero_lt_one (mul_pos (by norm_num) zetaTwo_pos)
  linarith

end RiemannResearch.RH.QSquarefreeCompressionLeakage
