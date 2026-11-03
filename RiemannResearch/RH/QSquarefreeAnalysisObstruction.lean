/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QDivisorHilbertBasis
import RiemannResearch.RH.QHilbertConvergence
import RiemannResearch.RH.QDivisibilityDensity
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Positive error forced by squarefree analysis coordinates

Source: Prime Tensor CRT RH Research Project (2 November 2026), section 6.2,
for the squarefree-row warning. The explicit two-site completion of squares
below strengthens that warning and applies to the actual Q norm.
Analysis row squarefreeness and legal synthesis squarefreeness have different
roles: this obstruction concerns analysis rows, not the legal closure.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeAnalysisObstruction
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative
open QDivisibilityDensity QDivisorHilbert

theorem pair_obstruction (f : QHilbert) (hf : qSequence f 2 = qSequence f 4) :
    1 / (180 * zetaTwo) ≤ ‖qResidue 3 - f‖ ^ 2 := by
  let e := qResidue 3 - f
  have hs := qSequence_square_summable e
  have hle := hs.sum_le_tsum ({2,4} : Finset ℕ)
    (fun k _ => mul_nonneg (positiveQWeight_nonneg k) (sq_nonneg (qSequence e k)))
  rw [← qNorm_weighted_sq] at hle
  have hseq : qSequence e = fun n => qSequence (qResidue 3) n - qSequence f n :=
    qSequenceLinear.map_sub (qResidue 3) f
  simp only [Finset.sum_insert, Finset.mem_singleton, show (2:ℕ) ≠ 4 by decide,
    not_false_eq_true, Finset.sum_singleton, hseq, qSequence_qResidue, hf] at hle
  norm_num only [residueFraction, Nat.reduceMod, Nat.cast_ofNat] at hle
  have hid : positiveQWeight 2 * (2/3-qSequence f 4)^2 +
      positiveQWeight 4 * (1/3-qSequence f 4)^2 =
      1/(180*zetaTwo)+(5/(16*zetaTwo))*(qSequence f 4-3/5)^2 := by
    unfold positiveQWeight
    norm_num
    field_simp
    ring
  have hnon : 0 ≤ (5/(16*zetaTwo))*(qSequence f 4-3/5)^2 := by
    have := zetaTwo_pos
    positivity
  change _ ≤ ‖qResidue 3-f‖^2 at hle
  linarith


theorem squarefree_wavelet_two_four (r : ℕ) (hr : Squarefree r) :
    qSequence (divisorWavelet r) 2 = qSequence (divisorWavelet r) 4 := by
  change qSequenceLinear (divisorWavelet r) 2 = qSequenceLinear (divisorWavelet r) 4
  unfold divisorWavelet
  rw [map_sum]
  simp only [Finset.sum_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro d hd
  have hs : Squarefree d := by
    intro x hx
    exact hr x (dvd_trans hx (Nat.dvd_of_mem_divisors hd))
  have he : d ∣ 4 ↔ d ∣ 2 := by
    simpa using hs.dvd_pow_iff_dvd (y := 2) (by decide : (2 : ℕ) ≠ 0)
  have hi : qSequenceLinear (qDivisor d) 2 = qSequenceLinear (qDivisor d) 4 := by
    change qSequence (qDivisor d) 2 = qSequence (qDivisor d) 4
    rw [qSequence_qDivisor]
    simp only [positiveDivisor, show (2:ℕ) ≠ 0 by decide,
      show (4:ℕ) ≠ 0 by decide, if_false, he]
  exact congrArg (fun x : ℝ => ((ArithmeticFunction.moebius (r / d) : ℝ) *
    (d : ℝ)^2) * x) hi

def squarefreeWaveletSpan : Submodule ℝ QHilbert :=
  Submodule.span ℝ (Set.range (fun r : {r : ℕ // Squarefree r} => divisorWavelet r.val))

theorem squarefree_span_two_four {f : QHilbert} (hf : f ∈ squarefreeWaveletSpan) :
    qSequence f 2 = qSequence f 4 := by
  have hle : squarefreeWaveletSpan ≤ (qEvalCLM 2 - qEvalCLM 4).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨r, rfl⟩
    change qEvalCLM 2 (divisorWavelet r.val) - qEvalCLM 4 (divisorWavelet r.val) = 0
    simp only [qEvalCLM_apply, squarefree_wavelet_two_four r.val r.property, sub_self]
  have h := hle hf
  change qEvalCLM 2 f - qEvalCLM 4 f = 0 at h
  simpa only [qEvalCLM_apply, sub_eq_zero] using h

theorem squarefree_closure_two_four {f : QHilbert}
    (hf : f ∈ squarefreeWaveletSpan.topologicalClosure) :
    qSequence f 2 = qSequence f 4 := by
  have hle : squarefreeWaveletSpan ≤ (qEvalCLM 2 - qEvalCLM 4).ker := by
    intro g hg
    change qEvalCLM 2 g - qEvalCLM 4 g = 0
    simp only [qEvalCLM_apply, squarefree_span_two_four hg, sub_self]
  have h := closure_minimal (fun g hg => hle hg)
    (qEvalCLM 2 - qEvalCLM 4).isClosed_ker hf
  change qEvalCLM 2 f - qEvalCLM 4 f = 0 at h
  simpa only [qEvalCLM_apply, sub_eq_zero] using h

theorem residue_three_distance_lower {f : QHilbert}
    (hf : f ∈ squarefreeWaveletSpan.topologicalClosure) :
    1/(180*zetaTwo) ≤ ‖qResidue 3 - f‖^2 :=
  pair_obstruction f (squarefree_closure_two_four hf)

theorem residue_three_not_mem :
    qResidue 3 ∉ squarefreeWaveletSpan.topologicalClosure := by
  intro h
  have he := residue_three_distance_lower h
  have hp : 0 < 1/(180*zetaTwo) := by have := zetaTwo_pos; positivity
  simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] at he
  linarith

end RiemannResearch.RH.QSquarefreeAnalysisObstruction
