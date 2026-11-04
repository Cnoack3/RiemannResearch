/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.QSquarefreeMultiplierRigidity
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.ZetaTwoReciprocalCompactness
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# The real joint commutant of the shifted reciprocal and legal projection

Source: the user-provided `Pasted text(9).txt`, final paper, section 3,
November 4, 2026. The diagonal spectrum is simple. Applying this fact to the
adjoint's physical coordinate vectors identifies every commuting bounded map
as a physical multiplier; arithmetic multiplier rigidity makes it scalar.
This proof needs neither a spectral theorem nor a dense-series interchange.
-/

noncomputable section
namespace RiemannResearch.RH.QSquarefreeJointCommutant
open ZetaTwoHilbert ZetaTwoOptimizerStage QShiftedReciprocal
open QSquarefreeMultiplierRigidity

theorem B_qPoint (n : ℕ) :
    B (qPoint n) = (1 / ((n : ℝ) + 2)) • qPoint n := by
  apply qSequence_injective
  funext k
  have hs := congrFun (qSequenceLinear.map_smul (1 / ((n : ℝ) + 2)) (qPoint n)) k
  change qSequence ((1 / ((n : ℝ) + 2)) • qPoint n) k =
    (1 / ((n : ℝ) + 2))*qSequence (qPoint n) k at hs
  rw [qSequence_B, hs, qSequence_qPoint]
  by_cases hk : k=n+1
  · subst k
    simp only [qPointSequence, Nat.cast_add, Nat.cast_one]
    ring
  · simp only [qPointSequence, if_neg hk, zero_div, mul_zero]

/-- Each positive eigenvalue has exactly its one physical coordinate eigenspace. -/
theorem eigenvector_eq_qPoint (n : ℕ) (f : QHilbert)
    (hf : B f = (1 / ((n : ℝ) + 2)) • f) :
    f = (qSequence f (n+1)) • qPoint n := by
  apply qSequence_injective
  funext k
  have hs := congrFun (qSequenceLinear.map_smul (qSequence f (n+1)) (qPoint n)) k
  change qSequence ((qSequence f (n+1)) • qPoint n) k =
    (qSequence f (n+1))*qSequence (qPoint n) k at hs
  rw [hs, qSequence_qPoint]
  by_cases hk : k=n+1
  · simp [qPointSequence, hk]
  · simp only [qPointSequence, if_neg hk, mul_zero]
    have he := congrArg (fun x : QHilbert => qSequence x k) hf
    rw [qSequence_B] at he
    have hsm := congrFun (qSequenceLinear.map_smul (1 / ((n : ℝ) + 2)) f) k
    change qSequence ((1 / ((n : ℝ) + 2)) • f) k =
      (1 / ((n : ℝ) + 2))*qSequence f k at hsm
    rw [hsm] at he
    have hn0 : (n : ℝ)+2 ≠ 0 := by positivity
    have hk0 : (k : ℝ)+1 ≠ 0 := by positivity
    field_simp [hn0, hk0] at he
    have hneq : ((n : ℝ)+2)-((k : ℝ)+1) ≠ 0 := by
      intro hz
      have hcast : (k : ℝ) = ((n+1 : ℕ) : ℝ) := by
        push_cast
        linarith
      exact hk (Nat.cast_injective hcast)
    have hz : (((n : ℝ)+2)-((k : ℝ)+1))*qSequence f k = 0 := by
      nlinarith
    exact (mul_eq_zero.mp hz).resolve_left hneq

theorem B_adjoint : B.adjoint = B := by
  exact ((ContinuousLinearMap.eq_adjoint_iff B B).mpr B_symmetric).symm

/-- Every bounded map commuting with B is a literal physical multiplier. -/
theorem physical_multiplier_of_commutes_B (M : QHilbert →L[ℝ] QHilbert)
    (hcomm : ∀ f : QHilbert, M (B f) = B (M f)) :
    ∃ h : ℕ → ℝ, ∀ f n, qSequence (M f) n = h n*qSequence f n := by
  have hcomp : M.comp B = B.comp M := by
    apply ContinuousLinearMap.ext
    intro f
    exact hcomm f
  have hadj := congrArg (fun T : QHilbert →L[ℝ] QHilbert => T.adjoint) hcomp
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    B_adjoint] at hadj
  let h : ℕ → ℝ := fun k => qSequence (M.adjoint (qPoint (k-1))) k
  refine ⟨h, ?_⟩
  intro f k
  cases k with
  | zero => simp only [qSequence_zero, mul_zero]
  | succ n =>
      have hroweig : B (M.adjoint (qPoint n)) =
          (1 / ((n : ℝ) + 2)) • M.adjoint (qPoint n) := by
        have he := congrArg (fun T : QHilbert →L[ℝ] QHilbert => T (qPoint n)) hadj
        change B (M.adjoint (qPoint n)) = M.adjoint (B (qPoint n)) at he
        rw [B_qPoint, map_smul] at he
        exact he
      have hrow := eigenvector_eq_qPoint n (M.adjoint (qPoint n)) hroweig
      have he : qWeight n*qSequence (M f) (n+1) =
          qSequence (M.adjoint (qPoint n)) (n+1) *
            (qWeight n*qSequence f (n+1)) := by
        rw [← qPoint_inner n (M f), ← ContinuousLinearMap.adjoint_inner_left]
        conv_lhs => rw [hrow]
        rw [real_inner_smul_left, qPoint_inner]
      change qSequence (M f) (n+1) =
        qSequence (M.adjoint (qPoint n)) (n+1)*qSequence f (n+1)
      apply mul_left_cancel₀ (ne_of_gt (qWeight_pos n))
      nlinarith [he]

/-- The exact real-Q joint commutant consists only of scalar operators. -/
theorem scalar_of_commutes_B_projection (M : QHilbert →L[ℝ] QHilbert)
    (hB : ∀ f : QHilbert, M (B f) = B (M f))
    (hP : ∀ f : QHilbert,
      M (closure.starProjection f) = closure.starProjection (M f)) :
    ∃ c : ℝ, M = c • ContinuousLinearMap.id ℝ QHilbert := by
  obtain ⟨h, hM⟩ := physical_multiplier_of_commutes_B M hB
  have hpres : ∀ f : QHilbert, f ∈ closure → M f ∈ closure := by
    intro f hf
    have he := hP f
    rw [Submodule.starProjection_eq_self_iff.mpr hf] at he
    exact Submodule.starProjection_eq_self_iff.mp he.symm
  have hc := (preserves_closure_iff_constant h M hM).mp hpres
  refine ⟨h 1, ?_⟩
  apply ContinuousLinearMap.ext
  intro f
  change M f = (h 1) • f
  apply qSequence_injective
  funext n
  have hs := congrFun (qSequenceLinear.map_smul (h 1) f) n
  change qSequence ((h 1) • f) n = (h 1)*qSequence f n at hs
  rw [hM, hs]
  cases n with
  | zero => simp only [qSequence_zero, mul_zero]
  | succ n => rw [hc (n+1) (by omega)]

end RiemannResearch.RH.QSquarefreeJointCommutant
