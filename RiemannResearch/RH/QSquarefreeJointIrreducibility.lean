/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.QSquarefreeJointCommutant
import RiemannResearch.Analysis.SymmetricInvariantProjection
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Real irreducibility of the reciprocal / squarefree-projection pair

Source: the user-provided paper, final section 3, November 4, 2026.
Every closed common invariant subspace has a scalar orthogonal projection;
idempotence then makes it either zero or the whole Hilbert space.
-/

noncomputable section
namespace RiemannResearch.RH.QSquarefreeJointCommutant
open ZetaTwoHilbert ZetaTwoOptimizerStage QShiftedReciprocal

theorem invariant_subspace_trivial (W : Submodule ℝ QHilbert)
    [W.HasOrthogonalProjection]
    (hB : ∀ f : QHilbert, f ∈ W → B f ∈ W)
    (hP : ∀ f : QHilbert, f ∈ W → closure.starProjection f ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  obtain ⟨c, hc⟩ := scalar_of_commutes_B_projection W.starProjection
    (Submodule.starProjection_commutes_of_symmetric_preserves W B B_symmetric hB)
    (Submodule.starProjection_commutes_of_symmetric_preserves W closure.starProjection
      (Submodule.inner_starProjection_left_eq_right closure) hP)
  have heval (t : ℝ) : qSequence (t • qOne) 1 = t := by
    have he := congrFun (qSequenceLinear.map_smul t qOne) 1
    change qSequence (t • qOne) 1 = t*qSequence qOne 1 at he
    have h1 : qSequence qOne 1 = 1 := by
      rw [qSequence_qOne]
      norm_num [qOneSequence]
    rw [h1, mul_one] at he
    exact he
  have hidem : W.starProjection (W.starProjection qOne) = W.starProjection qOne :=
    Submodule.starProjection_eq_self_iff.mpr (W.starProjection_apply_mem qOne)
  rw [hc] at hidem
  change c • (c • qOne) = c • qOne at hidem
  rw [smul_smul] at hidem
  have hc2 : c*c=c := by
    simpa only [heval] using congrArg (fun x : QHilbert => qSequence x 1) hidem
  have hz : c*(c-1)=0 := by nlinarith
  rcases mul_eq_zero.mp hz with hzero | hone
  · left
    apply le_antisymm
    · intro x hx
      have hfix := Submodule.starProjection_eq_self_iff.mpr hx
      rw [hc, hzero] at hfix
      simpa using hfix.symm
    · exact bot_le
  · right
    have hone' : c=1 := sub_eq_zero.mp hone
    apply top_unique
    intro x hx
    apply Submodule.starProjection_eq_self_iff.mp
    rw [hc, hone']
    simp

end RiemannResearch.RH.QSquarefreeJointCommutant
