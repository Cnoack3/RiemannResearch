/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.QFloorDilation
import RiemannResearch.RH.QMobiusExactHead
import RiemannResearch.RH.QSignedTailRigidity
import RiemannResearch.RH.QSquarefreeSignedPowerMoments
import RiemannResearch.RH.QAnnihilatorTailEscape
import RiemannResearch.Analysis.CofinalPrimeResiduePairing
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Lean.Elab.Tactic.Omega

/-!
# Localized residue pairing for the full conductor closure

Source: Full_Conductor_RH_Projection_Machinery, 6 November 2026, task A3.
The generic signed-charge estimate in CofinalPrimeResiduePairing needs
only one integer residue probe exceeding Y, not primality. Full legal
membership supplies it for every such integer. The exact-head pairing is
valid for every N, without requiring N+1 to be squarefree.
The two independent physical cutoffs and both complete tails are retained.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QFullLocalResiduePairing
open ZetaTwoHilbert QSignedTailRigidity QAnnihilatorTailEscape

theorem annihilator_defect_hasSum (u : QHilbert)
    (hu : u ∈ QFullResidueProjection.closureᗮ) (N : ℕ) :
    HasSum (fun n : ℕ => signedCoefficient u n * qSequence (defect N) n)
      (inner ℝ qOne u) := by
  have hz := Submodule.inner_right_of_mem_orthogonal
    (QFullResidueProjection.legalSpan.le_topologicalClosure
      (QMobiusExactHead.exactHead_mem_legalSpan N)) hu
  have he : inner ℝ u (defect N) = inner ℝ qOne u := by
    rw [real_inner_comm, defect, inner_sub_left, hz, sub_zero]
  rw [← he, qInner_weighted]
  exact (qSequence_product_summable u (defect N)).hasSum

theorem annihilator_residue_hasSum (u : QHilbert)
    (hu : u ∈ QFullResidueProjection.closureᗮ) (m : ℕ) (hm : 0 < m) :
    HasSum (fun n : ℕ => signedCoefficient u n * ((n % m : ℕ) : ℝ)) 0 := by
  apply residue_charge_hasSum_zero u m hm
  rw [real_inner_comm]
  exact Submodule.inner_right_of_mem_orthogonal
    (QFullResidueProjection.legalSpan.le_topologicalClosure
      (QFloorDilation.qResidue_mem_legalSpan m hm)) hu

/-- Either sign may be chosen independently at every outer cutoff. -/
theorem annihilator_mean_le_local_residue_head (u : QHilbert)
    (hu : u ∈ QFullResidueProjection.closureᗮ)
    (N X Y m : ℕ) (σ δ K : ℝ) (hσ : |σ| = 1)
    (hYX : Y ≤ X) (hYm : Y < m) (hδ : 0 ≤ δ)
    (hlin : ∀ n : ℕ, n ≤ Y → |qSequence (defect N) n| ≤ δ * n)
    (hbound : ∀ n : ℕ, Y < n → |qSequence (defect N) n| ≤ K) :
    |inner ℝ qOne u| ≤
      2 * δ * (∑ n ∈ Finset.range (X + 1),
        max (σ * signedCoefficient u n) 0 * (n : ℝ)) +
      (δ * (m : ℝ)) * (∑' n : ℕ, if X < n then |signedCoefficient u n| else 0) +
      K * (∑' n : ℕ, if Y < n then |signedCoefficient u n| else 0) := by
  have hm := (annihilator_defect_hasSum u hu N).mul_left σ
  have hz := (annihilator_residue_hasSum u hu m (by omega)).mul_left σ
  have h := RiemannResearch.Analysis.pairing_le_local_residue_head
    (fun n => σ * signedCoefficient u n) (qSequence (defect N))
    X Y m (σ * inner ℝ qOne u) δ K hYX hYm hδ
    ((signedCoefficient_summable u).mul_left σ)
    (by simpa only [mul_assoc] using hm)
    (by simpa only [mul_assoc, mul_zero] using hz) hlin hbound
  simpa only [abs_mul, hσ, one_mul] using h

end RiemannResearch.RH.QFullLocalResiduePairing
