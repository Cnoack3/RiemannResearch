/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QCRTPeriodHeadBalance
import RiemannResearch.RH.QSquarefreeHeadStep
import RiemannResearch.RH.QResidueHeadSpace
import RiemannResearch.RH.QSquarefreeAffineHead
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.QCRTCoprimeApproximation
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.NormalizedResidueExactHeadCharges
import RiemannResearch.Analysis.FiniteGramCapacity
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Actual minimum-energy head cost and a finite acceptance criterion

Source: the user-provided period-first research task, 28 October 2026.
The proof adapts the already checked QSquarefreeHeadStep tangent-space
capacity and correction completion to the minimum-norm `minimumAt` family.
That family differs from the older optimizer minimizing distance to one.
The old definitions and results remain unchanged.

All energies and capacities use the entire Q Hilbert space. The acceptance
criterion decides one finite head step, conditional on its actual capacity
and mismatch. It asserts no all-stage arithmetic estimate or RH consequence.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QCRTMinimumHeadCost
open ZetaTwoHilbert QSquarefreeLatticePackets QResidueHeadSpace
open QSquarefreeAffineHead QCRTPeriodHeadBalance QSquarefreeHeadStep
open RiemannResearch.Analysis.FiniteGramCapacity

/-- The exact cost of adding site n to the actual minimum-norm head.
The capacity permits every old zero-head direction. -/
theorem minimumAt_single_head_cost (j n r : ℕ) (hn : 1 < n)
    (hnj : n ≤ j + 1) (hnL : n ∣ primorial (j + 2))
    (hr : r ∈ conductors (primorial (j + 2))) (hrn : n < r) :
    ‖minimumAt j n‖ ^ 2 = ‖minimumAt j (n - 1)‖ ^ 2 +
      (1 - qSequence (minimumAt j (n - 1)) n) ^ 2 /
        stepCapacity n (primorial (j + 2)) r hr := by
  let L := primorial (j + 2)
  let δ := 1 - qSequence (minimumAt j (n - 1)) n
  let u := (δ / stepCapacity n L r hr) • stepNormal n L r hr
  have hL : 0 < L := primorial_pos _
  have hold : minimumAt j (n - 1) ∈ dictionary (conductors L) := by
    rw [← divisorStage_eq_dictionary L hL]
    exact minimumAt_mem j (n - 1)
  have hnew : minimumAt j n ∈ dictionary (conductors L) := by
    rw [← divisorStage_eq_dictionary L hL]
    exact minimumAt_mem j n
  have holdhead : ∀ k, 0 < k → k ≤ n - 1 →
      qSequence (minimumAt j (n - 1)) k = 1 :=
    minimumAt_head j (n - 1) (by omega)
  have hnewhead : ∀ k, 0 < k → k ≤ n → qSequence (minimumAt j n) k = 1 :=
    minimumAt_head j n hnj
  have hu : u ∈ zeroHeadSpan (conductors L) (n - 1) r :=
    Submodule.smul_mem _ _ (stepNormal_mem n L r hr)
  have hcap := ne_of_gt (stepCapacity_pos n L r hn hL hnL hr hrn)
  have huvalue : qSequence u n = δ := by
    change qSequenceLinear ((_ : ℝ) • _) n = δ
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    change δ / stepCapacity n L r hr * qSequence (stepNormal n L r hr) n = δ
    rw [stepNormal_sequence n L r (by omega) hr hrn, div_mul_cancel₀ _ hcap]
  have huenergy : ‖u‖ ^ 2 = δ ^ 2 / stepCapacity n L r hr :=
    scaled_source_energy _ _ (stepSource_ne_zero n L r hn hL hnL hrn) δ
  have hrepairmem : minimumAt j (n - 1) + u ∈ divisorStage L := by
    rw [divisorStage_eq_dictionary L hL]
    exact (dictionary (conductors L)).add_mem hold
      (zeroHeadSpan_le_dictionary _ _ _ hr hu)
  have hrepairhead : ∀ k, 0 < k → k ≤ n →
      qSequence (minimumAt j (n - 1) + u) k = 1 := by
    intro k hk hkn
    change qSequenceLinear (_ + _) k = 1
    simp only [map_add, Pi.add_apply]
    change qSequence (minimumAt j (n - 1)) k + qSequence u k = 1
    by_cases he : k = n
    · subst k
      rw [huvalue]
      dsimp [δ]
      ring
    · rw [holdhead k hk (by omega),
        zeroHeadSpan_le_headNull _ _ _ (by omega) hu k hk (by omega), add_zero]
  have hupper := minimumAt_completion j n hnj _ hrepairmem hrepairhead
  have hcompletion := minimumAt_completion j (n - 1) (by omega) _ hrepairmem
    (fun k hk hkn => hrepairhead k hk (by omega))
  simp only [add_sub_cancel_left] at hcompletion
  rw [huenergy] at hcompletion
  have hdiff : minimumAt j n - minimumAt j (n - 1) ∈
      zeroHeadSpan (conductors L) (n - 1) r := by
    apply (exact_head_iff_sub_mem_zeroHeadSpan (conductors L) (conductor_gt_one L)
      (n - 1) r (by omega) hr (by omega) (minimumAt j (n - 1))
      hold holdhead _).mp
    exact ⟨hnew, fun k hk hkn => hnewhead k hk (by omega)⟩
  have hvalue : qSequence (minimumAt j n - minimumAt j (n - 1)) n = δ := by
    change qSequenceLinear (_ - _) n = δ
    simp only [map_sub, Pi.sub_apply]
    change qSequence (minimumAt j n) n - qSequence (minimumAt j (n - 1)) n = δ
    rw [hnewhead n (by omega) le_rfl]
  have hcorr := correction_completion n L r hn hL hnL hr hrn _ hdiff δ hvalue
  have hcost := minimumAt_head_cost j (n - 1) n (by omega)
  change ‖minimumAt j n‖ ^ 2 = ‖minimumAt j (n - 1)‖ ^ 2 +
    δ ^ 2 / stepCapacity n L r hr
  apply le_antisymm
  · have hp := sq_nonneg ‖minimumAt j (n - 1) + u - minimumAt j n‖
    linarith
  · rw [hcost, hcorr]
    have hp := sq_nonneg ‖minimumAt j n - minimumAt j (n - 1) -
      (δ / stepCapacity n L r hr) • stepNormal n L r hr‖
    linarith

/-- The physical mismatch is exactly the new conductor coefficient's
deviation from its forced Mobius value. No cross term is discarded. -/
theorem minimumAt_single_head_coefficient_cost (j n r : ℕ) (hn : 1 < n)
    (hnj : n ≤ j + 1) (hnL : n ∣ primorial (j + 2))
    (hr : r ∈ conductors (primorial (j + 2))) (hrn : n < r)
    (c : ℕ → ℝ)
    (hc : (∑ d ∈ conductors (primorial (j + 2)), c d • qResidue d) =
      minimumAt j (n - 1)) :
    ‖minimumAt j n‖ ^ 2 = ‖minimumAt j (n - 1)‖ ^ 2 +
      (c n + (ArithmeticFunction.moebius n : ℝ)) ^ 2 /
        stepCapacity n (primorial (j + 2)) r hr := by
  have hm := Pareto.residueFraction_exact_head_next_coefficient
    (conductors (primorial (j + 2))) c n hn (by
      intro k hk hkn
      rw [← synthesis_sequence, hc]
      exact minimumAt_head j (n - 1) (by omega) k hk (by omega))
  have hnmem : n ∈ conductors (primorial (j + 2)) :=
    Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨hnL, primorial_ne_zero _⟩, hn⟩
  rw [← synthesis_sequence, hc, if_pos hnmem] at hm
  simpa only [hm] using minimumAt_single_head_cost j n r hn hnj hnL hr hrn

/-- A head increment respects a proposed ceiling exactly when the squared
mismatch is covered by the available energy slack times the full capacity. -/
theorem minimumAt_head_ceiling_iff (j n r : ℕ) (hn : 1 < n)
    (hnj : n ≤ j + 1) (hnL : n ∣ primorial (j + 2))
    (hr : r ∈ conductors (primorial (j + 2))) (hrn : n < r) (C : ℝ) :
    ‖minimumAt j n‖ ^ 2 ≤ C ↔
      (1 - qSequence (minimumAt j (n - 1)) n) ^ 2 ≤
        (C - ‖minimumAt j (n - 1)‖ ^ 2) *
          stepCapacity n (primorial (j + 2)) r hr := by
  have hcap := stepCapacity_pos n (primorial (j + 2)) r hn (primorial_pos _)
    hnL hr hrn
  rw [minimumAt_single_head_cost j n r hn hnj hnL hr hrn]
  constructor
  · intro h
    apply (div_le_iff₀ hcap).mp
    linarith
  · intro h
    have he := (div_le_iff₀ hcap).mpr h
    linarith

end RiemannResearch.RH.QCRTMinimumHeadCost
