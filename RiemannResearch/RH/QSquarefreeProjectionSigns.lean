/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

/-!
# Pointwise signs of the actual squarefree projection residual

Source: the user's questions about the limiting projection and negative residual
values, 25 October 2026. Positivity of prime residue atoms gives the proof below.
This uses only squarefree legality; no all-conductor or dilation annihilator
theorem is applied to the smaller space. Nonzero residuals must have both signs.
It is not asserted that the actual limiting residual is nonzero.
-/

noncomputable section
namespace RiemannResearch.RH.QSquarefreeProjectionSigns
open ZetaTwoHilbert ZetaTwoOptimizerStage ZetaTwoProbability ArithmeticCumulative
open RiemannResearch.Analysis.ExhaustiveWalk

theorem prime_atom_mem_closure (p : ℕ) (hp : p.Prime) :
    qResidue p ∈ closure := by
  change qResidue p ∈ (Submodule.span ℝ (Set.range squarefreeAtom)).topologicalClosure
  apply (Submodule.span ℝ (Set.range squarefreeAtom)).le_topologicalClosure
  apply Submodule.subset_span
  refine ⟨p - 2, ?_⟩
  have he : p - 2 + 2 = p := Nat.sub_add_cancel hp.two_le
  simp [squarefreeAtom, he, hp.squarefree]

private theorem atom_sequence_nonneg (d n : ℕ) :
    0 ≤ qSequence (qResidue d) n := by
  rw [qSequence_qResidue]
  unfold residueFraction
  positivity

/-- Prime tests detect every positive coordinate of a nonnegative annihilator. -/
theorem coordinate_eq_zero_of_orthogonal_nonneg
    (r : QHilbert) (hr : r ∈ closureᗮ)
    (hpos : ∀ n, 0 ≤ qSequence r n) (n : ℕ) :
    qSequence r n = 0 := by
  by_cases hn : n = 0
  · simp [hn]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  obtain ⟨p, hpn, hp⟩ := Nat.exists_infinite_primes (n + 1)
  have hnlt : n < p := by omega
  have hmem := prime_atom_mem_closure p hp
  have horth : inner ℝ r (qResidue p) = 0 := by
    rw [real_inner_comm]
    exact (closure.mem_orthogonal r).mp hr _ hmem
  have hsum := qSequence_product_summable r (qResidue p)
  have ht := hsum.le_tsum n (fun k _ =>
    mul_nonneg (mul_nonneg (positiveQWeight_nonneg k) (hpos k))
      (atom_sequence_nonneg p k))
  rw [← qInner_weighted, horth] at ht
  have hw : 0 < positiveQWeight n := by
    have hZ := zetaTwo_pos
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    unfold positiveQWeight
    positivity
  have ha : 0 < qSequence (qResidue p) n := by
    rw [qSequence_qResidue]
    unfold residueFraction
    rw [Nat.mod_eq_of_lt hnlt]
    apply div_pos
    · exact_mod_cast hnpos
    · exact_mod_cast hp.pos
  have hz : positiveQWeight n * qSequence r n * qSequence (qResidue p) n = 0 :=
    le_antisymm ht (mul_nonneg (mul_nonneg hw.le (hpos n)) ha.le)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (ne_of_gt ha))).resolve_left
    (ne_of_gt hw)

theorem orthogonal_eq_zero_of_nonneg (r : QHilbert) (hr : r ∈ closureᗮ)
    (hpos : ∀ n, 0 ≤ qSequence r n) : r = 0 := by
  apply qSequence_injective
  funext n
  rw [coordinate_eq_zero_of_orthogonal_nonneg r hr hpos n]
  change 0 = qSequenceLinear 0 n
  rw [map_zero]
  rfl

theorem orthogonal_eq_zero_of_nonpos (r : QHilbert) (hr : r ∈ closureᗮ)
    (hneg : ∀ n, qSequence r n ≤ 0) : r = 0 := by
  have hn : ∀ n, 0 ≤ qSequence (-r) n := by
    intro n
    change 0 ≤ qSequenceLinear (-r) n
    rw [map_neg]
    change 0 ≤ -qSequence r n
    exact neg_nonneg.mpr (hneg n)
  exact neg_eq_zero.mp (orthogonal_eq_zero_of_nonneg (-r) ((closureᗮ).neg_mem hr) hn)

/-- This is a global sign conclusion, not an assertion of eventual sign changes. -/
theorem nonzero_orthogonal_has_both_signs (r : QHilbert) (hr : r ∈ closureᗮ)
    (hne : r ≠ 0) :
    (∃ n, 0 < qSequence r n) ∧ (∃ n, qSequence r n < 0) := by
  constructor
  · by_contra! h
    exact hne (orthogonal_eq_zero_of_nonpos r hr h)
  · by_contra! h
    exact hne (orthogonal_eq_zero_of_nonneg r hr h)

theorem limitingResidual_mem_orthogonal : limitingResidual ∈ closureᗮ :=
  Submodule.sub_starProjection_mem_orthogonal qOne

theorem limitingResidual_has_both_signs (hne : limitingResidual ≠ 0) :
    (∃ n, 0 < qSequence limitingResidual n) ∧
      (∃ n, qSequence limitingResidual n < 0) :=
  nonzero_orthogonal_has_both_signs _ limitingResidual_mem_orthogonal hne

theorem limitingResidual_sequence (n : ℕ) (hn : 0 < n) :
    qSequence limitingResidual n =
      1 - qSequence (closure.starProjection qOne) n := by
  change qSequenceLinear (qOne - closure.starProjection qOne) n = _
  rw [map_sub]
  change qSequence qOne n - qSequence (closure.starProjection qOne) n = _
  rw [qSequence_qOne]
  simp [qOneSequence, Nat.ne_of_gt hn]

/-- A pointwise upper bound by one would force equality; it is not automatic. -/
theorem projection_le_one_iff_eq :
    (∀ n, 0 < n → qSequence (closure.starProjection qOne) n ≤ 1) ↔
      closure.starProjection qOne = qOne := by
  constructor
  · intro h
    have hz : limitingResidual = 0 := by
      apply orthogonal_eq_zero_of_nonneg _ limitingResidual_mem_orthogonal
      intro n
      by_cases hn : n = 0
      · simp [hn]
      rw [limitingResidual_sequence n (Nat.pos_of_ne_zero hn)]
      exact sub_nonneg.mpr (h n (Nat.pos_of_ne_zero hn))
    exact (sub_eq_zero.mp hz).symm
  · intro h n hn
    rw [h, qSequence_qOne]
    simp [qOneSequence, Nat.ne_of_gt hn]

theorem projection_ge_one_iff_eq :
    (∀ n, 0 < n → 1 ≤ qSequence (closure.starProjection qOne) n) ↔
      closure.starProjection qOne = qOne := by
  constructor
  · intro h
    have hz : limitingResidual = 0 := by
      apply orthogonal_eq_zero_of_nonpos _ limitingResidual_mem_orthogonal
      intro n
      by_cases hn : n = 0
      · simp [hn]
      rw [limitingResidual_sequence n (Nat.pos_of_ne_zero hn)]
      exact sub_nonpos.mpr (h n (Nat.pos_of_ne_zero hn))
    exact (sub_eq_zero.mp hz).symm
  · intro h n hn
    rw [h, qSequence_qOne]
    simp [qOneSequence, Nat.ne_of_gt hn]

/-- A strict projection has both overshoot and undershoot of the constant target. -/
theorem strict_projection_overshoots_and_undershoots
    (hne : closure.starProjection qOne ≠ qOne) :
    (∃ n, 0 < n ∧ 1 < qSequence (closure.starProjection qOne) n) ∧
      (∃ n, 0 < n ∧ qSequence (closure.starProjection qOne) n < 1) := by
  constructor
  · by_contra! h
    exact hne (projection_le_one_iff_eq.mp h)
  · by_contra! h
    exact hne (projection_ge_one_iff_eq.mp h)

end RiemannResearch.RH.QSquarefreeProjectionSigns
