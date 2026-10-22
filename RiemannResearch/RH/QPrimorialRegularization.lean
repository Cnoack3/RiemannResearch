/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.PrimitiveRegularization
import RiemannResearch.RH.QPhysicalDifference
import RiemannResearch.RH.QPrimitiveEnergyClosure
import RiemannResearch.RH.QSquarefreePrimorialCofinality
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Finite primorial regularization and strict complete-energy certificates

Source: user-provided Squarefree_Primitive_Energy_Regularization_2026-10-17,
Sections 8, 9 and 18. The fixed-penalty approximation uses the standard
Galerkin method; every signed and norm-square remainder is retained.
The line certificate is an explicit scalar completion of the same objective.

For any positive penalties tending to zero, squarefree constant closure is
equivalent to the existence of a cofinal finite-stage value strictly below
the penalty. Fixed positive penalties have finite legal norm approximants.
The RH consumers are conditional research reductions: no provider of the
strict finite-stage budgets or signed line certificates is proved here.

Bagchi, https://arxiv.org/abs/math/0607733, Remark 8, supports the external
interpretation as an RH equivalence. The forward implication from RH to
squarefree closure remains a literature input, not a theorem of this file.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.QPrimorialRegularization
open ZetaTwoHilbert ZetaTwoProbability QPhysicalDifference
open QSquarefreePrimorialCofinality
open RiemannResearch.Analysis.PrimitiveRegularization

/-- The objective uses complete physical Q energy. -/
def objective (lam : ℝ) (u : QHilbert) : ℝ :=
  ‖differenceCLM u - differenceCLM qOne‖ ^ 2 + lam * ‖u‖ ^ 2

/-- Restriction of the physical difference to the finite primorial stage. -/
def stageDifference (n : ℕ) : primorialStage n →L[ℝ] QHilbert :=
  differenceCLM.comp (primorialStage n).subtypeL

/-- The unique positive-penalty stage normal solution, chosen unconditionally. -/
def minimizer (n : ℕ) (lam : ℝ) (hlam : 0 < lam) :
    primorialStage n :=
  Classical.choose (exists_normal (stageDifference n) (differenceCLM qOne) hlam)

theorem minimizer_normal (n : ℕ) (lam : ℝ) (hlam : 0 < lam) :
    IsNormal (stageDifference n).toLinearMap ⊤ (differenceCLM qOne) lam
      (minimizer n lam hlam) :=
  Classical.choose_spec (exists_normal (stageDifference n) (differenceCLM qOne) hlam)

/-- Algebraic cofinality covers each finite legal vector beyond any requested stage. -/
theorem exists_stage_mem (u : QHilbert) (hu : u ∈ qSquarefreeCRTSpan) (N : ℕ) :
    ∃ M, N ≤ M ∧ u ∈ primorialStage M := by
  rw [← iSup_primorial_eq_squarefreeSpan] at hu
  obtain ⟨m, hm⟩ := (Submodule.mem_iSup_of_directed primorialStage
    primorialStage_mono.directed_le).mp hu
  exact ⟨max m N, le_max_right _ _, primorialStage_mono (le_max_left _ _) hm⟩

theorem exists_strict_stage_budget
    (hOne : qOne ∈ qSquarefreeCRTSpan.topologicalClosure)
    (N : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    ∃ M, N ≤ M ∧ ∃ u ∈ primorialStage M, objective lam u < lam := by
  obtain ⟨u, hu, hbudget⟩ :=
    exists_strict_budget_of_unit_target differenceCLM qSquarefreeCRTSpan qOne qOne_norm_sq hOne hlam
  obtain ⟨M, hMN, huM⟩ := exists_stage_mem u hu N
  exact ⟨M, hMN, u, huM, hbudget⟩


theorem minimizer_normal_ambient (n : ℕ) (lam : ℝ) (hlam : 0 < lam) :
    IsNormal differenceCLM.toLinearMap (primorialStage n) (differenceCLM qOne) lam
      (minimizer n lam hlam : QHilbert) := by
  intro h hh
  have hn := minimizer_normal n lam hlam ⟨h, hh⟩ (by simp)
  change inner ℝ (differenceCLM (minimizer n lam hlam : QHilbert) -
    differenceCLM qOne) (differenceCLM h) +
      lam * inner ℝ (minimizer n lam hlam : QHilbert) h = 0 at hn
  exact hn

def value (n : ℕ) (lam : ℝ) (hlam : 0 < lam) : ℝ :=
  objective lam (minimizer n lam hlam : QHilbert)

/-- Complete stage objective decomposition. -/
theorem minimizer_completion (n : ℕ) (lam : ℝ) (hlam : 0 < lam)
    (u : QHilbert) (hu : u ∈ primorialStage n) :
    objective lam u = value n lam hlam +
      ‖differenceCLM (u - (minimizer n lam hlam : QHilbert))‖ ^ 2 +
        lam * ‖u - (minimizer n lam hlam : QHilbert)‖ ^ 2 := by
  exact objective_completion differenceCLM.toLinearMap (primorialStage n)
    (differenceCLM qOne) lam (minimizer n lam hlam : QHilbert) u
      (minimizer n lam hlam).property hu (minimizer_normal_ambient n lam hlam)

theorem minimizer_le_trial (n : ℕ) (lam : ℝ) (hlam : 0 < lam)
    (u : QHilbert) (hu : u ∈ primorialStage n) :
    value n lam hlam ≤ objective lam u := by
  have h := minimizer_completion n lam hlam u hu
  have hp := mul_nonneg hlam.le (sq_nonneg ‖u - (minimizer n lam hlam : QHilbert)‖)
  nlinarith [sq_nonneg ‖differenceCLM (u - (minimizer n lam hlam : QHilbert))‖]

/-- Enlarging a stage saves exactly the complete regularized displacement energy. -/
theorem nested_value_identity (n m : ℕ) (hnm : n ≤ m)
    (lam : ℝ) (hlam : 0 < lam) :
    value n lam hlam = value m lam hlam +
      ‖differenceCLM ((minimizer n lam hlam : QHilbert) -
        (minimizer m lam hlam : QHilbert))‖ ^ 2 +
      lam * ‖(minimizer n lam hlam : QHilbert) -
        (minimizer m lam hlam : QHilbert)‖ ^ 2 := by
  exact minimizer_completion m lam hlam (minimizer n lam hlam : QHilbert)
    (primorialStage_mono hnm (minimizer n lam hlam).property)

theorem exists_strict_value
    (hOne : qOne ∈ qSquarefreeCRTSpan.topologicalClosure)
    (N : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    ∃ M, N ≤ M ∧ value M lam hlam < lam := by
  obtain ⟨M, hMN, u, huM, hbudget⟩ := exists_strict_stage_budget hOne N hlam
  exact ⟨M, hMN, (minimizer_le_trial M lam hlam u huM).trans_lt hbudget⟩

/-- The strict constant-one finite-stage criterion; no budget provider is assumed silently. -/
theorem squarefree_constant_mem_iff_strict_primorial_budget
    (penalty : ℕ → ℝ) (hpos : ∀ N, 0 < penalty N)
    (hzero : Tendsto penalty atTop (𝓝 0)) :
    qOne ∈ qSquarefreeCRTSpan.topologicalClosure ↔
      ∀ N, ∃ M, N ≤ M ∧ value M (penalty N) (hpos N) < penalty N := by
  constructor
  · intro hOne N
    exact exists_strict_value hOne N (hpos N)
  · intro hbudget
    choose M hMN hB using hbudget
    apply QPrimitiveEnergyClosure.mem_closure_of_regularized_budget qSquarefreeCRTSpan
      (fun N => (minimizer (M N) (penalty N) (hpos N) : QHilbert)) qOne
      (fun N => primorialStage_le_squarefreeSpan (M N)
        (minimizer (M N) (penalty N) (hpos N)).property) penalty hpos hzero (C := 1)
    intro N
    simpa only [value, objective, one_mul] using (hB N).le


theorem value_antitone (lam : ℝ) (hlam : 0 < lam) :
    Antitone (fun n => value n lam hlam) := by
  intro n m hnm
  exact minimizer_le_trial m lam hlam (minimizer n lam hlam : QHilbert)
    (primorialStage_mono hnm (minimizer n lam hlam).property)

/-- Fixed positive penalties yield actual finite legal norm approximation. -/
theorem minimizer_tendsto (lam : ℝ) (hlam : 0 < lam)
    (u : QPrimitiveEnergyClosure.SquarefreeSpace)
    (hnormal : IsNormal QPrimitiveEnergyClosure.squarefreeDifference.toLinearMap ⊤
      (differenceCLM qOne) lam u) :
    Tendsto (fun n => (minimizer n lam hlam : QHilbert)) atTop (𝓝 (u : QHilbert)) := by
  have hn : IsNormal differenceCLM.toLinearMap
      qSquarefreeCRTSpan.topologicalClosure (differenceCLM qOne) lam (u : QHilbert) := by
    intro h hh
    have hh' := hnormal ⟨h, hh⟩ (by simp)
    change inner ℝ (differenceCLM (u : QHilbert) - differenceCLM qOne)
      (differenceCLM h) + lam * inner ℝ (u : QHilbert) h = 0 at hh'
    exact hh'
  have hcomplete (n : ℕ) :
      value n lam hlam = objective lam (u : QHilbert) +
        ‖differenceCLM ((minimizer n lam hlam : QHilbert) - (u : QHilbert))‖ ^ 2 +
        lam * ‖(minimizer n lam hlam : QHilbert) - (u : QHilbert)‖ ^ 2 :=
    objective_completion differenceCLM.toLinearMap qSquarefreeCRTSpan.topologicalClosure
      (differenceCLM qOne) lam (u : QHilbert) (minimizer n lam hlam : QHilbert)
      u.property (qSquarefreeCRTSpan.le_topologicalClosure
        (primorialStage_le_squarefreeSpan n (minimizer n lam hlam).property)) hn
  apply Metric.tendsto_atTop.mpr
  intro eps heps
  obtain ⟨w, hw, hobj⟩ :=
    exists_objective_lt_of_mem_closure differenceCLM qSquarefreeCRTSpan
      (differenceCLM qOne) lam (u : QHilbert) u.property
      (show objective lam (u : QHilbert) <
        objective lam (u : QHilbert) + lam * eps ^ 2 by
        have hp := mul_pos hlam (sq_pos_of_pos heps)
        linarith)
  obtain ⟨N, _, hwN⟩ := exists_stage_mem w hw 0
  refine ⟨N, ?_⟩
  intro n hNn
  have htrial := minimizer_le_trial n lam hlam w (primorialStage_mono hNn hwN)
  have hsq :
      ‖(minimizer n lam hlam : QHilbert) - (u : QHilbert)‖ ^ 2 < eps ^ 2 := by
    have hc := hcomplete n
    have hnonneg := sq_nonneg
      ‖differenceCLM ((minimizer n lam hlam : QHilbert) - (u : QHilbert))‖
    change objective lam w < objective lam (u : QHilbert) + lam * eps ^ 2 at hobj
    have hp : lam * ‖(minimizer n lam hlam : QHilbert) - (u : QHilbert)‖ ^ 2 <
        lam * eps ^ 2 := by linarith
    by_contra hnot
    have hm := mul_le_mul_of_nonneg_left (le_of_not_gt hnot) hlam.le
    linarith only [hp, hm]
  rw [dist_eq_norm]
  nlinarith [norm_nonneg ((minimizer n lam hlam : QHilbert) - (u : QHilbert))]

theorem strict_value_of_ray_certificate (M : ℕ) (lam : ℝ) (hlam : 0 < lam)
    (v : QHilbert) (hv : v ∈ primorialStage M)
    (hq : 0 < ‖differenceCLM v‖ ^ 2 + lam * ‖v‖ ^ 2)
    (hcert : (‖differenceCLM qOne‖ ^ 2 - lam) *
      (‖differenceCLM v‖ ^ 2 + lam * ‖v‖ ^ 2) <
      (inner ℝ (differenceCLM qOne) (differenceCLM v)) ^ 2) :
    value M lam hlam < lam := by
  obtain ⟨w, hw, hb⟩ := exists_strict_budget_of_ray_certificate differenceCLM.toLinearMap
    (primorialStage M) (differenceCLM qOne) lam v hv hq hcert
  exact (minimizer_le_trial M lam hlam w hw).trans_lt hb

/-- Conditional RH consumer: the strict finite-stage budget is still Open. -/
theorem riemannHypothesis_of_strict_primorial_budget
    (penalty : ℕ → ℝ) (hpos : ∀ N, 0 < penalty N)
    (hzero : Tendsto penalty atTop (𝓝 0))
    (hbudget : ∀ N, ∃ M, N ≤ M ∧ value M (penalty N) (hpos N) < penalty N) :
    RiemannHypothesis := by
  have hclosure := (squarefree_constant_mem_iff_strict_primorial_budget
    penalty hpos hzero).mpr hbudget
  have hs : qSquarefreeCRTSpan ≤ QFullResidueProjection.legalSpan := by
    apply Submodule.span_le.mpr
    rintro _ ⟨d, rfl⟩
    apply Submodule.subset_span
    refine ⟨d.val - 2, ?_⟩
    change qResidue (d.val - 2 + 2) = qResidue d.val
    congr 1
    have hd := d.property.1
    omega
  apply QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure
  exact closure_mono (show (qSquarefreeCRTSpan : Set QHilbert) ⊆
    (QFullResidueProjection.legalSpan : Set QHilbert) from hs) hclosure

/-- Inverse-free complete-energy provider; its signed inequalities remain Open. -/
theorem riemannHypothesis_of_primorial_ray_certificates
    (penalty : ℕ → ℝ) (hpos : ∀ N, 0 < penalty N)
    (hzero : Tendsto penalty atTop (𝓝 0))
    (M : ℕ → ℕ) (v : ℕ → QHilbert)
    (hmem : ∀ N, v N ∈ primorialStage (M N))
    (hq : ∀ N, 0 < ‖differenceCLM (v N)‖ ^ 2 + penalty N * ‖v N‖ ^ 2)
    (hcert : ∀ N, (‖differenceCLM qOne‖ ^ 2 - penalty N) *
      (‖differenceCLM (v N)‖ ^ 2 + penalty N * ‖v N‖ ^ 2) <
      (inner ℝ (differenceCLM qOne) (differenceCLM (v N))) ^ 2) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_strict_primorial_budget penalty hpos hzero
  intro N
  refine ⟨max (M N) N, le_max_right _ _, ?_⟩
  exact strict_value_of_ray_certificate _ _ (hpos N) (v N)
    (primorialStage_mono (le_max_left _ _) (hmem N)) (hq N) (hcert N)


end RiemannResearch.RH.QPrimorialRegularization
