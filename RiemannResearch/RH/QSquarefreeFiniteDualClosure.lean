/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoCoordinateDual
import RiemannResearch.RH.QSquarefreeCompatibleHeads
import RiemannResearch.RH.QSquarefreeExactHeadResidualBarrier
import RiemannResearch.RH.QFiniteSupportDualCriterion
import RiemannResearch.RH.SquarefreeRadicalDifference
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Compatible heads and the finite-support annihilator barrier

Source: the user's CRT/Ramanujan/Pareto research agenda, continued 29 October
2026. Finite interpolation supplies all finite dual consequences, but does
not supply Hilbert density. The exact residual distance below separates these
two issues without asserting that the residual is nonzero.
-/

noncomputable section
open scoped Topology
namespace RiemannResearch.RH.QSquarefreeFiniteDualClosure
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoOptimizerStage
open QFiniteSupportDualCriterion QSquarefreeCompatibleHeads
open QSquarefreeExactHeadResidualBarrier SquarefreeRadicalDifference
open UniqueFactorizationMonoid

/-- The ambient Hilbert subspace determined by all radical-jump constraints. -/
def radicalCompatible : Submodule ℝ QHilbert where
  carrier := {x | ∀ m, 2 ≤ m → qDifference x m = qDifference x (radical m)}
  zero_mem' := by intro m hm; rw [qDifference_zero, qDifference_zero]
  add_mem' := by
    intro x y hx hy m hm
    rw [qDifference_add, qDifference_add, hx m hm, hy m hm]
  smul_mem' := by
    intro c x hx m hm
    rw [qDifference_smul, qDifference_smul, hx m hm]

theorem legal_le_radicalCompatible : qSquarefreeCRTSpan ≤ radicalCompatible := by
  apply Submodule.span_le.mpr
  rintro x ⟨d, rfl⟩ m hm
  simpa only [qDifference, qSequence_qResidue] using
    residueFraction_difference_radical d.val m d.property.1 d.property.2 hm

theorem radicalCompatible_closed : IsClosed (radicalCompatible : Set QHilbert) := by
  have hc : IsClosed (⋂ (m : ℕ) (_ : 2 ≤ m),
      {x : QHilbert | qDifference x m = qDifference x (radical m)}) :=
    isClosed_iInter fun m => isClosed_iInter fun _ =>
      isClosed_eq (continuous_qDifference m) (continuous_qDifference (radical m))
  convert hc using 1 <;> ext x <;> simp [radicalCompatible]

theorem legalClosure_le_radicalCompatible :
    qSquarefreeCRTSpan.topologicalClosure ≤ radicalCompatible :=
  closure_minimal legal_le_radicalCompatible radicalCompatible_closed

/-- Necessity and sufficiency for every finite anchored physical head. -/
theorem exact_head_iff_radicalCompatible (v : ℕ → ℝ) (H : ℕ) (hv0 : v 0 = 0) :
    (∃ F : QHilbert, F ∈ qSquarefreeCRTSpan ∧
      ∀ n, n ≤ H → qSequence F n = v n) ↔
    (∀ n, 2 ≤ n → n ≤ H →
      v n - v (n - 1) = v (radical n) - v (radical n - 1)) := by
  constructor
  · rintro ⟨F, hF, hh⟩ n hn hnH
    have hr : radical n ≤ n := Nat.radical_le_self_iff.mpr (by omega)
    have he := legal_le_radicalCompatible hF n hn
    simpa only [qDifference, hh n hnH, hh (n - 1) (by omega),
      hh (radical n) (by omega), hh (radical n - 1) (by omega)] using he
  · exact exists_legal_exact_head v H hv0

/-- Every finite-support squarefree annihilator also annihilates every
radical-compatible Hilbert vector. -/
theorem inner_finite_annihilator_compatible (M : ℕ) (a x : QHilbert)
    (ha : finiteHead M a ∈ ZetaTwoOptimizerStage.closureᗮ)
    (hx : x ∈ radicalCompatible) : inner ℝ x (finiteHead M a) = 0 := by
  obtain ⟨F, hF, hh⟩ := exists_legal_exact_head (qSequence x) M
    (qSequence_zero x) (fun n hn hnM => hx n hn)
  have he := inner_finiteHead_eq_of_matching_head M F x a
    (fun k hk hkM => hh k hkM)
  rw [← he]
  exact Submodule.inner_right_of_mem_orthogonal
    (legal_mem_optimizer_closure F hF) ha

theorem qOne_mem_radicalCompatible : qOne ∈ radicalCompatible := by
  intro m hm
  rw [qDifference_qOne m hm,
    qDifference_qOne (radical m) (Nat.two_le_radical_iff.mpr hm)]

theorem inner_qOne_finite_annihilator (M : ℕ) (a : QHilbert)
    (ha : finiteHead M a ∈ ZetaTwoOptimizerStage.closureᗮ) :
    inner ℝ qOne (finiteHead M a) = 0 :=
  inner_finite_annihilator_compatible M a qOne ha qOne_mem_radicalCompatible

theorem inner_residual_finite_annihilator (M : ℕ) (a : QHilbert)
    (ha : finiteHead M a ∈ ZetaTwoOptimizerStage.closureᗮ) :
    inner ℝ limitingResidual (finiteHead M a) = 0 := by
  have hz := Submodule.inner_right_of_mem_orthogonal
    (ZetaTwoOptimizerStage.closure.starProjection_apply_mem qOne) ha
  rw [limitingResidual, inner_sub_left,
    inner_qOne_finite_annihilator M a ha, hz, sub_zero]

def finiteAnnihilators : Set QHilbert :=
  {a | a ∈ finiteTests ∧ a ∈ ZetaTwoOptimizerStage.closureᗮ}

theorem inner_residual_finiteAnnihilator (a : QHilbert)
    (ha : a ∈ finiteAnnihilators) : inner ℝ limitingResidual a = 0 := by
  obtain ⟨⟨M, b, rfl⟩, ha⟩ := ha
  exact inner_residual_finite_annihilator M b ha

/-- The entire norm closure of finite-support annihilators remains
orthogonal to the actual squarefree target residual. -/
theorem inner_residual_finiteAnnihilatorClosure (a : QHilbert)
    (ha : a ∈ _root_.closure finiteAnnihilators) :
    inner ℝ limitingResidual a = 0 := by
  have hc : IsClosed {a : QHilbert | inner ℝ limitingResidual a = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  exact closure_minimal (fun a ha => inner_residual_finiteAnnihilator a ha) hc ha

/-- Adding any vector from that closure can only increase squared distance. -/
theorem residual_finiteAnnihilatorClosure_distance (a : QHilbert)
    (ha : a ∈ _root_.closure finiteAnnihilators) :
    ‖limitingResidual - a‖ ^ 2 = ‖limitingResidual‖ ^ 2 + ‖a‖ ^ 2 := by
  rw [norm_sub_sq_real, inner_residual_finiteAnnihilatorClosure a ha]
  ring

/-- Approximating the actual residual by finite-support annihilators is
equivalent to its vanishing, not an automatic truncation principle. -/
theorem residual_mem_finiteAnnihilatorClosure_iff :
    limitingResidual ∈ _root_.closure finiteAnnihilators ↔ limitingResidual = 0 := by
  constructor
  · intro hr
    have h := inner_residual_finiteAnnihilatorClosure limitingResidual hr
    rw [real_inner_self_eq_norm_sq] at h
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg limitingResidual])
  · intro hr
    rw [hr]
    apply subset_closure
    refine ⟨⟨0, 0, ?_⟩, Submodule.zero_mem _⟩
    simp [finiteHead]

-- Add import RiemannResearch.RH.ZetaTwoCoordinateDual to the main module.
-- Insert these declarations in namespace QSquarefreeFiniteDualClosure.

theorem finiteHead_eq_of_physical_support (M : ℕ) (a : QHilbert)
    (ha : ∀ k, M < k → qSequence a k = 0) : finiteHead M a = a := by
  apply lp.ext
  funext n
  by_cases hn : n < M
  · exact finiteHead_apply_of_lt M a n hn
  · rw [finiteHead_apply_eq_zero M a n (by omega)]
    have hz := ha (n + 1) (by omega)
    rw [qSequence_succ] at hz
    have hs : Real.sqrt (qWeight n) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr (qWeight_pos n))
    exact ((div_eq_zero_iff).mp hz).resolve_right hs |>.symm

/-- The four-site Riesz representer of one radical-jump constraint. -/
def radicalWitness (m : ℕ) : QHilbert :=
  qSiteRiesz m - qSiteRiesz (m - 1) - qSiteRiesz (radical m) +
    qSiteRiesz (radical m - 1)

theorem radicalWitness_inner (m : ℕ) (hm : 2 ≤ m) (x : QHilbert) :
    inner ℝ (radicalWitness m) x = qDifference x m - qDifference x (radical m) := by
  have hr : 2 ≤ radical m := Nat.two_le_radical_iff.mpr hm
  rw [radicalWitness, inner_add_left, inner_sub_left, inner_sub_left,
    qSiteRiesz_inner m (by omega), qSiteRiesz_inner (m - 1) (by omega),
    qSiteRiesz_inner (radical m) (by omega),
    qSiteRiesz_inner (radical m - 1) (by omega)]
  simp only [qDifference]
  ring

theorem radicalWitness_finiteHead (m : ℕ) (hm : 2 ≤ m) :
    finiteHead m (radicalWitness m) = radicalWitness m := by
  apply finiteHead_eq_of_physical_support
  intro k hk
  have hr : 2 ≤ radical m := Nat.two_le_radical_iff.mpr hm
  have hrm : radical m ≤ m := Nat.radical_le_self_iff.mpr (by omega)
  change qSequenceLinear (qSiteRiesz m - qSiteRiesz (m - 1) -
    qSiteRiesz (radical m) + qSiteRiesz (radical m - 1)) k = 0
  simp only [map_add, map_sub, Pi.add_apply, Pi.sub_apply]
  change qSequence (qSiteRiesz m) k - qSequence (qSiteRiesz (m - 1)) k -
    qSequence (qSiteRiesz (radical m)) k +
    qSequence (qSiteRiesz (radical m - 1)) k = 0
  rw [qSequence_qSiteRiesz m (by omega),
    qSequence_qSiteRiesz (m - 1) (by omega),
    qSequence_qSiteRiesz (radical m) (by omega),
    qSequence_qSiteRiesz (radical m - 1) (by omega)]
  simp only [if_neg (show k ≠ m by omega), if_neg (show k ≠ m - 1 by omega),
    if_neg (show k ≠ radical m by omega),
    if_neg (show k ≠ radical m - 1 by omega), sub_zero, add_zero]

theorem radicalWitness_mem_finiteAnnihilators (m : ℕ) (hm : 2 ≤ m) :
    radicalWitness m ∈ finiteAnnihilators := by
  refine ⟨⟨m, radicalWitness m, radicalWitness_finiteHead m hm⟩, ?_⟩
  intro f hf
  rw [real_inner_comm, radicalWitness_inner m hm f]
  have hf' : f ∈ qSquarefreeCRTSpan.topologicalClosure := by
    rw [← QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure]
    exact hf
  exact sub_eq_zero.mpr (legalClosure_le_radicalCompatible hf' m hm)

/-- Finite-support dual tests characterize precisely the radical-compatible
ambient space, not the norm closure of the legal atoms. -/
theorem radicalCompatible_iff_finiteAnnihilator_tests (x : QHilbert) :
    x ∈ radicalCompatible ↔
      ∀ a ∈ finiteAnnihilators, inner ℝ a x = 0 := by
  constructor
  · intro hx a ha
    obtain ⟨⟨M, b, rfl⟩, ha⟩ := ha
    rw [real_inner_comm]
    exact inner_finite_annihilator_compatible M b x ha hx
  · intro h m hm
    have he := h (radicalWitness m) (radicalWitness_mem_finiteAnnihilators m hm)
    rw [radicalWitness_inner m hm x] at he
    exact sub_eq_zero.mp he

def finiteAnnihilatorSpan : Submodule ℝ QHilbert :=
  Submodule.span ℝ finiteAnnihilators

theorem finiteAnnihilatorSpan_orthogonal :
    finiteAnnihilatorSpanᗮ = radicalCompatible := by
  ext x
  constructor
  · intro hx
    apply (radicalCompatible_iff_finiteAnnihilator_tests x).mpr
    intro a ha
    exact hx a (Submodule.subset_span ha)
  · intro hx a ha
    have hh := (radicalCompatible_iff_finiteAnnihilator_tests x).mp hx
    induction ha using Submodule.span_induction with
    | mem a ha => exact hh a ha
    | zero => simp
    | add a b ha hb iha ihb => rw [inner_add_left, iha, ihb, add_zero]
    | smul c a ha iha => rw [real_inner_smul_left, iha, mul_zero]

end RiemannResearch.RH.QSquarefreeFiniteDualClosure
