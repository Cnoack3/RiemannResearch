/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoParetoTransfer
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Tactic.Positivity

/-!
# Sequence-preserving equivalence of the Pareto and Q realizations

Source: user-requested transfer of the Pareto research to Q, 15 October 2026.
The weight comparison is the existing checked comparison in
`ZetaTwoParetoTransfer`. This module completes its inverse and gives a
single transfer API for arbitrary subspaces and arbitrary conductor families.

The equivalence preserves physical sequences, constants, and legal atoms.
It is not an isometry: numerical Gram matrices and orthogonal projections
must be computed in their respective metrics.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.QParetoEquivalence
open Pareto ZetaTwoProbability ZetaTwoHilbert ZetaTwoParetoTransfer

theorem paretoSequence_q_square_summable (f : ThresholdHilbert) :
    Summable (fun k => positiveQWeight k * (hilbertSequence f k) ^ 2) := by
  have hs := (hilbertSequence_square_summable f).mul_left (2 / zetaTwo)
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (positiveQWeight_nonneg k) (sq_nonneg _)) _ hs
  intro k
  have hw : positiveQWeight k ≤ (2 / zetaTwo) * positiveWeight k := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ zetaTwo_pos).mpr
    simpa only [mul_comm] using
      zetaTwo_mul_QWeight_le_two_mul_paretoWeight k
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_right hw (sq_nonneg (hilbertSequence f k))

/-- Encode exactly the same physical sequence with Q weights. -/
def toQ (f : ThresholdHilbert) : QHilbert :=
  encodeQ (hilbertSequence f) (paretoSequence_q_square_summable f)

@[simp] theorem toQ_sequence (f : ThresholdHilbert) :
    qSequence (toQ f) = hilbertSequence f :=
  qSequence_encodeQ _ _ (hilbertSequence_zero f)

def toQLinear : ThresholdHilbert →ₗ[ℝ] QHilbert where
  toFun := toQ
  map_add' f g := by
    apply qSequence_injective
    change qSequence (toQ (f + g)) = qSequenceLinear (toQ f + toQ g)
    rw [map_add]
    change qSequence (toQ (f + g)) = qSequence (toQ f) + qSequence (toQ g)
    simp only [toQ_sequence]
    exact hilbertSequenceLinear.map_add f g
  map_smul' c f := by
    apply qSequence_injective
    change qSequence (toQ (c • f)) = qSequenceLinear (c • toQ f)
    rw [map_smul]
    change qSequence (toQ (c • f)) = c • qSequence (toQ f)
    simp only [toQ_sequence]
    exact hilbertSequenceLinear.map_smul c f

@[simp] theorem toPareto_toQ (f : ThresholdHilbert) : toPareto (toQ f) = f := by
  apply hilbertSequence_injective
  rw [toPareto_sequence, toQ_sequence]

@[simp] theorem toQ_toPareto (f : QHilbert) : toQ (toPareto f) = f := by
  apply qSequence_injective
  rw [toQ_sequence, toPareto_sequence]

theorem toQ_norm_sq_le (f : ThresholdHilbert) :
    ‖toQ f‖ ^ 2 ≤ (2 / zetaTwo) * ‖f‖ ^ 2 := by
  have h := zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq (toQ f)
  rw [toPareto_toQ] at h
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ zetaTwo_pos).mpr
  simpa only [mul_comm] using h

theorem toQ_norm_le (f : ThresholdHilbert) :
    ‖toQ f‖ ≤ Real.sqrt (2 / zetaTwo) * ‖f‖ := by
  have hp : 0 ≤ 2 / zetaTwo := by positivity [zetaTwo_pos]
  have hs : ‖toQ f‖ ^ 2 ≤ (Real.sqrt (2 / zetaTwo) * ‖f‖) ^ 2 := by
    simpa only [mul_pow, Real.sq_sqrt hp] using toQ_norm_sq_le f
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hs

def toQCLM : ThresholdHilbert →L[ℝ] QHilbert :=
  toQLinear.mkContinuous (Real.sqrt (2 / zetaTwo)) toQ_norm_le

/-- A bounded invertible change of probability weights preserving the raw sequence. -/
def paretoEquiv : QHilbert ≃L[ℝ] ThresholdHilbert where
  toLinearEquiv :=
    { toParetoLinear with
      invFun := toQ
      left_inv := toQ_toPareto
      right_inv := toPareto_toQ }
  continuous_toFun := toParetoCLM.continuous
  continuous_invFun := toQCLM.continuous

@[simp] theorem paretoEquiv_apply (f : QHilbert) : paretoEquiv f = toPareto f := rfl
@[simp] theorem paretoEquiv_symm_apply (f : ThresholdHilbert) :
    paretoEquiv.symm f = toQ f := rfl

@[simp] theorem toQ_hilbertOne : toQ hilbertOne = qOne := by
  rw [← toPareto_qOne, toQ_toPareto]

theorem toQ_residueVector (d : ℕ) (hd : 0 < d) :
    toQ (Pareto.BaezDuarte.residueVector d) = qResidue d := by
  rw [← toPareto_qResidue d hd, toQ_toPareto]

/-- Strong convergence of arbitrary families is equivalent in the two measures. -/
theorem tendsto_toPareto_iff {α : Type*} {l : Filter α}
    (f : α → QHilbert) (x : QHilbert) :
    Tendsto (fun a => toPareto (f a)) l (𝓝 (toPareto x)) ↔
      Tendsto f l (𝓝 x) := by
  constructor
  · intro h
    have ht := toQCLM.continuous.continuousAt.tendsto.comp h
    change Tendsto (fun a => toQ (toPareto (f a))) l (𝓝 (toQ (toPareto x))) at ht
    simpa only [toQ_toPareto] using ht
  · exact fun h => toParetoCLM.continuous.continuousAt.tendsto.comp h

/-- The same legal family is uniformly bounded under P exactly when under Q. -/
theorem uniformly_bounded_iff {α : Type*} (f : α → QHilbert) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ a, ‖f a‖ ≤ C) ↔
      (∃ C : ℝ, 0 ≤ C ∧ ∀ a, ‖toPareto (f a)‖ ≤ C) := by
  constructor
  · rintro ⟨C, hC, hb⟩
    refine ⟨Real.sqrt zetaTwo * C, by positivity, fun a => ?_⟩
    exact (toPareto_norm_le (f a)).trans
      (mul_le_mul_of_nonneg_left (hb a) (Real.sqrt_nonneg _))
  · rintro ⟨C, hC, hb⟩
    refine ⟨Real.sqrt (2 / zetaTwo) * C, by positivity, fun a => ?_⟩
    have hh := toQ_norm_le (toPareto (f a))
    rw [toQ_toPareto] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left (hb a) (Real.sqrt_nonneg _))

/-- Norm-closed subspace membership transfers for every subspace, including
squarefree, restricted-conductor, CRT, and affine-difference spans. -/
theorem mem_closure_map_iff (S : Submodule ℝ QHilbert) (f : QHilbert) :
    toPareto f ∈ (S.map paretoEquiv.toLinearMap).topologicalClosure ↔
      f ∈ S.topologicalClosure := by
  change paretoEquiv f ∈ _root_.closure
    (paretoEquiv '' (S : Set QHilbert)) ↔ f ∈ _root_.closure (S : Set QHilbert)
  have hc := paretoEquiv.toHomeomorph.image_closure (S : Set QHilbert)
  change paretoEquiv '' _root_.closure (S : Set QHilbert) =
    _root_.closure (paretoEquiv '' (S : Set QHilbert)) at hc
  rw [← hc]
  constructor
  · rintro ⟨x, hx, hxf⟩
    exact paretoEquiv.injective hxf ▸ hx
  · intro h
    exact ⟨f, h, rfl⟩

theorem map_span_range {ι : Type*} (v : ι → QHilbert) :
    (Submodule.span ℝ (Set.range v)).map paretoEquiv.toLinearMap =
      Submodule.span ℝ (Set.range (fun i => toPareto (v i))) := by
  rw [Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨v i, ⟨i, rfl⟩, rfl⟩

/-- Closure transfer for an arbitrary indexed collection of Q vectors. -/
theorem mem_closure_span_iff {ι : Type*} (v : ι → QHilbert) (f : QHilbert) :
    f ∈ (Submodule.span ℝ (Set.range v)).topologicalClosure ↔
      toPareto f ∈ (Submodule.span ℝ
        (Set.range (fun i => toPareto (v i)))).topologicalClosure := by
  rw [← map_span_range]
  exact (mem_closure_map_iff _ _).symm

/-- All restricted legal closure problems transfer with unchanged conductors. -/
theorem legal_closure_iff {ι : Type*} (d : ι → ℕ) (hd : ∀ i, 0 < d i) :
    qOne ∈ (Submodule.span ℝ (Set.range (fun i => qResidue (d i)))).topologicalClosure ↔
      hilbertOne ∈ (Submodule.span ℝ
        (Set.range (fun i => Pareto.BaezDuarte.residueVector (d i)))).topologicalClosure := by
  simpa only [toPareto_qOne, toPareto_qResidue _ (hd _)] using
    mem_closure_span_iff (fun i => qResidue (d i)) qOne

end RiemannResearch.RH.QParetoEquivalence
