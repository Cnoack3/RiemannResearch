/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFiniteForcingData
import RiemannResearch.RH.QParetoMetric
import RiemannResearch.RH.QParetoEquivalence
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Finite joint-annihilator estimates in the physical Pareto realization

Source: user-provided Pareto First Projections and Transfer to Q Research Draft,
11 November 2026, Priority 1 and the finite joint-annihilator theorem:
https://chatgpt.com/space/page_899f440a0304819182638fe62685b02e.
The estimate is stronger than the prime-only statement: any positive included
conductor works. The two inner products refer to the same physical sequence.
The global P-mean and the unresolved Q-mean remain separate questions.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QParetoJointAnnihilator
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer
open QParetoEquivalence QShiftedReciprocal QSquarefreeFiniteDisplacement

/-- V intersected with the P and Q annihilators of the same physical W. -/
def jointAnnihilator (V : Submodule ℝ ThresholdHilbert) (W : Submodule ℝ QHilbert) :
    Submodule ℝ ThresholdHilbert :=
  V ⊓ ((W.map toParetoLinear)ᗮ ⊓ Wᗮ.comap toQLinear)

instance jointAnnihilator_isClosed (V : Submodule ℝ ThresholdHilbert)
    (W : Submodule ℝ QHilbert) [IsClosed (V : Set ThresholdHilbert)] :
    IsClosed (jointAnnihilator V W : Set ThresholdHilbert) := by
  exact (‹IsClosed (V : Set ThresholdHilbert)›).inter
    ((W.map toParetoLinear).isClosed_orthogonal.inter
      (W.isClosed_orthogonal.preimage toQCLM.continuous))

instance jointAnnihilator_hasOrthogonalProjection (V : Submodule ℝ ThresholdHilbert)
    (W : Submodule ℝ QHilbert) [IsClosed (V : Set ThresholdHilbert)] :
    (jointAnnihilator V W).HasOrthogonalProjection := by infer_instance

theorem jointAnnihilator_le (V : Submodule ℝ ThresholdHilbert)
    (W : Submodule ℝ QHilbert) : jointAnnihilator V W ≤ V := inf_le_left

/-- The small P-mean follows from two orthogonalities to a single conductor. -/
theorem mean_bound_of_two_orthogonalities (m : ℕ) (hm : 0 < m)
    (k : ThresholdHilbert)
    (hp : inner ℝ (toPareto (qResidue m)) k = 0)
    (hq : inner ℝ (qResidue m) (toQ k) = 0) :
    |inner ℝ hilbertOne k| ≤ Real.sqrt (1 / (m : ℝ)) * ‖k‖ := by
  have hi := pareto_inner_identity (qResidue m) (toQ k)
  rw [toPareto_toQ, hp, hq, zero_sub] at hi
  have hb : inner ℝ (qResidue m) (B (toQ k)) = 0 := by
    have hz := (mul_eq_zero.mp hi.symm).resolve_left zetaTwo_pos.ne'
    exact neg_eq_zero.mp hz
  have hr := ratioVector_pair_shifted m hm (toQ k)
  rw [hb, mul_zero, toPareto_toQ] at hr
  have he : inner ℝ hilbertOne k = inner ℝ (hilbertOne - ratioVector m) k := by
    rw [inner_sub_left, ← hr, sub_zero]
  have hn : ‖hilbertOne - ratioVector m‖ ≤ Real.sqrt (1 / (m : ℝ)) :=
    Real.le_sqrt_of_sq_le (ratioVector_error_norm_sq_le m hm)
  rw [he]
  exact (abs_real_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg k))

theorem joint_mean_bound (V : Submodule ℝ ThresholdHilbert)
    (W : Submodule ℝ QHilbert) (m : ℕ) (hm : 0 < m) (hW : qResidue m ∈ W)
    (k : ThresholdHilbert) (hk : k ∈ jointAnnihilator V W) :
    |inner ℝ hilbertOne k| ≤ Real.sqrt (1 / (m : ℝ)) * ‖k‖ := by
  apply mean_bound_of_two_orthogonalities m hm k
  · exact Submodule.inner_right_of_mem_orthogonal
      (show toPareto (qResidue m) ∈ W.map toParetoLinear from ⟨_, hW, rfl⟩) hk.2.1
  · exact Submodule.inner_right_of_mem_orthogonal hW hk.2.2

/-- The global conclusion needs cofinal tests, unlike the finite bound. -/
theorem joint_mean_zero_of_cofinal_conductors (V : Submodule ℝ ThresholdHilbert)
    (W : Submodule ℝ QHilbert) (m : ℕ → ℕ) (hpos : ∀ j, 0 < m j)
    (hcofinal : Tendsto m atTop atTop) (hW : ∀ j, qResidue (m j) ∈ W)
    (k : ThresholdHilbert) (hk : k ∈ jointAnnihilator V W) :
    inner ℝ hilbertOne k = 0 := by
  have hi : Tendsto (fun j => 1 / (m j : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp hcofinal)
  have hb : Tendsto (fun j => Real.sqrt (1 / (m j : ℝ)) * ‖k‖) atTop (𝓝 0) := by
    simpa using (Real.continuous_sqrt.continuousAt.tendsto.comp hi).mul_const ‖k‖
  have hz : Tendsto (fun _ : ℕ => |inner ℝ hilbertOne k|) atTop (𝓝 0) :=
    squeeze_zero (fun _ => abs_nonneg _) (fun j => joint_mean_bound V W
      (m j) (hpos j) (hW j) k hk) hb
  exact abs_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hz)

/-- All prime atoms supply the cofinal tests required for exact P-mean zero. -/
theorem joint_mean_zero_of_all_primes (V : Submodule ℝ ThresholdHilbert)
    (W : Submodule ℝ QHilbert) (hW : ∀ p : ℕ, p.Prime → qResidue p ∈ W)
    (k : ThresholdHilbert) (hk : k ∈ jointAnnihilator V W) :
    inner ℝ hilbertOne k = 0 := by
  choose m hm hp using (fun j : ℕ => Nat.exists_infinite_primes (j + 1))
  apply joint_mean_zero_of_cofinal_conductors V W m
    (fun j => (hp j).pos) ?_ (fun j => hW _ (hp j)) k hk
  apply tendsto_atTop_mono (fun j => (Nat.le_succ j).trans (hm j)) tendsto_id

/-- P-mean zero leaves an explicit reciprocal pairing for the Q mean. -/
theorem joint_qMean_identity (V : Submodule ℝ ThresholdHilbert)
    (W : Submodule ℝ QHilbert) (hW : ∀ p : ℕ, p.Prime → qResidue p ∈ W)
    (k : ThresholdHilbert) (hk : k ∈ jointAnnihilator V W) :
    zetaTwo * inner ℝ qOne (toQ k) = inner ℝ (reciprocalD hilbertOne) k := by
  have h := QParetoMetric.inner_identity qOne (toQ k)
  rw [toPareto_qOne, toPareto_toQ,
    joint_mean_zero_of_all_primes V W hW k hk, zero_add] at h
  simpa only [QParetoMetric.metricPairing, toPareto_qOne, toPareto_toQ,
    reciprocalD_symmetric] using h

theorem joint_qMean_zero_iff (V : Submodule ℝ ThresholdHilbert)
    (W : Submodule ℝ QHilbert) (hW : ∀ p : ℕ, p.Prime → qResidue p ∈ W)
    (k : ThresholdHilbert) (hk : k ∈ jointAnnihilator V W) :
    inner ℝ qOne (toQ k) = 0 ↔ inner ℝ (reciprocalD hilbertOne) k = 0 := by
  rw [← joint_qMean_identity V W hW k hk]
  simp only [mul_eq_zero, zetaTwo_pos.ne', false_or]

variable (V : Submodule ℝ ThresholdHilbert) (W : Submodule ℝ QHilbert)
variable [(jointAnnihilator V W).HasOrthogonalProjection]

/-- Quantitative finite-stage result; exact mean zero is not asserted here. -/
theorem joint_projection_norm_le (m : ℕ) (hm : 0 < m) (hW : qResidue m ∈ W) :
    ‖(jointAnnihilator V W).starProjection hilbertOne‖ ≤
      Real.sqrt (1 / (m : ℝ)) := by
  let K := jointAnnihilator V W
  let k := K.starProjection hilbertOne
  have hk : k ∈ K := K.starProjection_apply_mem _
  have hb := joint_mean_bound V W m hm hW k hk
  have ho := Submodule.inner_right_of_mem_orthogonal hk
    (Submodule.sub_starProjection_mem_orthogonal (K := K) hilbertOne)
  change inner ℝ k (hilbertOne - k) = 0 at ho
  rw [inner_sub_right, real_inner_self_eq_norm_sq, ← real_inner_comm k hilbertOne] at ho
  have he : inner ℝ hilbertOne k = ‖k‖ ^ 2 := sub_eq_zero.mp ho
  rw [he, abs_of_nonneg (sq_nonneg _)] at hb
  by_cases hz : ‖k‖ = 0
  · change ‖k‖ ≤ _
    rw [hz]
    exact Real.sqrt_nonneg _
  · have hpos : 0 < ‖k‖ := lt_of_le_of_ne (norm_nonneg k) (Ne.symm hz)
    change ‖k‖ ≤ _
    nlinarith

/-- Nesting gives the same bound for the Pareto fit onto V. -/
theorem joint_projection_fit_eq [V.HasOrthogonalProjection] :
    (jointAnnihilator V W).starProjection (V.starProjection hilbertOne) =
      (jointAnnihilator V W).starProjection hilbertOne := by
  exact congrArg (fun A : ThresholdHilbert →L[ℝ] ThresholdHilbert => A hilbertOne)
    (Submodule.starProjection_comp_starProjection_of_le (jointAnnihilator_le V W))

theorem joint_projection_fit_norm_le [V.HasOrthogonalProjection]
    (m : ℕ) (hm : 0 < m) (hW : qResidue m ∈ W) :
    ‖(jointAnnihilator V W).starProjection (V.starProjection hilbertOne)‖ ≤
      Real.sqrt (1 / (m : ℝ)) := by
  rw [joint_projection_fit_eq]
  exact joint_projection_norm_le V W m hm hW

/-- The finite dictionary statement with an explicit largest included prime. -/
theorem finite_prime_joint_projection_bound [IsClosed (V : Set ThresholdHilbert)]
    (s : Finset ℕ) (hs : s.Nonempty) (hp : ∀ p ∈ s, p.Prime) :
    ‖(jointAnnihilator V (Submodule.span ℝ (qResidue '' (s : Set ℕ)))).starProjection
      hilbertOne‖ ≤ Real.sqrt (1 / (s.max' hs : ℝ)) := by
  apply joint_projection_norm_le V _ _ (hp _ (s.max'_mem hs)).pos
  exact Submodule.subset_span ⟨s.max' hs, s.max'_mem hs, rfl⟩

/-- Membership means simultaneous orthogonality to the same physical prime-test space. -/
theorem mem_jointAnnihilator_iff (k : ThresholdHilbert) :
    k ∈ jointAnnihilator V W ↔
      k ∈ V ∧
      (∀ w ∈ W, inner ℝ (toPareto w) k = 0) ∧
      (∀ w ∈ W, inner ℝ w (toQ k) = 0) := by
  constructor
  · intro hk
    refine ⟨hk.1, ?_, ?_⟩
    · intro w hw
      exact Submodule.inner_right_of_mem_orthogonal
        (show toPareto w ∈ W.map toParetoLinear from ⟨w, hw, rfl⟩) hk.2.1
    · intro w hw
      exact Submodule.inner_right_of_mem_orthogonal hw hk.2.2
  · rintro ⟨hV, hP, hQ⟩
    refine ⟨hV, ?_, ?_⟩
    · apply (Submodule.mem_orthogonal _ _).mpr
      intro w hw
      obtain ⟨v, hv, rfl⟩ := hw
      exact hP v hv
    · change toQ k ∈ Wᗮ
      exact (Submodule.mem_orthogonal W (toQ k)).mpr hQ

/-- The whole K-space has Q-mean zero exactly when its reciprocal constant projection vanishes. -/
theorem joint_qMean_zero_iff_project_reciprocal_one_zero
    (hW : ∀ p : ℕ, p.Prime → qResidue p ∈ W) :
    (∀ k ∈ jointAnnihilator V W, inner ℝ qOne (toQ k) = 0) ↔
      (jointAnnihilator V W).starProjection (reciprocalD hilbertOne) = 0 := by
  rw [Submodule.starProjection_apply_eq_zero_iff]
  constructor
  · intro h
    apply (Submodule.mem_orthogonal _ _).mpr
    intro k hk
    rw [real_inner_comm]
    exact (joint_qMean_zero_iff V W hW k hk).mp (h k hk)
  · intro h k hk
    apply (joint_qMean_zero_iff V W hW k hk).mpr
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal hk h


end RiemannResearch.RH.QParetoJointAnnihilator
