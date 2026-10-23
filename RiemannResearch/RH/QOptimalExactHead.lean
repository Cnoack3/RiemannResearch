/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteHilbertConstraints
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import RiemannResearch.Analysis.DenseProjectionTesting
import RiemannResearch.RH.QFullHeadControllability
import RiemannResearch.RH.QFullHeadRepair
import RiemannResearch.RH.QExactHeadTailEnergy
import RiemannResearch.RH.QFiniteSupportDualEstimates
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Optimal exact heads in the actual closed full residue span

Source: user-provided RH_Uniform_Dual_Bound_Research_Agenda_Continued,
22 October 2026, finite-head controllability and optimal energies, Sections 3--6.
The actual projected coordinate rows are linearly independent by unconditional
finite-head controllability. Existing finite Hilbert constraint machinery then
constructs the unique full-closure minimizer and its exact inverse-Gram energy.
Uniform boundedness of the resulting energies remains an Open arithmetic
obligation; its RH consumer is a conditional research reduction.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.QOptimalExactHead
open ZetaTwoHilbert QFiniteSupportDualCriterion
open RiemannResearch.Analysis.DenseProjectionTesting
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteHilbertConstraints

def headRow (M : ℕ) (i : Fin M) : QHilbert :=
  QFullResidueProjection.closure.starProjection (lp.single 2 (i : ℕ) 1)

theorem headRow_mem (M : ℕ) (i : Fin M) :
    headRow M i ∈ QFullResidueProjection.closure :=
  QFullResidueProjection.closure.starProjection_apply_mem _

theorem headRow_inner (M : ℕ) (i : Fin M) (f : QHilbert)
    (hf : f ∈ QFullResidueProjection.closure) :
    inner ℝ (headRow M i) f = f i := by
  rw [real_inner_comm]
  change inner ℝ f (QFullResidueProjection.closure.starProjection
    (lp.single 2 (i : ℕ) 1)) = f i
  rw [← inner_eq_projected_test QFullResidueProjection.closure hf]
  simp only [lp.inner_single_right, RCLike.inner_apply, conj_trivial, one_mul]

/-- No inverse or positive-definiteness hypothesis is assumed. -/
theorem headRow_linearIndependent (M : ℕ) : LinearIndependent ℝ (headRow M) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  let F := QFullHeadRepair.headBasis M i
  have hFc : F ∈ QFullResidueProjection.closure :=
    QFullResidueProjection.legalSpan.le_topologicalClosure
      (QFullHeadRepair.headBasis_mem M i)
  have hz := congrArg (fun x : QHilbert => inner ℝ x F) hc
  simp only [sum_inner, real_inner_smul_left, inner_zero_left] at hz
  simp only [headRow_inner M _ F hFc, F, QFullHeadRepair.headBasis_coord] at hz
  simpa using hz

def targetHead (M : ℕ) (i : Fin M) : ℝ := qOne i

def optimizer (M : ℕ) : QHilbert :=
  minimumVector (headRow_linearIndependent M) (targetHead M)

def energy (M : ℕ) : ℝ := ‖optimizer M‖ ^ 2

theorem optimizer_mem (M : ℕ) : optimizer M ∈ QFullResidueProjection.closure := by
  classical
  unfold optimizer minimumVector
  rw [Fintype.linearCombination_apply]
  exact QFullResidueProjection.closure.sum_mem fun i _ =>
    QFullResidueProjection.closure.smul_mem _ (headRow_mem M i)

theorem optimizer_coord (M n : ℕ) (hn : n < M) : optimizer M n = qOne n := by
  have h := minimumVector_observation (headRow_linearIndependent M)
    (targetHead M) (⟨n, hn⟩ : Fin M)
  change inner ℝ (headRow M ⟨n, hn⟩) (optimizer M) = qOne n at h
  rwa [headRow_inner M _ _ (optimizer_mem M)] at h

theorem energy_inverseGram (M : ℕ) :
    energy M = ∑ i, (gramEquiv (headRow_linearIndependent M)).symm
      (targetHead M) i * targetHead M i :=
  minimumVector_norm_sq (headRow_linearIndependent M) (targetHead M)

/-- Every feasible vector has the exact nonnegative norm-square remainder. -/
theorem norm_sq_completion (M : ℕ) (f : QHilbert)
    (hf : f ∈ QFullResidueProjection.closure)
    (hh : ∀ n, n < M → f n = qOne n) :
    ‖f‖ ^ 2 = energy M + ‖f - optimizer M‖ ^ 2 := by
  apply feasible_norm_sq_completion (headRow_linearIndependent M) (targetHead M)
  intro i
  rw [headRow_inner M i f hf]
  exact hh i i.isLt

theorem energy_le (M : ℕ) (f : QHilbert)
    (hf : f ∈ QFullResidueProjection.closure)
    (hh : ∀ n, n < M → f n = qOne n) : energy M ≤ ‖f‖ ^ 2 := by
  rw [norm_sq_completion M f hf hh]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem unique_minimizer (M : ℕ) (f : QHilbert)
    (hf : f ∈ QFullResidueProjection.closure)
    (hh : ∀ n, n < M → f n = qOne n) :
    ‖f‖ ^ 2 = energy M ↔ f = optimizer M := by
  apply feasible_norm_sq_eq_iff (headRow_linearIndependent M) (targetHead M)
  intro i
  rw [headRow_inner M i f hf]
  exact hh i i.isLt

theorem energy_increment (M N : ℕ) (hMN : M ≤ N) :
    energy N = energy M + ‖optimizer N - optimizer M‖ ^ 2 :=
  norm_sq_completion M (optimizer N) (optimizer_mem N)
    (fun n hn => optimizer_coord N n (lt_of_lt_of_le hn hMN))

theorem energy_monotone : Monotone energy := by
  intro M N hMN
  rw [energy_increment M N hMN]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem energy_nonneg (M : ℕ) : 0 ≤ energy M := sq_nonneg _

theorem energy_le_exactHead (M : ℕ) :
    energy M ≤ ‖QMobiusExactHead.exactHead M‖ ^ 2 := by
  apply energy_le M _ (QFullResidueProjection.legalSpan.le_topologicalClosure
    (QMobiusExactHead.exactHead_mem_legalSpan M))
  intro n hn
  have he := QMobiusExactHead.exactHead_exact M (n + 1) (Nat.succ_pos _) (by omega)
  have ho : qSequence qOne (n + 1) = 1 := by
    rw [qSequence_qOne]
    simp [qOneSequence]
  have hne : Real.sqrt (qWeight n) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (qWeight_pos n))
  apply (div_left_inj' hne).mp
  simpa only [qSequence_succ] using he.trans ho.symm

theorem optimizer_pairing (M : ℕ) (a : QHilbert) :
    inner ℝ (optimizer M) (finiteHead M a) = inner ℝ qOne (finiteHead M a) := by
  rw [inner_finiteHead_eq_sum, inner_finiteHead_eq_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [optimizer_coord M n (Finset.mem_range.mp hn)]

theorem optimal_finiteHead_bound (M : ℕ) (a : QHilbert) :
    |inner ℝ qOne (finiteHead M a)| ≤ ‖optimizer M‖ *
      ‖QFullResidueProjection.closure.starProjection (finiteHead M a)‖ := by
  rw [← optimizer_pairing, inner_eq_projected_test
    QFullResidueProjection.closure (optimizer_mem M)]
  exact abs_real_inner_le_norm _ _

/-- Uniform boundedness is equivalent to the missing target membership. -/
theorem qOne_mem_iff_energy_bounded :
    qOne ∈ QFullResidueProjection.closure ↔ ∃ B : ℝ, ∀ M, energy M ≤ B := by
  constructor
  · intro h
    refine ⟨1, fun M => ?_⟩
    simpa only [qOne_norm, one_pow] using energy_le M qOne h (fun _ _ => rfl)
  · rintro ⟨B, hB⟩
    apply (mem_closure_iff_finite_test_bound qOne).mpr
    refine ⟨|B| + 1, fun M a => ?_⟩
    apply (optimal_finiteHead_bound M a).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have h := hB M
    change ‖optimizer M‖ ^ 2 ≤ B at h
    nlinarith [norm_nonneg (optimizer M), abs_nonneg B, le_abs_self B]

theorem qOne_mem_iff_energy_le_one :
    qOne ∈ QFullResidueProjection.closure ↔ ∀ M, energy M ≤ 1 := by
  constructor
  · intro h M
    simpa only [qOne_norm, one_pow] using energy_le M qOne h (fun _ _ => rfl)
  · intro h
    exact qOne_mem_iff_energy_bounded.mpr ⟨1, h⟩

theorem riemannHypothesis_of_energy_bounded
    (h : ∃ B : ℝ, ∀ M, energy M ≤ B) : RiemannHypothesis :=
  QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure
    (qOne_mem_iff_energy_bounded.mpr h)

/-- The alternative to bounded optimal energies is genuine divergence. -/
theorem energy_tendsto_atTop_of_not_mem
    (h : qOne ∉ QFullResidueProjection.closure) : Tendsto energy atTop atTop := by
  apply tendsto_atTop.2
  intro B
  have hex : ∃ M, B < energy M := by
    by_contra hn
    push Not at hn
    exact h (qOne_mem_iff_energy_bounded.mpr ⟨B, hn⟩)
  obtain ⟨M, hM⟩ := hex
  exact eventually_atTop.2 ⟨M, fun N hMN =>
    le_trans hM.le (energy_monotone hMN)⟩

theorem energy_isLeast (M : ℕ) :
    IsLeast {E : ℝ | ∃ f ∈ QFullResidueProjection.closure,
      (∀ n, n < M → f n = qOne n) ∧ ‖f‖ ^ 2 = E} (energy M) := by
  constructor
  · exact ⟨optimizer M, optimizer_mem M, optimizer_coord M, rfl⟩
  · rintro E ⟨f, hf, hh, rfl⟩
    exact energy_le M f hf hh

theorem optimizer_head (M : ℕ) :
    finiteHead M (optimizer M) = finiteHead M qOne := by
  unfold finiteHead
  apply Finset.sum_congr rfl
  intro n hn
  rw [optimizer_coord M n (Finset.mem_range.mp hn)]

theorem head_energy_le (M : ℕ) : ‖finiteHead M qOne‖ ^ 2 ≤ energy M := by
  have h := finiteHead_norm_le M (optimizer M)
  rw [optimizer_head] at h
  dsimp [energy]
  nlinarith [norm_nonneg (finiteHead M qOne), norm_nonneg (optimizer M)]

/-- Under membership, the optimal error is bounded by the target's own tail. -/
theorem optimizer_error_le_target_tail
    (h : qOne ∈ QFullResidueProjection.closure) (M : ℕ) :
    ‖optimizer M - qOne‖ ≤ ‖qOne - finiteHead M qOne‖ := by
  have hc := norm_sq_completion M qOne h (fun _ _ => rfl)
  have ht := finiteHead_norm_sq_split M qOne
  have he := head_energy_le M
  rw [norm_sub_rev (optimizer M) qOne]
  nlinarith [norm_nonneg (qOne - optimizer M),
    norm_nonneg (qOne - finiteHead M qOne)]

theorem optimizer_tendsto_qOne (h : qOne ∈ QFullResidueProjection.closure) :
    Tendsto optimizer atTop (𝓝 qOne) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun M => norm_nonneg (optimizer M - qOne))
    (optimizer_error_le_target_tail h)
  simpa only [sub_self, norm_zero] using
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => qOne) atTop (𝓝 qOne)).sub
      (finiteHead_tendsto qOne)).norm

theorem energy_tendsto_one (h : qOne ∈ QFullResidueProjection.closure) :
    Tendsto energy atTop (𝓝 1) := by
  change Tendsto (fun M => ‖optimizer M‖ ^ 2) atTop (𝓝 1)
  simpa only [qOne_norm, one_pow] using
    (optimizer_tendsto_qOne h).norm.pow 2

/-- The optimal energies inherit the unconditional sublinear envelope. -/
theorem energy_sublinear :
    Tendsto (fun M => energy M / (M : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero (fun M => div_nonneg (energy_nonneg M) (Nat.cast_nonneg M))
    (fun M => div_le_div_of_nonneg_right (energy_le_exactHead M) (Nat.cast_nonneg M))
  exact QSquarefreeSublinearHeads.exactHead_sublinear

/-- Complete dichotomy: strong convergence to one or unbounded energy escape. -/
theorem optimizer_dichotomy :
    (qOne ∈ QFullResidueProjection.closure ∧
      Tendsto optimizer atTop (𝓝 qOne) ∧ Tendsto energy atTop (𝓝 1)) ∨
    (qOne ∉ QFullResidueProjection.closure ∧ Tendsto energy atTop atTop) := by
  by_cases h : qOne ∈ QFullResidueProjection.closure
  · exact Or.inl ⟨h, optimizer_tendsto_qOne h, energy_tendsto_one h⟩
  · exact Or.inr ⟨h, energy_tendsto_atTop_of_not_mem h⟩

def headGram (M : ℕ) : Matrix (Fin M) (Fin M) ℝ := gramMatrix (headRow M)

theorem headGram_entry (M : ℕ) (i j : Fin M) :
    headGram M i j = headRow M j i :=
  headRow_inner M i (headRow M j) (headRow_mem M j)

theorem headGram_posDef (M : ℕ) : (headGram M).PosDef :=
  gramMatrix_posDef (headRow_linearIndependent M)

theorem headGram_det_pos (M : ℕ) : 0 < (headGram M).det :=
  (headGram_posDef M).det_pos

/-- Literal inverse of the actual compressed projection matrix. -/
theorem energy_inverseMatrix (M : ℕ) :
    energy M = dotProduct (targetHead M) ((headGram M)⁻¹.mulVec (targetHead M)) := by
  rw [energy_inverseGram, headGram, gramMatrix_inverseSource (headRow_linearIndependent M)]
  simp only [dotProduct, RiemannResearch.Analysis.FiniteGramCapacity.inverseSource]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem optimizer_inner_feasible (M : ℕ) (f : QHilbert)
    (hf : f ∈ QFullResidueProjection.closure)
    (hh : ∀ n, n < M → f n = qOne n) :
    inner ℝ (optimizer M) f = energy M := by
  apply minimumVector_inner_feasible (headRow_linearIndependent M) (targetHead M)
  intro i
  rw [headRow_inner M i f hf]
  exact hh i i.isLt

theorem optimizer_inner_later (M N : ℕ) (hMN : M ≤ N) :
    inner ℝ (optimizer M) (optimizer N) = energy M :=
  optimizer_inner_feasible M (optimizer N) (optimizer_mem N)
    (fun n hn => optimizer_coord N n (lt_of_lt_of_le hn hMN))

def innovation (M : ℕ) : QHilbert := optimizer (M + 1) - optimizer M

theorem innovation_norm_sq (M : ℕ) :
    ‖innovation M‖ ^ 2 = energy (M + 1) - energy M := by
  have h := energy_increment M (M + 1) (by omega)
  dsimp [innovation]
  linarith

/-- The complete optimal increments are pairwise orthogonal. -/
theorem innovation_orthogonal (M N : ℕ) (hMN : M < N) :
    inner ℝ (innovation M) (innovation N) = 0 := by
  simp only [innovation, inner_sub_left, inner_sub_right]
  rw [optimizer_inner_later (M + 1) (N + 1) (by omega),
    optimizer_inner_later (M + 1) N (by omega),
    optimizer_inner_later M (N + 1) (by omega),
    optimizer_inner_later M N (by omega)]
  ring

/-- The closed-space minimum is exactly the infimum over finite legal
interpolants with the constraints preserved, not merely approximated. -/
theorem energy_isGLB_finiteLegal (M : ℕ) :
    IsGLB {E : ℝ | ∃ f ∈ QFullResidueProjection.legalSpan,
      (∀ n, n < M → f n = qOne n) ∧ ‖f‖ ^ 2 = E} (energy M) := by
  constructor
  · rintro E ⟨f, hf, hh, rfl⟩
    exact energy_le M f (QFullResidueProjection.legalSpan.le_topologicalClosure hf) hh
  · intro B hB
    by_contra hn
    have hlt : energy M < B := lt_of_not_ge hn
    obtain ⟨f, hf, hh, hnorm⟩ := QFullHeadRepair.exists_exact_head_norm_sq_lt
      M (optimizer M) (optimizer_mem M) (B - energy M) (sub_pos.mpr hlt)
    have hb : B ≤ ‖f‖ ^ 2 := hB ⟨f, hf,
      (fun n hn => (hh n hn).trans (optimizer_coord M n hn)), rfl⟩
    change ‖f‖ ^ 2 < energy M + (B - energy M) at hnorm
    linarith

/-- Sharp coupling of optimal interpolation energy and the actual residual tail. -/
theorem actualResidual_energy_tail_bound (M : ℕ) :
    (inner ℝ qOne (finiteHead M QAnnihilatorTailEscape.actualResidual)) ^ 2 ≤
      (energy M - ‖finiteHead M qOne‖ ^ 2) *
        ‖QAnnihilatorTailEscape.tail M QAnnihilatorTailEscape.actualResidual‖ ^ 2 :=
  QExactHeadTailEnergy.actualResidual_head_energy_bound M (optimizer M)
    (optimizer_mem M) (optimizer_head M)

/-- Coefficients of the finite supported equality witness in the signed dual bound. -/
def dualCoefficients (M : ℕ) : Fin M → ℝ :=
  (gramEquiv (headRow_linearIndependent M)).symm (targetHead M)

/-- The finite-support dual maximizer uses the actual inverse-Gram source. -/
def dualWitness (M : ℕ) : QHilbert :=
  ∑ i : Fin M, dualCoefficients M i • (lp.single 2 (i : ℕ) 1 : QHilbert)

private theorem coordinate_atom_inner (n : ℕ) (a : QHilbert) :
    inner ℝ (lp.single 2 n 1) a = a n := by
  simp only [lp.inner_single_left, RCLike.inner_apply, conj_trivial, mul_one]

theorem dualWitness_supported (M : ℕ) : finiteHead M (dualWitness M) = dualWitness M := by
  classical
  apply lp.ext
  funext n
  by_cases hn : n < M
  · exact finiteHead_apply_of_lt M (dualWitness M) n hn
  · have hnM : M ≤ n := Nat.le_of_not_gt hn
    rw [finiteHead_apply_eq_zero M (dualWitness M) n hnM]
    symm
    rw [← coordinate_atom_inner n (dualWitness M), dualWitness, inner_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [inner_smul_right, coordinate_atom_inner]
    have hne : n ≠ (i : ℕ) := by omega
    simp [lp.single_apply, hne]

theorem dualWitness_projection (M : ℕ) :
    QFullResidueProjection.closure.starProjection (dualWitness M) = optimizer M := by
  classical
  simp only [dualWitness, map_sum, map_smul, optimizer, minimumVector,
    Fintype.linearCombination_apply, headRow, dualCoefficients]

theorem dualWitness_pairing (M : ℕ) :
    inner ℝ qOne (dualWitness M) = energy M := by
  classical
  rw [dualWitness, inner_sum, energy_inverseGram]
  simp only [inner_smul_right, lp.inner_single_right, RCLike.inner_apply,
    conj_trivial, one_mul, dualCoefficients, targetHead]

theorem dualWitness_projected_norm_sq (M : ℕ) :
    ‖QFullResidueProjection.closure.starProjection (dualWitness M)‖ ^ 2 = energy M := by
  rw [dualWitness_projection]
  rfl

/-- The head-zero problem is excluded: its dual denominator is identically zero. -/
theorem energy_pos (M : ℕ) (hM : 0 < M) : 0 < energy M := by
  apply minimumVector_norm_sq_pos (headRow_linearIndependent M) (targetHead M)
  intro hz
  have hzero : qOne 0 = 0 := congrFun hz (⟨0, hM⟩ : Fin M)
  have he : qSequence qOne (0 + 1) = 1 := by
    rw [qSequence_qOne]
    simp [qOneSequence]
  rw [qSequence_succ, hzero, zero_div] at he
  exact zero_ne_one he

theorem optimal_finiteHead_squared_bound (M : ℕ) (a : QHilbert) :
    (inner ℝ qOne (finiteHead M a)) ^ 2 ≤ energy M *
      ‖QFullResidueProjection.closure.starProjection (finiteHead M a)‖ ^ 2 := by
  have h := optimal_finiteHead_bound M a
  have hs := mul_self_le_mul_self
    (abs_nonneg (inner ℝ qOne (finiteHead M a))) h
  dsimp [energy]
  nlinarith [sq_abs (inner ℝ qOne (finiteHead M a))]

/-- The optimal signed squared constant is attained by a finite supported test. -/
theorem energy_isLeast_squared_dual_constant (M : ℕ) (hM : 0 < M) :
    IsLeast {C : ℝ | ∀ a : QHilbert,
      (inner ℝ qOne (finiteHead M a)) ^ 2 ≤ C *
        ‖QFullResidueProjection.closure.starProjection (finiteHead M a)‖ ^ 2}
      (energy M) := by
  refine ⟨optimal_finiteHead_squared_bound M, ?_⟩
  intro C hC
  have h := hC (dualWitness M)
  rw [dualWitness_supported, dualWitness_pairing, dualWitness_projected_norm_sq,
    pow_two] at h
  nlinarith [energy_pos M hM]

/-- Exact attained dual quotient, with its positive denominator exposed. -/
theorem dualWitness_quotient (M : ℕ) (hM : 0 < M) :
    0 < ‖QFullResidueProjection.closure.starProjection (dualWitness M)‖ ^ 2 ∧
    (inner ℝ qOne (dualWitness M)) ^ 2 /
      ‖QFullResidueProjection.closure.starProjection (dualWitness M)‖ ^ 2 = energy M := by
  rw [dualWitness_projected_norm_sq, dualWitness_pairing]
  refine ⟨energy_pos M hM, ?_⟩
  rw [pow_two, mul_div_cancel_right₀ _ (ne_of_gt (energy_pos M hM))]



end RiemannResearch.RH.QOptimalExactHead
