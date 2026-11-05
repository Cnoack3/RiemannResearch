/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QSquarefreeClosedKernel
import RiemannResearch.RH.QSquarefreeLogDisplacement
import RiemannResearch.RH.QSquarefreeCRTContinuity
import RiemannResearch.RH.QSquarefreeDisplacementResolvent
import RiemannResearch.RH.QSquarefreeDisplacementRigidity
import RiemannResearch.RH.QSquarefreeCoordinateLegality
import RiemannResearch.RH.QSquarefreeCapacity
import RiemannResearch.RH.SquarefreeRadicalDifference
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoOptimizerStage
import RiemannResearch.NumberTheory.RadicalFiberSeparation
import Mathlib.Topology.Sequences
import Mathlib.Tactic.Push
import Lean.Elab.Tactic.Omega

/-!
# Arithmetic recurrence and the unresolved projection regularity

The actual displacement obeys a radical difference recurrence, an exact
signed kernel equation, and normal equations. If it is nonzero, its physical
values blow up along some convergent CRT sequence, and the actual projection
takes the vanishing vector B r_P to an unbounded vector.

The smoothed-kernel bound and the c0-to-bounded projection premise below are
conditional research reductions. Both premises remain Open. Neither Hilbert
contraction nor the completion universal property proves them.

Sources: existing squarefree radical identities and displacement rigidity;
Mathlib.Topology.Sequences, CompactSpace.tendsto_subseq, for the standard
compactness argument; Bagchi (2006), arXiv:math/0607733, Remark 8, for the
published squarefree RH criterion. The inherited Lean RH bridge supplies
only the direction used here, not a new formalization of its converse.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QSquarefreeDisplacementRegularity
open ZetaTwoHilbert ZetaTwoOptimizerStage QSquarefreeDisplacementRigidity
open QSquarefreeDisplacementResolvent QShiftedReciprocal QSquarefreeCRTContinuity
open QSquarefreeCRTRegularity QSquarefreeClosedKernel
open SquarefreeRadicalDifference UniqueFactorizationMonoid

theorem displacement_physical_tsum (n : ℕ) :
    qSequence displacement n = ∑' m, positiveQWeight m *
      (qSequence pResidual m / ((m : ℝ) + 1)) * qSequence (closedKernel n) m := by
  calc
    _ = qSequence (closure.starProjection (B pResidual)) n :=
      congrArg (fun f => qSequence f n) displacement_eq_projected_pResidual
    _ = _ := by rw [projected_physical_tsum]; simp only [qSequence_B]

theorem displacement_normal_equation (v : QHilbert) (hv : v ∈ closure) :
    inner ℝ v displacement = inner ℝ v (B pResidual) := by
  have h := Submodule.inner_right_of_mem_orthogonal hv witness_mem_orthogonal
  rw [witness, inner_sub_right] at h
  exact (sub_eq_zero.mp h).symm

theorem residual_zero_of_projection_preserves_c0_bound
    (hP : ∀ f : QHilbert, Tendsto (qSequence f) atTop (𝓝 0) →
      ∃ C : ℝ, ∀ n, |qSequence (closure.starProjection f) n| ≤ C) :
    limitingResidual = 0 := by
  obtain ⟨C, hC⟩ := hP (B pResidual) (B_physical_tendsto_zero pResidual)
  apply residual_eq_zero_of_displacement_physically_bounded C
  simpa only [← displacement_eq_projected_pResidual] using hC

theorem displacement_difference_radical (m : ℕ) (hm : 2 ≤ m) :
    qDifference displacement m = qDifference displacement (radical m) := by
  apply QSquarefreeCoordinateLegality.closure_difference_radical _ m hm
  rw [← QSquarefreeCapacity.optimizer_closure_eq_squarefree_closure]
  exact displacement_mem

theorem displacement_difference_squarefree_power {s k : ℕ}
    (hs : 2 ≤ s) (hsf : Squarefree s) (hk : k ≠ 0) :
    qDifference displacement (s ^ k) = qDifference displacement s := by
  have hpow : 2 ≤ s ^ k := hs.trans (by
    simpa using Nat.pow_le_pow_right (by omega : 0 < s) (by omega : 1 ≤ k))
  rw [displacement_difference_radical _ hpow,
    Nat.radical_pow_eq_of_squarefree hs hsf hk]

theorem projected_decay_unbounded_of_residual_ne_zero (hr : limitingResidual ≠ 0) :
    ∃ f : QHilbert, Tendsto (qSequence f) atTop (𝓝 0) ∧
      ∀ C : ℝ, ∃ n : ℕ, C < |qSequence (closure.starProjection f) n| := by
  refine ⟨B pResidual, QSquarefreeCRTContinuity.B_physical_tendsto_zero _, ?_⟩
  intro C
  rw [← displacement_eq_projected_pResidual]
  by_contra h
  push Not at h
  exact hr (residual_eq_zero_of_displacement_physically_bounded C h)

theorem displacement_crt_blowup_of_ne_zero (hd : displacement ≠ 0) :
    ∃ (a : ℕ → ℕ) (x : PrimeResidueSpace),
      (∀ k, 1 ≤ a k) ∧
      Tendsto (fun k => physicalPoint (a k)) atTop (𝓝 x) ∧
      Tendsto (fun k => |qSequence displacement (a k)|) atTop atTop := by
  classical
  let (p : Nat.Primes) : NeZero p.val := ⟨p.property.ne_zero⟩
  have hr : limitingResidual ≠ 0 :=
    fun h => hd (displacement_eq_zero_of_residual_eq_zero h)
  have hex : ∀ j : ℕ, ∃ n : ℕ,
      (j : ℝ) < |qSequence displacement n| := by
    intro j
    by_contra h
    push Not at h
    exact hr (residual_eq_zero_of_displacement_physically_bounded (j : ℝ) h)
  choose a ha using hex
  obtain ⟨x, φ, hφ, hx⟩ :=
    CompactSpace.tendsto_subseq (fun j => physicalPoint (a j))
  refine ⟨a ∘ φ, x, ?_, ?_, ?_⟩
  · intro k
    have hn : a (φ k) ≠ 0 := by
      intro hz
      have ht := ha (φ k)
      rw [hz, qSequence_zero, abs_zero] at ht
      exact (not_lt_of_ge (Nat.cast_nonneg (φ k))) ht
    exact Nat.one_le_iff_ne_zero.mpr hn
  · simpa only [Function.comp_def] using hx
  · apply tendsto_atTop.2
    intro b
    obtain ⟨N, hN⟩ := exists_nat_gt b
    filter_upwards [(tendsto_atTop.1 hφ.tendsto_atTop) N] with k hk
    exact (hN.le.trans (Nat.cast_le.mpr hk)).trans (ha (φ k)).le

theorem displacement_eq_smoothed_kernel_pairing (n : ℕ) :
    qSequence displacement n = inner ℝ pResidual (B (closedKernel n)) := by
  rw [displacement_eq_projected_pResidual, projected_physical_pairing]
  exact B_symmetric _ _

theorem displacement_abs_le_smoothed_kernel (n : ℕ) :
    |qSequence displacement n| ≤ ‖pResidual‖ * ‖B (closedKernel n)‖ := by
  rw [displacement_eq_smoothed_kernel_pairing]
  exact abs_real_inner_le_norm _ _

theorem residual_zero_of_smoothed_kernel_bound (C : ℝ)
    (hC : ∀ n, ‖B (closedKernel n)‖ ≤ C) : limitingResidual = 0 := by
  apply residual_eq_zero_of_displacement_physically_bounded (‖pResidual‖ * C)
  intro n
  exact (displacement_abs_le_smoothed_kernel n).trans
    (mul_le_mul_of_nonneg_left (hC n) (norm_nonneg _))

/-- Conditional research reduction. An eventual fixed polylogarithmic bound on the
smoothed kernels implies residual vanishing by the physical polylogarithmic
displacement criterion. The kernel growth hypothesis remains open. -/
theorem residual_zero_of_smoothed_kernel_polylog_bound
    (m : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hK : ∀ᶠ n : ℕ in atTop,
      ‖B (closedKernel n)‖ ≤ C * (6 + Real.log (n : ℝ)) ^ m) :
    limitingResidual = 0 := by
  apply
    (QSquarefreeLogDisplacement.residual_zero_iff_eventually_polylog_displacement m).mpr
  refine ⟨‖pResidual‖ * C, mul_nonneg (norm_nonneg _) hC, ?_⟩
  filter_upwards [hK] with n hn
  calc
    |qSequence displacement n| ≤ ‖pResidual‖ * ‖B (closedKernel n)‖ :=
      displacement_abs_le_smoothed_kernel n
    _ ≤ ‖pResidual‖ * (C * (6 + Real.log (n : ℝ)) ^ m) :=
      mul_le_mul_of_nonneg_left hn (norm_nonneg _)
    _ = (‖pResidual‖ * C) * (6 + Real.log (n : ℝ)) ^ m :=
      (mul_assoc _ _ _).symm

end RiemannResearch.RH.QSquarefreeDisplacementRegularity
