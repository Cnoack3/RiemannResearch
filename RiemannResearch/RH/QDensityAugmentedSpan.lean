/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QDensityMetric
import RiemannResearch.RH.QReciprocalMetric
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.ThresholdHilbertSpace
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Squarefree
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Density-augmented prime and squarefree approximation

Source: user-provided residue-quotient argument, 8 November 2026.
For every positive conductor m, the approximant m * D(g_m) has physical
value (n mod m) / n and equals zetaTwo * m * B(g_m) - m * g_m.

The complete squared Q-error is retained as an exact infinite sum.
Pointwise eventual equality to one and the uniform bound by one give norm
convergence by dominated convergence for series. Any unbounded conductor
family therefore gives one in its density-augmented closed span. Primes
already suffice; squarefree conductors greater than one are a consequence.

The sequence-preserving Pareto equivalence transfers the squarefree result
to L²(P). These are unconditional augmented-span statements. They neither
assume RH nor establish membership in the unaugmented legal span.
-/

noncomputable section
namespace RiemannResearch.RH.QDensityMetric
open ZetaTwoHilbert ZetaTwoProbability

def approximation (m : ℕ) : QHilbert :=
  (m : ℝ) • QReciprocalMetric.D (qResidue m)

theorem approximation_sequence (m k : ℕ) (hm : 0 < m) :
    qSequence (approximation m) k = ((k % m : ℕ) : ℝ) / (k : ℝ) := by
  change qSequenceLinear ((m : ℝ) • QReciprocalMetric.D (qResidue m)) k = _
  rw [map_smul]
  change (m : ℝ) * qSequence (QReciprocalMetric.D (qResidue m)) k = _
  rw [QReciprocalMetric.qSequence_D, qSequence_qResidue]
  unfold ArithmeticCumulative.residueFraction
  have hmR : (m : ℝ) ≠ 0 := by positivity
  field_simp [hmR]

theorem approximation_eq_density_combination (m : ℕ) :
    approximation m = (zetaTwo * (m : ℝ)) • B (qResidue m) -
      (m : ℝ) • qResidue m := by
  apply Subtype.ext
  funext n
  change (m : ℝ) * (qResidue m n / ((n : ℝ) + 1)) =
    (zetaTwo * (m : ℝ)) * ((1 / zetaTwo) *
      (qResidue m n + qResidue m n / ((n : ℝ) + 1))) -
    (m : ℝ) * qResidue m n
  field_simp [ne_of_gt zetaTwo_pos]
  ring

theorem approximation_error_sequence (m k : ℕ) (hm : 0 < m) :
    qSequence (approximation m - qOne) k =
      ((k % m : ℕ) : ℝ) / (k : ℝ) - qOneSequence k := by
  change qSequenceLinear (approximation m - qOne) k = _
  rw [map_sub]
  change qSequence (approximation m) k - qSequence qOne k = _
  rw [approximation_sequence m k hm, qSequence_qOne]

theorem approximation_sequence_bounds (m k : ℕ) (hm : 0 < m) :
    0 ≤ qSequence (approximation m) k ∧ qSequence (approximation m) k ≤ 1 := by
  rw [approximation_sequence m k hm]
  constructor
  · positivity
  · by_cases hk : k = 0
    · simp [hk]
    · apply (div_le_one (show (0 : ℝ) < k by exact_mod_cast Nat.pos_of_ne_zero hk)).mpr
      exact_mod_cast Nat.mod_le k m

theorem approximation_error_abs_le_one (m k : ℕ) (hm : 0 < m) :
    |qSequence (approximation m - qOne) k| ≤ 1 := by
  have hb := approximation_sequence_bounds m k hm
  change |qSequenceLinear (approximation m - qOne) k| ≤ 1
  rw [map_sub]
  change |qSequence (approximation m) k - qSequence qOne k| ≤ 1
  rw [qSequence_qOne]
  by_cases hk : k = 0
  · simp [hk, qOneSequence]
  · rw [qOneSequence, if_neg hk]
    exact abs_le.mpr ⟨by linarith [hb.1], by linarith [hb.2]⟩

/-- The entire Q-energy, including the infinite tail, is retained. -/
theorem approximation_error_norm_sq (m : ℕ) (hm : 0 < m) :
    ‖approximation m - qOne‖ ^ 2 =
      ∑' k : ℕ, positiveQWeight k *
        (((k % m : ℕ) : ℝ) / (k : ℝ) - qOneSequence k) ^ 2 := by
  rw [qNorm_weighted_sq]
  apply tsum_congr
  intro k
  rw [approximation_error_sequence m k hm]

open Filter
open scoped Topology

theorem approximation_tendsto :
    Tendsto approximation atTop (𝓝 qOne) := by
  let f : ℕ → ℕ → ℝ := fun m k =>
    positiveQWeight k * (qSequence (approximation m - qOne) k) ^ 2
  have hpoint (k : ℕ) : Tendsto (fun m => f m k) atTop (𝓝 0) := by
    have hz : ∀ᶠ m : ℕ in atTop, f m k = 0 := by
      filter_upwards [eventually_gt_atTop k] with m hm
      have hm0 : 0 < m := (Nat.zero_le k).trans_lt hm
      dsimp [f]
      rw [approximation_error_sequence m k hm0, Nat.mod_eq_of_lt hm]
      by_cases hk : k = 0
      · simp [hk, qOneSequence]
      · simp [qOneSequence, hk, Nat.cast_ne_zero.mpr hk]
    exact tendsto_const_nhds.congr' (hz.mono fun _ hm => hm.symm)
  have hbound : ∀ᶠ m : ℕ in atTop, ∀ k, ‖f m k‖ ≤ positiveQWeight k := by
    filter_upwards [eventually_gt_atTop 0] with m hm k
    have hb := approximation_error_abs_le_one m k hm
    have hs : (qSequence (approximation m - qOne) k) ^ 2 ≤ 1 := by
      have h := mul_le_mul hb hb (abs_nonneg _) zero_le_one
      simpa only [← pow_two, sq_abs, one_pow] using h
    change |positiveQWeight k * (qSequence (approximation m - qOne) k) ^ 2| ≤ _
    rw [abs_of_nonneg
      (mul_nonneg (positiveQWeight_nonneg k) (sq_nonneg _))]
    exact mul_le_of_le_one_right (positiveQWeight_nonneg k) hs
  have ht := tendsto_tsum_of_dominated_convergence
    (g := fun _ : ℕ => (0 : ℝ)) positiveQWeight_summable hpoint hbound
  have hsq : Tendsto (fun m => ‖approximation m - qOne‖ ^ 2) atTop (𝓝 0) := by
    simpa only [f, ← qNorm_weighted_sq, tsum_zero] using ht
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hn

/-- Finite linear span of the residue atoms and their density images. -/
def augmentedSpan (s : Set ℕ) : Submodule ℝ QHilbert :=
  Submodule.span ℝ {f | ∃ m, m ∈ s ∧
    (f = qResidue m ∨ f = B (qResidue m))}

theorem approximation_mem_augmentedSpan (s : Set ℕ) (m : ℕ) (hm : m ∈ s) :
    approximation m ∈ augmentedSpan s := by
  have hg : qResidue m ∈ augmentedSpan s :=
    Submodule.subset_span ⟨m, hm, Or.inl rfl⟩
  have hBg : B (qResidue m) ∈ augmentedSpan s :=
    Submodule.subset_span ⟨m, hm, Or.inr rfl⟩
  rw [approximation_eq_density_combination]
  exact (augmentedSpan s).sub_mem
    ((augmentedSpan s).smul_mem _ hBg) ((augmentedSpan s).smul_mem _ hg)

/-- Any unbounded conductor family suffices after adjoining its density images. -/
theorem one_mem_augmentedClosure_of_unbounded (s : Set ℕ)
    (hs : ∀ N : ℕ, ∃ m, N ≤ m ∧ m ∈ s) :
    qOne ∈ (augmentedSpan s).topologicalClosure := by
  classical
  choose p hp hpS using hs
  have hpt : Tendsto p atTop atTop := tendsto_atTop_mono hp tendsto_id
  change qOne ∈ _root_.closure (augmentedSpan s : Set QHilbert)
  exact mem_closure_of_tendsto (approximation_tendsto.comp hpt)
    (Eventually.of_forall fun N => approximation_mem_augmentedSpan s (p N) (hpS N))

theorem one_mem_prime_augmentedClosure :
    qOne ∈ (augmentedSpan {m : ℕ | m.Prime}).topologicalClosure :=
  one_mem_augmentedClosure_of_unbounded _ Nat.exists_infinite_primes

/-- The requested squarefree density-augmented approximation theorem. -/
theorem one_mem_squarefree_augmentedClosure :
    qOne ∈ (augmentedSpan {m : ℕ | 1 < m ∧ Squarefree m}).topologicalClosure := by
  apply one_mem_augmentedClosure_of_unbounded
  intro N
  obtain ⟨p, hN, hp⟩ := Nat.exists_infinite_primes N
  exact ⟨p, hN, hp.one_lt, hp.prime.squarefree⟩

open Pareto ZetaTwoParetoTransfer QParetoEquivalence

/-- The same physical generator family in the Pareto realization. -/
def paretoAugmentedSpan (s : Set ℕ) : Submodule ℝ ThresholdHilbert :=
  Submodule.span ℝ {f | ∃ m, m ∈ s ∧
    (f = toPareto (qResidue m) ∨ f = toPareto (B (qResidue m)))}

theorem map_augmentedSpan (s : Set ℕ) :
    (augmentedSpan s).map paretoEquiv.toLinearMap = paretoAugmentedSpan s := by
  unfold augmentedSpan paretoAugmentedSpan
  rw [Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨m, hm, hx⟩, rfl⟩
    rcases hx with rfl | rfl
    · exact ⟨m, hm, Or.inl rfl⟩
    · exact ⟨m, hm, Or.inr rfl⟩
  · rintro ⟨m, hm, hy⟩
    rcases hy with rfl | rfl
    · exact ⟨qResidue m, ⟨m, hm, Or.inl rfl⟩, rfl⟩
    · exact ⟨B (qResidue m), ⟨m, hm, Or.inr rfl⟩, rfl⟩

theorem pareto_one_mem_squarefree_augmentedClosure :
    hilbertOne ∈
      (paretoAugmentedSpan {m : ℕ | 1 < m ∧ Squarefree m}).topologicalClosure := by
  have h := (mem_closure_map_iff
    (augmentedSpan {m : ℕ | 1 < m ∧ Squarefree m}) qOne).mpr
      one_mem_squarefree_augmentedClosure
  simpa only [toPareto_qOne, map_augmentedSpan] using h

end RiemannResearch.RH.QDensityMetric
