/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.TwoSeedExactHeadEnergy
import RiemannResearch.RH.FiniteTwoSeedHeadRepair
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Geometry of the actual two-seed exact-head optimum

Source: independently developed from the user-provided full-energy problem,
14 September 2026. Finite-head repair identifies the finite legal infimum
with a minimum in the closed legal space. Orthogonal projection constructs
that minimizer and gives an exact Pythagorean identity as the head grows.
No growth estimate for the energy is assumed in this construction.
-/

open Filter
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.TwoSeedExactHeadEnergy

noncomputable section

open FiniteTwoSeedCompletion

/-- The exact-head fiber in the closed legal space. -/
def ClosedFeasible (N : ℕ) (f : ThresholdHilbert) : Prop :=
  f ∈ hilbertLegalClosure ({2, 3} : Set ℕ) ∧
    ∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1

theorem feasible_closed {N : ℕ} {f : ThresholdHilbert} (hf : Feasible N f) :
    ClosedFeasible N f := ⟨Submodule.le_topologicalClosure _ hf.1, hf.2⟩

theorem closedFeasible_of_le {N M : ℕ} (hNM : N ≤ M)
    {f : ThresholdHilbert} (hf : ClosedFeasible M f) : ClosedFeasible N f :=
  ⟨hf.1, fun k hk hkN => hf.2 k hk (hkN.trans hNM)⟩

/-- Taking the Hilbert closure does not lower the actual finite legal infimum. -/
theorem energy_le_closed {N : ℕ} {f : ThresholdHilbert} (hf : ClosedFeasible N f) :
    energy N ≤ ‖f‖ ^ 2 := by
  by_contra h
  have hlt : ‖f‖ ^ 2 < energy N := lt_of_not_ge h
  have ho : IsOpen {g : ThresholdHilbert | ‖g‖ ^ 2 < energy N} :=
    isOpen_lt (continuous_norm.pow 2) continuous_const
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp ho f hlt
  obtain ⟨g, hg, hhead, hnear⟩ := exists_legal_near_with_same_head hf.1 N hδ
  have hgf : Feasible N g :=
    ⟨hg, fun k hk hkN => (hhead k hk hkN).trans (hf.2 k hk hkN)⟩
  have hgn : ‖g‖ ^ 2 < energy N := hball
    (by simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hnear)
  exact (not_lt_of_ge (energy_le hgf)) hgn

/-- The bounded restriction to the first `N` physical coordinates. -/
def headRestriction (N : ℕ) : ThresholdHilbert →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.pi fun i => physicalEvaluation i.val

@[simp] theorem headRestriction_apply (N : ℕ) (f : ThresholdHilbert) (i : Fin N) :
    headRestriction N f i = hilbertSequence f (i.val + 1) := by
  simp [headRestriction]

/-- Closed legal directions that preserve the current exact head. -/
def zeroHeadLegal (N : ℕ) : Submodule ℝ ThresholdHilbert :=
  hilbertLegalClosure ({2, 3} : Set ℕ) ⊓ (headRestriction N).ker

theorem zeroHeadLegal_mem_iff (N : ℕ) (f : ThresholdHilbert) :
    f ∈ zeroHeadLegal N ↔ f ∈ hilbertLegalClosure ({2, 3} : Set ℕ) ∧
      ∀ k, k < N → hilbertSequence f (k + 1) = 0 := by
  change (f ∈ hilbertLegalClosure ({2, 3} : Set ℕ) ∧ headRestriction N f = 0) ↔ _
  constructor
  · rintro ⟨hf, hh⟩
    refine ⟨hf, ?_⟩
    intro k hk
    have := congrFun hh ⟨k, hk⟩
    simpa using this
  · rintro ⟨hf, hh⟩
    refine ⟨hf, ?_⟩
    ext i
    simpa using hh i.val i.isLt

theorem zeroHeadLegal_isClosed (N : ℕ) : IsClosed (zeroHeadLegal N : Set ThresholdHilbert) :=
  (Submodule.isClosed_topologicalClosure _).inter (headRestriction N).isClosed_ker

instance zeroHeadLegal_complete (N : ℕ) : CompleteSpace (zeroHeadLegal N) := by
  let : IsClosed (zeroHeadLegal N : Set ThresholdHilbert) := zeroHeadLegal_isClosed N
  exact IsClosed.completeSpace_coe

private def headBase (N : ℕ) : ThresholdHilbert := Classical.choose (feasible_nonempty N)

private theorem headBase_feasible (N : ℕ) : Feasible N (headBase N) :=
  Classical.choose_spec (feasible_nonempty N)

/-- The minimum-norm exact-head vector in the closed legal space. -/
def closedMinimizer (N : ℕ) : ThresholdHilbert :=
  headBase N - (zeroHeadLegal N).starProjection (headBase N)

/-- Canonical minimization removes every legal direction with zero current head. -/
theorem closedMinimizer_orthogonal_zeroHead {N : ℕ} {g : ThresholdHilbert}
    (hg : g ∈ zeroHeadLegal N) : inner ℝ (closedMinimizer N) g = 0 :=
  Submodule.starProjection_inner_eq_zero (headBase N) g hg

theorem closedMinimizer_feasible (N : ℕ) : ClosedFeasible N (closedMinimizer N) := by
  have hb := feasible_closed (headBase_feasible N)
  have hp : (zeroHeadLegal N).starProjection (headBase N) ∈ zeroHeadLegal N :=
    Submodule.starProjection_apply_mem _ _
  obtain ⟨hpv, hph⟩ := (zeroHeadLegal_mem_iff N _).mp hp
  refine ⟨(hilbertLegalClosure ({2, 3} : Set ℕ)).sub_mem hb.1 hpv, ?_⟩
  intro k hk hkN
  cases k with
  | zero => omega
  | succ k =>
      change hilbertSequenceLinear (headBase N -
        (zeroHeadLegal N).starProjection (headBase N)) (k + 1) = 1
      rw [map_sub]
      change hilbertSequence (headBase N) (k + 1) -
        hilbertSequence ((zeroHeadLegal N).starProjection (headBase N)) (k + 1) = 1
      rw [hb.2 (k + 1) (by omega) hkN, hph k (by omega), sub_zero]

theorem closedFeasible_sub_minimizer_mem {N : ℕ} {g : ThresholdHilbert}
    (hg : ClosedFeasible N g) : g - closedMinimizer N ∈ zeroHeadLegal N := by
  apply (zeroHeadLegal_mem_iff N _).mpr
  refine ⟨(hilbertLegalClosure ({2, 3} : Set ℕ)).sub_mem hg.1
    (closedMinimizer_feasible N).1, ?_⟩
  intro k hk
  change hilbertSequenceLinear (g - closedMinimizer N) (k + 1) = 0
  rw [map_sub]
  change hilbertSequence g (k + 1) - hilbertSequence (closedMinimizer N) (k + 1) = 0
  rw [hg.2 (k + 1) (by omega) (by omega),
    (closedMinimizer_feasible N).2 (k + 1) (by omega) (by omega), sub_self]

/-- The minimum retains the complete signed Hilbert energy. -/
theorem closedMinimizer_energy_split {N : ℕ} {g : ThresholdHilbert}
    (hg : ClosedFeasible N g) :
    ‖g‖ ^ 2 = ‖closedMinimizer N‖ ^ 2 + ‖g - closedMinimizer N‖ ^ 2 := by
  have ho : inner ℝ (closedMinimizer N) (g - closedMinimizer N) = 0 :=
    Submodule.starProjection_inner_eq_zero (headBase N) (g - closedMinimizer N)
      (closedFeasible_sub_minimizer_mem hg)
  have ho' : inner ℝ (g - closedMinimizer N) (closedMinimizer N) = 0 := by
    rw [real_inner_comm]
    exact ho
  have he : g = closedMinimizer N + (g - closedMinimizer N) := by abel
  conv_lhs => rw [he]
  rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    inner_add_right, ho, ho', real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  ring

/-- The closed minimum equals the infimum over actual finite legal witnesses. -/
theorem closedMinimizer_norm_sq (N : ℕ) : ‖closedMinimizer N‖ ^ 2 = energy N := by
  apply le_antisymm
  · apply le_energy
    intro g hg
    rw [closedMinimizer_energy_split (feasible_closed hg)]
    exact le_add_of_nonneg_right (sq_nonneg _)
  · exact energy_le_closed (closedMinimizer_feasible N)

/-- Increasing the head creates exactly orthogonal energy increments. -/
theorem nested_minimizer_energy {N M : ℕ} (hNM : N ≤ M) :
    energy M = energy N + ‖closedMinimizer M - closedMinimizer N‖ ^ 2 := by
  have h := closedMinimizer_energy_split
    (closedFeasible_of_le hNM (closedMinimizer_feasible M))
  simpa only [closedMinimizer_norm_sq] using h

theorem energy_le_sup (hb : BddAbove (Set.range energy)) (N : ℕ) :
    energy N ≤ sSup (Set.range energy) :=
  le_csSup hb ⟨N, rfl⟩

theorem energy_tendsto_sup (hb : BddAbove (Set.range energy)) :
    Tendsto energy atTop (nhds (sSup (Set.range energy))) := by
  apply tendsto_order.2
  constructor
  · intro b hb'
    have hex : ∃ N, b < energy N := by
      by_contra! h
      have hs : sSup (Set.range energy) ≤ b := by
        apply csSup_le (s := Set.range energy) ⟨energy 0, 0, rfl⟩
        rintro e ⟨N, rfl⟩
        exact h N
      linarith
    obtain ⟨N, hN⟩ := hex
    filter_upwards [eventually_ge_atTop N] with M hM
    exact hN.trans_le (energy_monotone hM)
  · intro b hb'
    exact Filter.Eventually.of_forall fun N => (energy_le_sup hb N).trans_lt hb'

/-- Bounded optimal energy makes the actual closed minimizers a Cauchy sequence. -/
theorem closedMinimizer_cauchy_of_bddAbove (hb : BddAbove (Set.range energy)) :
    CauchySeq closedMinimizer := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hgap : sSup (Set.range energy) - ε ^ 2 < sSup (Set.range energy) := by
    nlinarith [sq_pos_of_pos hε]
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((energy_tendsto_sup hb).eventually (lt_mem_nhds hgap))
  refine ⟨N, ?_⟩
  intro m hm n hn
  rcases le_total n m with hnm | hmn
  · rw [dist_eq_norm]
    have he := nested_minimizer_energy hnm
    have hu := energy_le_sup hb m
    have hl := hN n hn
    nlinarith [norm_nonneg (closedMinimizer m - closedMinimizer n)]
  · rw [dist_comm, dist_eq_norm]
    have he := nested_minimizer_energy hmn
    have hu := energy_le_sup hb n
    have hl := hN m hm
    nlinarith [norm_nonneg (closedMinimizer n - closedMinimizer m)]

/-- Any bounded optimum forces strong convergence of the closed minimizers to one. -/
theorem closedMinimizer_tendsto_one_of_bddAbove (hb : BddAbove (Set.range energy)) :
    Tendsto closedMinimizer atTop (nhds hilbertOne) := by
  obtain ⟨f, hf⟩ := cauchySeq_tendsto_of_complete (closedMinimizer_cauchy_of_bddAbove hb)
  have hcoord (k : ℕ) : physicalEvaluation k f = 1 := by
    have ht : Tendsto (fun N => physicalEvaluation k (closedMinimizer N))
        atTop (nhds (physicalEvaluation k f)) :=
      ((physicalEvaluation k).continuous.tendsto f).comp hf
    have he : ∀ᶠ N : ℕ in atTop, physicalEvaluation k (closedMinimizer N) = 1 := by
      filter_upwards [eventually_ge_atTop (k + 1)] with N hN
      simpa only [physicalEvaluation_apply] using
        (closedMinimizer_feasible N).2 (k + 1) (by omega) hN
    have he' : (fun _ : ℕ => (1 : ℝ)) =ᶠ[atTop]
        (fun N => physicalEvaluation k (closedMinimizer N)) := by
      filter_upwards [he] with N hN
      exact hN.symm
    have ht' : Tendsto (fun N => physicalEvaluation k (closedMinimizer N))
        atTop (nhds (1 : ℝ)) := tendsto_const_nhds.congr' he'
    exact tendsto_nhds_unique ht ht'
  have hfone : f = hilbertOne := by
    apply hilbertSequence_injective
    funext k
    cases k with
    | zero => simp
    | succ k =>
        have hOne : hilbertSequence hilbertOne (k + 1) = 1 := by
          rw [hilbertOne_sequence]
          simp [zeroAnchor]
        calc
          hilbertSequence f (k + 1) = physicalEvaluation k f :=
            (physicalEvaluation_apply k f).symm
          _ = 1 := hcoord k
          _ = hilbertSequence hilbertOne (k + 1) := hOne.symm
  simpa only [hfone] using hf

theorem hilbertOne_mem_closure_of_energy_bddAbove (hb : BddAbove (Set.range energy)) :
    hilbertOne ∈ hilbertLegalClosure ({2, 3} : Set ℕ) := by
  exact (Submodule.isClosed_topologicalClosure _).mem_of_tendsto
    (closedMinimizer_tendsto_one_of_bddAbove hb)
    (Filter.Eventually.of_forall fun N => (closedMinimizer_feasible N).1)

/-- Once one belongs to the closure, the infimum at every fixed head is at most one. -/
theorem energy_le_one_of_closure
    (h1 : hilbertOne ∈ hilbertLegalClosure ({2, 3} : Set ℕ)) (N : ℕ) : energy N ≤ 1 := by
  have hh : ClosedFeasible N hilbertOne := by
    refine ⟨h1, ?_⟩
    intro k hk hkN
    simp [hilbertOne_sequence, zeroAnchor, Nat.ne_of_gt hk]
  simpa only [hilbertOne_norm_sq] using energy_le_closed hh

/-- Uniform boundedness of the actual finite-legal infimum is exactly the
two-seed closure problem, independently of the Mellin-to-RH implication. -/
theorem energy_bddAbove_iff_closure :
    BddAbove (Set.range energy) ↔ hilbertOne ∈ hilbertLegalClosure ({2, 3} : Set ℕ) := by
  constructor
  · exact hilbertOne_mem_closure_of_energy_bddAbove
  · intro h1
    refine ⟨1, ?_⟩
    rintro e ⟨N, rfl⟩
    exact energy_le_one_of_closure h1 N

/-- In the bounded case the limit is forced to be exactly one. -/
theorem energy_tendsto_one_of_bddAbove (hb : BddAbove (Set.range energy)) :
    Tendsto energy atTop (nhds 1) := by
  have h1 := hilbertOne_mem_closure_of_energy_bddAbove hb
  have ht : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun N => by linarith) tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹) atTop (nhds (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp ht
  have hl : Tendsto (fun N : ℕ => 1 - ((N : ℝ) + 1)⁻¹) atTop (nhds (1 : ℝ)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hi
  have hlow (N : ℕ) : 1 - ((N : ℝ) + 1)⁻¹ ≤ energy N := by
    have he : 1 - ((N : ℝ) + 1)⁻¹ = (N : ℝ) / ((N : ℝ) + 1) := by
      have hn : (N : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    rw [he]
    exact head_floor_le_energy N
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl tendsto_const_nhds hlow
    (energy_le_one_of_closure h1)

/-- The actual optimum has no finite limiting plateau above one. -/
theorem energy_limit_dichotomy :
    Tendsto energy atTop (nhds 1) ∨ Tendsto energy atTop atTop := by
  by_cases hb : BddAbove (Set.range energy)
  · exact Or.inl (energy_tendsto_one_of_bddAbove hb)
  · right
    apply tendsto_atTop.mpr
    intro B
    obtain ⟨e, he, hB⟩ := not_bddAbove_iff.mp hb B
    obtain ⟨N, rfl⟩ := he
    filter_upwards [eventually_ge_atTop N] with M hM
    exact hB.le.trans (energy_monotone hM)

end

end RiemannResearch.RH.Pareto.TwoSeedExactHeadEnergy
