/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.RamanujanBlockEnlargement
import RiemannResearch.RH.RamanujanSaturationCriteria
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import RiemannResearch.RH.RamanujanCanonicalOptimizer
import RiemannResearch.RH.MobiusCoefficientStabilization
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum

/-!
# The actual squarefree packet cutoff capacity

Source: user-requested constructive squarefree-capacity investigation,
24 October 2026. The index contains exactly the squarefree conductors from
2 through n+1. Every Gram entry is the complete Pareto inner product.
Monotonicity and convergence to a supremum are unconditional. Identifying
that supremum with one remains an explicit hypothesis and implies RH.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.SquarefreePacketCapacity
open Pareto Pareto.CoefficientStabilization RamanujanCanonicalOptimizer
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.ExhaustiveWalk

abbrev Index (n : ℕ) := {i : Fin n // Squarefree (i.val + 2)}

noncomputable instance indexFintype (n : ℕ) : Fintype (Index n) :=
  Fintype.ofFinite _

def conductor (n : ℕ) (i : Index n) : ℕ := i.val.val + 2

theorem conductor_gt_one (n : ℕ) (i : Index n) : 1 < conductor n i := by
  unfold conductor
  omega

theorem conductor_injective (n : ℕ) : Function.Injective (conductor n) := by
  intro i j h
  apply Subtype.ext
  apply Fin.ext
  change i.val.val + 2 = j.val.val + 2 at h
  omega

def family (n : ℕ) : Index n → ThresholdHilbert :=
  RamanujanBlock.family (conductor n)

theorem family_independent (n : ℕ) : LinearIndependent ℝ (family n) :=
  RamanujanBlock.family_independent (conductor n)
    (conductor_gt_one n) (conductor_injective n)

def source (n : ℕ) : Index n → ℝ :=
  fun i => ArithmeticFunction.vonMangoldt (conductor n i)

theorem source_eq_cross (n : ℕ) : source n = cross (family n) hilbertOne := by
  funext i
  exact (packet_inner_one (conductor n i)).symm

def stage (n : ℕ) : Submodule ℝ ThresholdHilbert := synthesisSpan (family n)

instance stage_finiteDimensional (n : ℕ) : FiniteDimensional ℝ (stage n) :=
  synthesisSpan_finiteDimensional (family n)

def candidate (n : ℕ) : ThresholdHilbert := (stage n).starProjection hilbertOne
def kappa (n : ℕ) : ℝ := ‖candidate n‖ ^ 2

theorem candidate_eq_synthesis (n : ℕ) :
    candidate n = Fintype.linearCombination ℝ (family n)
      (inverseCoeff (family_independent n) hilbertOne) :=
  (synthesis_inverseCoeff_eq_projection (family_independent n) hilbertOne).symm

theorem kappa_eq_inverseGram (n : ℕ) :
    kappa n = dotProduct (source n)
      ((gramMatrix (family n))⁻¹.mulVec (source n)) := by
  rw [source_eq_cross, ← projection_inner_eq_inverseGram (family_independent n)]
  exact (real_inner_self_eq_norm_sq (candidate n)).symm

theorem gram_posDef (n : ℕ) : (gramMatrix (family n)).PosDef :=
  gramMatrix_posDef (family_independent n)

theorem candidate_normal (n : ℕ) (i : Index n) :
    inner ℝ (family n i) (candidate n) = source n i := by
  rw [candidate_eq_synthesis, inverseCoeff_normal, ← source_eq_cross]

theorem error_eq (n : ℕ) :
    ‖hilbertOne - candidate n‖ ^ 2 = 1 - kappa n := by
  have he := residual_schur_value (family_independent n) hilbertOne
  rw [← candidate_eq_synthesis, hilbertOne_norm_sq] at he
  have hk : kappa n = ∑ i, inverseCoeff (family_independent n) hilbertOne i *
      cross (family n) hilbertOne i := by
    unfold kappa
    rw [candidate_eq_synthesis, gram_quadratic]
    apply Finset.sum_congr rfl
    intro i _
    rw [show gram (family n) (inverseCoeff (family_independent n) hilbertOne) i =
      cross (family n) hilbertOne i from inverseCoeff_normal (family_independent n) hilbertOne i]
  rw [hk]
  exact he

theorem stage_monotone : Monotone stage := by
  intro m n hmn
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  refine ⟨⟨⟨i.val.val, lt_of_lt_of_le i.val.isLt hmn⟩, i.property⟩, ?_⟩
  rfl

theorem stage_le_full (n : ℕ) : stage n ≤ finiteSpace n := by
  change stage n ≤ Submodule.span ℝ (Set.range (fun i : Fin n => residueAtom i.val))
  rw [← finitePacket_span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨i.val, rfl⟩

theorem kappa_monotone : Monotone kappa := by
  intro m n hmn
  have he := nested_projection_energy (stage m) (stage n) (stage_monotone hmn) hilbertOne
  change ‖hilbertOne - candidate m‖ ^ 2 =
    ‖hilbertOne - candidate n‖ ^ 2 + ‖candidate n - candidate m‖ ^ 2 at he
  rw [error_eq, error_eq] at he
  linarith [sq_nonneg ‖candidate n - candidate m‖]

theorem kappa_le_full (n : ℕ) : kappa n ≤ packetMass n := by
  have he := nested_projection_energy (stage n) (finiteSpace n) (stage_le_full n) hilbertOne
  change ‖hilbertOne - candidate n‖ ^ 2 =
    ‖hilbertOne - projection n‖ ^ 2 + ‖projection n - candidate n‖ ^ 2 at he
  rw [← packetCandidate_eq_projection, error_eq, packet_error] at he
  linarith [sq_nonneg ‖packetCandidate n - candidate n‖]

theorem kappa_bounds (n : ℕ) : 0 ≤ kappa n ∧ kappa n < 1 :=
  ⟨sq_nonneg _, lt_of_le_of_lt (kappa_le_full n) (packetMass_bounds n).2⟩

theorem kappa_pos (n : ℕ) (hn : 0 < n) : 0 < kappa n := by
  have hne : candidate n ≠ 0 := by
    intro hz
    let i : Index n := ⟨⟨0, hn⟩, by simpa using Nat.prime_two.squarefree⟩
    have h := candidate_normal n i
    rw [hz, inner_zero_right] at h
    have hp : 0 < source n i := by
      change 0 < ArithmeticFunction.vonMangoldt 2
      rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
      exact Real.log_pos (by norm_num)
    linarith
  exact sq_pos_of_pos (norm_pos_iff.mpr hne)

def limitingCapacity : ℝ := sSup (Set.range kappa)

theorem kappa_bddAbove : BddAbove (Set.range kappa) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact (kappa_bounds n).2.le

theorem kappa_le_limit (n : ℕ) : kappa n ≤ limitingCapacity :=
  le_csSup kappa_bddAbove ⟨n, rfl⟩

theorem limitingCapacity_le_one : limitingCapacity ≤ 1 := by
  apply csSup_le (Set.range_nonempty kappa)
  rintro _ ⟨n, rfl⟩
  exact (kappa_bounds n).2.le

theorem limitingCapacity_pos : 0 < limitingCapacity :=
  (kappa_pos 1 (by omega)).trans_le (kappa_le_limit 1)

theorem kappa_tendsto : Tendsto kappa atTop (𝓝 limitingCapacity) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hex : ∃ n, a < kappa n := by
      by_contra! hn
      have hle : limitingCapacity ≤ a := by
        apply csSup_le (Set.range_nonempty kappa)
        rintro _ ⟨n, rfl⟩
        exact hn n
      linarith
    obtain ⟨n, hn⟩ := hex
    exact eventually_atTop.mpr ⟨n, fun m hm => hn.trans_le (kappa_monotone hm)⟩
  · intro b hb
    exact Filter.Eventually.of_forall fun n => (kappa_le_limit n).trans_lt hb

theorem saturation_iff_limit :
    Tendsto kappa atTop (𝓝 1) ↔ limitingCapacity = 1 := by
  constructor
  · intro h
    exact tendsto_nhds_unique kappa_tendsto h
  · intro h
    simpa only [h] using kappa_tendsto

theorem riemannHypothesis_of_saturation
    (h : Tendsto kappa atTop (𝓝 1)) : RiemannHypothesis := by
  apply packet_riemannHypothesis_of_saturation
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le h tendsto_const_nhds
    kappa_le_full (fun n => (packetMass_bounds n).2.le)

/-- Every increase is exactly the squared norm of the new projection component. -/
theorem kappa_increment_exact {m n : ℕ} (hmn : m ≤ n) :
    kappa n - kappa m = ‖candidate n - candidate m‖ ^ 2 := by
  have he := nested_projection_energy (stage m) (stage n) (stage_monotone hmn) hilbertOne
  change ‖hilbertOne - candidate m‖ ^ 2 =
    ‖hilbertOne - candidate n‖ ^ 2 + ‖candidate n - candidate m‖ ^ 2 at he
  rw [error_eq, error_eq] at he
  linarith

/-- A nonsquarefree integer contributes no conductor to this dictionary. -/
theorem stage_succ_eq_of_not_squarefree (n : ℕ) (hns : ¬ Squarefree (n + 2)) :
    stage (n + 1) = stage n := by
  apply le_antisymm
  · apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    have hi : i.val.val < n := by
      have hilt := i.val.isLt
      have hne : i.val.val ≠ n := by
        intro he
        have hs := i.property
        change Squarefree (i.val.val + 2) at hs
        rw [he] at hs
        exact hns hs
      omega
    exact ⟨⟨⟨i.val.val, hi⟩, i.property⟩, rfl⟩
  · exact stage_monotone (Nat.le_succ n)

theorem kappa_succ_eq_of_not_squarefree (n : ℕ) (hns : ¬ Squarefree (n + 2)) :
    kappa (n + 1) = kappa n := by
  simp only [kappa, candidate, stage_succ_eq_of_not_squarefree n hns]

/-- A trial vector in the actual legal stage cannot improve on its projection. -/
theorem legal_error_floor (n : ℕ) (f : ThresholdHilbert) (hf : f ∈ stage n) :
    1 - kappa n ≤ ‖hilbertOne - f‖ ^ 2 := by
  change f ∈ synthesisSpan (family n) at hf
  rw [synthesisSpan, ← Fintype.range_linearCombination] at hf
  obtain ⟨a, rfl⟩ := hf
  have he := residual_completion (family_independent n) hilbertOne a
  rw [← candidate_eq_synthesis, error_eq] at he
  linarith [sq_nonneg ‖Fintype.linearCombination ℝ (family n)
    (a - inverseCoeff (family_independent n) hilbertOne)‖]

/-- The limiting defect is a common lower bound for all finite legal errors. -/
theorem limiting_error_floor (n : ℕ) (f : ThresholdHilbert) (hf : f ∈ stage n) :
    1 - limitingCapacity ≤ ‖hilbertOne - f‖ ^ 2 := by
  have hfinite := legal_error_floor n f hf
  have hlimit := kappa_le_limit n
  linarith

/-- Conversely any verified legal error estimate certifies a capacity lower bound. -/
theorem kappa_lower_of_legal_error (n : ℕ) (f : ThresholdHilbert)
    (hf : f ∈ stage n) (ε : ℝ) (hε : ‖hilbertOne - f‖ ^ 2 ≤ ε) :
    1 - ε ≤ kappa n := by
  linarith [legal_error_floor n f hf]

end RiemannResearch.RH.SquarefreePacketCapacity
