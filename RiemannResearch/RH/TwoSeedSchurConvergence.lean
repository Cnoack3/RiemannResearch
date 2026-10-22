import RiemannResearch.RH.TwoSeedSchurCandidates
import RiemannResearch.RH.FiniteTwoSeedHeadRepair
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.RH.ThresholdRiemannHypothesis

/-!
# Limits of the actual two-seed Schur regressions

Source: independently assembled for the user's CRT and regression-uniqueness
request, 19 September 2026. The proof uses the full Gram normal equations,
orthogonal projection uniqueness, and Mathlib's monotone projection limit.
No novelty claim is made.

Established unconditionally: unique finite coefficients, exact nested energy
drops, and norm convergence for every fixed head along a growing dictionary.
The limit is the affine projection onto the closed union of tail spans.
Convergence to one is equivalent to membership of the target residual in that
closed union; uniqueness does not prove this membership.

The last theorem shows that existence of a norm limit for the candidates with
a growing exact head would already imply RH. That existence remains OPEN.
-/

open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.TwoSeedSchurCandidates
open RiemannResearch.Analysis
open FiniteTwoSeedCompletion
noncomputable section
set_option backward.isDefEq.respectTransparency false

def tailSpan (S : Finset ℕ+) : Submodule ℝ ThresholdHilbert :=
  FiniteHilbertGram.synthesisSpan (BalancedFiniteTailGram.family S)

instance tailSpan_finiteDimensional (S : Finset ℕ+) :
    FiniteDimensional ℝ (tailSpan S) := by
  unfold tailSpan
  infer_instance

theorem tailSpan_mono {S T : Finset ℕ+} (hST : S ⊆ T) : tailSpan S ≤ tailSpan T := by
  apply Submodule.span_mono
  rintro _ ⟨m, rfl⟩
  exact ⟨⟨m.val, hST m.property⟩, rfl⟩

theorem candidate_eq_projection (N : ℕ) (S : Finset ℕ+) (target : ℝ) :
    candidate N S target = balancedTargetHead N +
      (tailSpan S).starProjection (target • hilbertOne - balancedTargetHead N) := by
  unfold candidate tailSpan
  rw [FiniteHilbertGram.synthesis_inverseCoeff_eq_projection]

/-- Equality of full losses forces equality of all regression coefficients. -/
theorem candidate_coefficients_unique (N : ℕ) (S : Finset ℕ+) (target : ℝ)
    (c : S → ℝ)
    (hc : ‖target • hilbertOne - (balancedTargetHead N +
      Fintype.linearCombination ℝ (BalancedFiniteTailGram.family S) c)‖ ^ 2 =
      ‖target • hilbertOne - candidate N S target‖ ^ 2) :
    c = FiniteHilbertGram.inverseCoeff (BalancedFiniteTailGram.family_independent S)
      (target • hilbertOne - balancedTargetHead N) := by
  apply FiniteHilbertGram.residual_minimizer_unique
    (BalancedFiniteTailGram.family_independent S) _ c
  simpa only [sub_add_eq_sub_sub] using hc.trans (candidate_error_sq N S target)

/-- The same prescribed head is used on both sides. -/
theorem candidate_nested_error (N : ℕ) (target : ℝ)
    {S T : Finset ℕ+} (hST : S ⊆ T) :
    ‖target • hilbertOne - candidate N S target‖ ^ 2 =
      ‖target • hilbertOne - candidate N T target‖ ^ 2 +
        ‖candidate N T target - candidate N S target‖ ^ 2 := by
  simp only [candidate_eq_projection, sub_add_eq_sub_sub, add_sub_cancel_left]
  exact ExhaustiveWalk.nested_projection_energy _ _ (tailSpan_mono hST) _

def tailClosure (S : ℕ → Finset ℕ+) : Submodule ℝ ThresholdHilbert :=
  (⨆ M, tailSpan (S M)).topologicalClosure

instance tailClosure_hasOrthogonalProjection (S : ℕ → Finset ℕ+) :
    (tailClosure S).HasOrthogonalProjection := by
  unfold tailClosure
  infer_instance

def limitCandidate (N : ℕ) (S : ℕ → Finset ℕ+) (target : ℝ) : ThresholdHilbert :=
  balancedTargetHead N +
    (tailClosure S).starProjection (target • hilbertOne - balancedTargetHead N)

/-- A fixed-head regression converges strongly; no density hypothesis is used. -/
theorem candidate_tendsto_fixed_head (N : ℕ) (S : ℕ → Finset ℕ+)
    (hS : Monotone S) (target : ℝ) :
    Tendsto (fun M => candidate N (S M) target) atTop
      (𝓝 (limitCandidate N S target)) := by
  have ht := Submodule.starProjection_tendsto_closure_iSup
    (fun M => tailSpan (S M)) (fun m n hmn => tailSpan_mono (hS hmn))
    (target • hilbertOne - balancedTargetHead N)
  simpa only [candidate_eq_projection, limitCandidate, tailClosure] using
    (tendsto_const_nhds (x := balancedTargetHead N)).add ht

theorem candidate_error_tendsto_fixed_head (N : ℕ) (S : ℕ → Finset ℕ+)
    (hS : Monotone S) (target : ℝ) :
    Tendsto (fun M => ‖target • hilbertOne - candidate N (S M) target‖ ^ 2)
      atTop (𝓝 (‖target • hilbertOne - limitCandidate N S target‖ ^ 2)) :=
  (tendsto_const_nhds.sub (candidate_tendsto_fixed_head N S hS target)).norm.pow 2

/-- Exact remaining condition, not a consequence of the finite normal equations. -/
theorem candidate_tendsto_one_iff (N : ℕ) (S : ℕ → Finset ℕ+)
    (hS : Monotone S) :
    Tendsto (fun M => candidate N (S M) 1) atTop (𝓝 hilbertOne) ↔
      hilbertOne - balancedTargetHead N ∈ tailClosure S := by
  have ht := candidate_tendsto_fixed_head N S hS 1
  constructor
  · intro h
    have he := tendsto_nhds_unique ht h
    have hp : (tailClosure S).starProjection
        (hilbertOne - balancedTargetHead N) = hilbertOne - balancedTargetHead N := by
      have he' : balancedTargetHead N + (tailClosure S).starProjection
          (hilbertOne - balancedTargetHead N) = hilbertOne := by
        simpa only [limitCandidate, one_smul] using he
      calc
        _ = (balancedTargetHead N + (tailClosure S).starProjection
          (hilbertOne - balancedTargetHead N)) - balancedTargetHead N := by abel
        _ = _ := by rw [he']
    exact Submodule.starProjection_eq_self_iff.mp hp
  · intro h
    have hp := Submodule.starProjection_eq_self_iff.mpr h
    have he : limitCandidate N S 1 = hilbertOne := by
      simp only [limitCandidate, one_smul, hp]
      abel
    simpa only [he] using ht

/-- The literal finite set {N+1, ..., N+M}. -/
def tailIndices (N M : ℕ) : Finset ℕ+ :=
  (Finset.range M).image (fun j => (⟨N+j+1, by omega⟩ : ℕ+))

theorem tailIndices_after (N M : ℕ) : TailAfter N (tailIndices N M) := by
  intro m hm
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm
  change N < N+j+1
  omega

theorem tailIndices_mono (N : ℕ) : Monotone (tailIndices N) := by
  intro M K hMK
  exact Finset.image_subset_image (Finset.range_mono hMK)

theorem mem_tailIndices {N M : ℕ} {m : ℕ+} :
    m ∈ tailIndices N M ↔ N < (m : ℕ) ∧ (m : ℕ) ≤ N+M := by
  constructor
  · intro hm
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hm
    have hjM := Finset.mem_range.mp hj
    change N < N+j+1 ∧ N+j+1 ≤ N+M
    omega
  · rintro ⟨hmN, hmM⟩
    apply Finset.mem_image.mpr
    refine ⟨(m : ℕ)-N-1, Finset.mem_range.mpr (by omega), ?_⟩
    apply Subtype.ext
    change N+((m : ℕ)-N-1)+1 = (m : ℕ)
    omega

def allTailSpan (N : ℕ) : Submodule ℝ ThresholdHilbert :=
  Submodule.span ℝ {f | ∃ m : ℕ+, N < (m : ℕ) ∧ f = scalarBalancedHilbert m}

/-- Every balanced index beyond the head occurs in the growing finite dictionary. -/
theorem iSup_tailSpan_interval (N : ℕ) :
    (⨆ M, tailSpan (tailIndices N M)) = allTailSpan N := by
  apply le_antisymm
  · apply iSup_le
    intro M
    apply Submodule.span_le.mpr
    rintro _ ⟨m, rfl⟩
    exact Submodule.subset_span
      ⟨m.val, (mem_tailIndices.mp m.property).1, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨m, hm, rfl⟩
    apply (le_iSup (fun M => tailSpan (tailIndices N M)) (m : ℕ))
    apply Submodule.subset_span
    exact ⟨⟨m, mem_tailIndices.mpr ⟨hm, by omega⟩⟩, rfl⟩

theorem tailClosure_interval (N : ℕ) :
    tailClosure (tailIndices N) = (allTailSpan N).topologicalClosure := by
  rw [tailClosure, iSup_tailSpan_interval]

theorem candidate_interval_tendsto (N : ℕ) (target : ℝ) :
    Tendsto (fun M => candidate N (tailIndices N M) target) atTop
      (𝓝 (limitCandidate N (tailIndices N) target)) :=
  candidate_tendsto_fixed_head N (tailIndices N) (tailIndices_mono N) target

/-- A norm limit of any exact growing-head candidates must equal one. -/
theorem diagonal_limit_eq_one (S : ℕ → Finset ℕ+)
    (hS : ∀ N, TailAfter N (S N)) (target : ℝ) {f : ThresholdHilbert}
    (hf : Tendsto (fun N => candidate N (S N) target) atTop (𝓝 f)) :
    f = hilbertOne := by
  have hcoord (k : ℕ) : physicalEvaluation k f = 1 := by
    have ht := ((physicalEvaluation k).continuous.tendsto f).comp hf
    have he : (fun N => physicalEvaluation k (candidate N (S N) target)) =ᶠ[atTop]
        (fun _ => (1 : ℝ)) := by
      filter_upwards [eventually_ge_atTop (k+1)] with N hN
      simpa only [physicalEvaluation_apply] using
        (candidate_feasible (hS N) target).2 (k+1) (by omega) hN
    exact tendsto_nhds_unique ht (tendsto_const_nhds.congr' he.symm)
  apply hilbertSequence_injective
  funext k
  cases k with
  | zero => simp
  | succ k =>
      rw [← physicalEvaluation_apply, hcoord, hilbertOne_sequence]
      simp [zeroAnchor]

/-- CONDITIONAL RESEARCH REDUCTION: existence of this norm limit is OPEN. -/
theorem riemannHypothesis_of_diagonal_limit (S : ℕ → Finset ℕ+)
    (hS : ∀ N, TailAfter N (S N)) (target : ℝ) {f : ThresholdHilbert}
    (hf : Tendsto (fun N => candidate N (S N) target) atTop (𝓝 f)) :
    RiemannHypothesis := by
  have he := diagonal_limit_eq_one S hS target hf
  apply riemannHypothesis_of_twoSeed_closure
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto
    (by simpa only [he] using hf)
  exact Eventually.of_forall (fun N => (hilbertLegalSubspace ({2,3} : Set ℕ)).le_topologicalClosure
    (candidate_feasible (hS N) target).1)

end
end RiemannResearch.RH.Pareto.TwoSeedSchurCandidates
