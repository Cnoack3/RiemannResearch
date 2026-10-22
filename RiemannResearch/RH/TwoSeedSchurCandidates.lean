import RiemannResearch.RH.BalancedFiniteTailGram
import RiemannResearch.RH.TwoSeedExactHeadEnergy

/-!
# Finite two-seed candidates from full Schur minimization

Source: user request to combine the Green--Pareto matrix, CLT, and Schur
optimization, 19 September 2026. Independently assembled from the project's
balanced scalar basis and finite Hilbert Gram minimization.

The target parameter is zero for minimum packet energy and one for minimum
error to the constant. Every selected tail index lies beyond the fixed head.
All balanced tail vectors are permitted, including zero-target coefficients.
The inverse uses the full Hilbert Gram matrix, with every mixed term retained.
The existing ParetoPacketGreenGram module identifies these inner products
with the anchored Green matrix plus the genuine infinite Pareto tail.

Feasibility also holds for empirical or rational coefficients. The completion
identity measures their exact excess loss. No CLT, uniform energy bound,
budget-growth estimate, or unconditional approximation theorem is assumed
or proved here.
-/

namespace RiemannResearch.RH.Pareto.TwoSeedSchurCandidates
open RiemannResearch.Analysis
open scoped BigOperators
noncomputable section

/-- Only the physical tail condition is imposed; no support thinning. -/
def TailAfter (N : ℕ) (S : Finset ℕ+) : Prop :=
  ∀ m ∈ S, N < (m : ℕ)

/-- The complete finite inverse-Gram correction to the canonical exact head. -/
def candidate (N : ℕ) (S : Finset ℕ+) (target : ℝ) : ThresholdHilbert :=
  balancedTargetHead N +
    Fintype.linearCombination ℝ (BalancedFiniteTailGram.family S)
      (FiniteHilbertGram.inverseCoeff (BalancedFiniteTailGram.family_independent S)
        (target • hilbertOne - balancedTargetHead N))

/-- Any fixed finite tail coefficients preserve exact-head legality. -/
theorem correctedHead_feasible {N : ℕ} {S : Finset ℕ+}
    (hS : TailAfter N S) (c : S → ℝ) :
    TwoSeedExactHeadEnergy.Feasible N
      (balancedTargetHead N +
        Fintype.linearCombination ℝ (BalancedFiniteTailGram.family S) c) := by
  classical
  constructor
  · apply Submodule.add_mem _
      (BalancedExactHeadEnergy.targetSpan_le_legal
        (balancedTargetHead_mem_nonzeroTargetSpan N))
    rw [Fintype.linearCombination_apply]
    apply Submodule.sum_mem
    intro m _
    apply Submodule.smul_mem
    change hilbertSequence (scalarBalancedHilbert m.val) ∈ legalSeedSpan ({2, 3} : Set ℕ)
    rw [hilbertSequence_scalarBalanced, ← balancedSelected_span_eq_twoSeedSpan]
    exact Submodule.subset_span ⟨m.val, m.val.pos, rfl⟩
  · intro k hk hkN
    have hz : hilbertSequence
        (Fintype.linearCombination ℝ (BalancedFiniteTailGram.family S) c) k = 0 := by
      change hilbertSequenceLinear
        (Fintype.linearCombination ℝ (BalancedFiniteTailGram.family S) c) k = 0
      simp only [Fintype.linearCombination_apply, map_sum, Finset.sum_apply,
        map_smul, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_eq_zero
      intro m _
      change c m * hilbertSequence (scalarBalancedHilbert m.val) k = 0
      have hkm : k < (m.val : ℕ) := lt_of_le_of_lt hkN (hS m.val m.property)
      rw [hilbertSequence_scalarBalanced]
      simp [balancedSelected, dilation, residue, Nat.div_eq_of_lt hkm]
    change hilbertSequenceLinear (balancedTargetHead N +
      Fintype.linearCombination ℝ (BalancedFiniteTailGram.family S) c) k = 1
    rw [map_add]
    change hilbertSequence (balancedTargetHead N) k +
      hilbertSequence (Fintype.linearCombination ℝ (BalancedFiniteTailGram.family S) c) k = 1
    rw [balancedTargetHead_exact N k hk hkN, hz, add_zero]

theorem candidate_feasible {N : ℕ} {S : Finset ℕ+}
    (hS : TailAfter N S) (target : ℝ) :
    TwoSeedExactHeadEnergy.Feasible N (candidate N S target) :=
  correctedHead_feasible hS _

/-- Exact signed Schur value for either target, with the full infinite norm. -/
theorem candidate_error_sq (N : ℕ) (S : Finset ℕ+) (target : ℝ) :
    ‖target • hilbertOne - candidate N S target‖ ^ 2 =
      ‖target • hilbertOne - balancedTargetHead N‖ ^ 2 -
      ∑ i : S,
        FiniteHilbertGram.inverseCoeff (BalancedFiniteTailGram.family_independent S)
          (target • hilbertOne - balancedTargetHead N) i *
        FiniteHilbertGram.cross (BalancedFiniteTailGram.family S)
          (target • hilbertOne - balancedTargetHead N) i := by
  have he : target • hilbertOne - candidate N S target =
      (target • hilbertOne - balancedTargetHead N) -
        Fintype.linearCombination ℝ (BalancedFiniteTailGram.family S)
          (FiniteHilbertGram.inverseCoeff (BalancedFiniteTailGram.family_independent S)
            (target • hilbertOne - balancedTargetHead N)) := by
    unfold candidate
    abel
  rw [he]
  exact FiniteHilbertGram.residual_schur_value
    (BalancedFiniteTailGram.family_independent S) _

/-- Exact excess loss for arbitrary coefficients, including sampled fits. -/
theorem candidate_completion (N : ℕ) (S : Finset ℕ+) (target : ℝ) (c : S → ℝ) :
    ‖target • hilbertOne - (balancedTargetHead N +
        Fintype.linearCombination ℝ (BalancedFiniteTailGram.family S) c)‖ ^ 2 =
      ‖target • hilbertOne - candidate N S target‖ ^ 2 +
      ‖Fintype.linearCombination ℝ (BalancedFiniteTailGram.family S)
        (c - FiniteHilbertGram.inverseCoeff (BalancedFiniteTailGram.family_independent S)
          (target • hilbertOne - balancedTargetHead N))‖ ^ 2 := by
  simpa only [candidate, sub_add_eq_sub_sub] using
    FiniteHilbertGram.residual_completion (BalancedFiniteTailGram.family_independent S)
      (target • hilbertOne - balancedTargetHead N) c

/-- Unconditional optimality within the selected finite affine tail space. -/
theorem candidate_minimizes (N : ℕ) (S : Finset ℕ+) (target : ℝ) (c : S → ℝ) :
    ‖target • hilbertOne - candidate N S target‖ ^ 2 ≤
      ‖target • hilbertOne - (balancedTargetHead N +
        Fintype.linearCombination ℝ (BalancedFiniteTailGram.family S) c)‖ ^ 2 := by
  rw [candidate_completion]
  exact le_add_of_nonneg_right (sq_nonneg _)

end
end RiemannResearch.RH.Pareto.TwoSeedSchurCandidates
