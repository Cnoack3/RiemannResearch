import RiemannResearch.Analysis.FiniteHilbertGram
import RiemannResearch.RH.BalancedExactHeadEnergy

/-!
# Exact signed tail optimization for the minimal-support RH criterion

Source: `RH_Minimal_Seeds_Continuation_20260916.md`, Section 13, equations
(13.7)–(13.8). Every finite tail uses actual balanced Hilbert vectors and their
full signed Gram matrix. Invertibility follows from the established continuous
biorthogonal coordinates. The uniform gain estimate remains an explicit,
unproved hypothesis of the final reduction to Mathlib's Riemann Hypothesis.
-/

namespace RiemannResearch.RH.Pareto.BalancedFiniteTailGram
open scoped BigOperators
open RiemannResearch.Analysis
noncomputable section

/-- Actual Hilbert vectors indexed by a finite set of positive integers. -/
def family (S : Finset ℕ+) (m : S) : ThresholdHilbert := scalarBalancedHilbert m.val

theorem family_independent (S : Finset ℕ+) : LinearIndependent ℝ (family S) :=
  scalarBalancedHilbert_linearIndependent.comp _ Subtype.val_injective

/-- All selected vectors are permitted by the nonzero-target support and begin
strictly after the prescribed head. -/
def SupportedTail (N : ℕ) (S : Finset ℕ+) : Prop :=
  ∀ m ∈ S, N < (m : ℕ) ∧ scalarBalancedIndex m ∈ balancedNonzeroTargetSupport

/-- Exact inverse-Gram improvement, including all mixed terms. -/
def gain (N : ℕ) (S : Finset ℕ+) : ℝ :=
  ∑ m : S, FiniteHilbertGram.inverseCoeff (family_independent S) (balancedTargetHead N) m *
    FiniteHilbertGram.cross (family S) (balancedTargetHead N) m

/-- Simultaneous optimal additive correction; no sequential projection is used. -/
def optimizedHead (N : ℕ) (S : Finset ℕ+) : ThresholdHilbert :=
  balancedTargetHead N + Fintype.linearCombination ℝ (family S)
    (-FiniteHilbertGram.inverseCoeff (family_independent S) (balancedTargetHead N))

theorem optimizedHead_norm_sq (N : ℕ) (S : Finset ℕ+) :
    ‖optimizedHead N S‖ ^ 2 = ‖balancedTargetHead N‖ ^ 2 - gain N S :=
  FiniteHilbertGram.additive_inverse_schur_value (family_independent S) (balancedTargetHead N)

private theorem scalar_zero_before (m : ℕ+) (k : ℕ) (hkm : k < (m : ℕ)) :
    hilbertSequence (scalarBalancedHilbert m) k = 0 := by
  rw [hilbertSequence_scalarBalanced]
  simp [balancedSelected, dilation, residue, Nat.div_eq_of_lt hkm]

/-- Every signed correction in a supported tail preserves feasibility. -/
theorem correctedHead_feasible {N : ℕ} {S : Finset ℕ+} (hS : SupportedTail N S)
    (c : S → ℝ) :
    BalancedExactHeadEnergy.Feasible N
      (balancedTargetHead N + Fintype.linearCombination ℝ (family S) c) := by
  classical
  constructor
  · apply Submodule.add_mem _ (balancedTargetHead_mem_nonzeroTargetSpan N)
    rw [Fintype.linearCombination_apply]
    apply Submodule.sum_mem
    intro m _
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨scalarBalancedIndex m.val, (hS m.val m.property).2, rfl⟩
  · intro k hk hkN
    have hz : hilbertSequence (Fintype.linearCombination ℝ (family S) c) k = 0 := by
      change hilbertSequenceLinear (Fintype.linearCombination ℝ (family S) c) k = 0
      simp only [Fintype.linearCombination_apply, map_sum, Finset.sum_apply,
        map_smul, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_eq_zero
      intro m _
      change c m * hilbertSequence (scalarBalancedHilbert m.val) k = 0
      rw [scalar_zero_before m.val k (lt_of_le_of_lt hkN (hS m.val m.property).1), mul_zero]
    change hilbertSequenceLinear
      (balancedTargetHead N + Fintype.linearCombination ℝ (family S) c) k = 1
    rw [map_add]
    change hilbertSequence (balancedTargetHead N) k +
      hilbertSequence (Fintype.linearCombination ℝ (family S) c) k = 1
    rw [balancedTargetHead_exact N k hk hkN, hz, add_zero]

theorem optimizedHead_feasible {N : ℕ} {S : Finset ℕ+} (hS : SupportedTail N S) :
    BalancedExactHeadEnergy.Feasible N (optimizedHead N S) :=
  correctedHead_feasible hS _

/-- A concrete finite inverse-Gram calculation bounds the unrestricted optimum. -/
theorem energy_le_schur_value {N : ℕ} {S : Finset ℕ+} (hS : SupportedTail N S) :
    BalancedExactHeadEnergy.energy N ≤ ‖balancedTargetHead N‖ ^ 2 - gain N S := by
  rw [← optimizedHead_norm_sq]
  exact BalancedExactHeadEnergy.energy_le (optimizedHead_feasible hS)

/-- CONDITIONAL RESEARCH REDUCTION: the estimate supplied in `hC` is open.
Proving it for actual finite supported tails would prove Riemann Hypothesis. -/
theorem riemannHypothesis_of_uniform_tail_gain (C : ℝ)
    (hC : ∀ N : ℕ, ∃ S : Finset ℕ+, SupportedTail N S ∧
      ‖balancedTargetHead N‖ ^ 2 - gain N S ≤ C) : RiemannHypothesis := by
  apply BalancedExactHeadEnergy.riemannHypothesis_of_energy_bddAbove
  refine ⟨C, ?_⟩
  rintro e ⟨N, rfl⟩
  obtain ⟨S, hS, hbound⟩ := hC N
  exact (energy_le_schur_value hS).trans hbound

/-!
## Exhausting all finite supported tails

Source: user-provided
`RH_Minimal_Seeds_Canonical_Basis_and_Arithmetic_Charge_20260914 (1)(1).md`,
Sections 12 and 16, especially (12.4), (16.6), and (16.8). The source supports
the statements and proof strategy. The cofinal RH reduction also uses the
existing actual two-seed Mellin obstruction. No arithmetic upper bound,
support-thinning theorem, or unconditional RH proof is asserted.
-/

section TailExhaustion
set_option backward.isDefEq.respectTransparency false

private theorem scalarIndex_of_value (i : BalancedArithmeticIndex) :
    scalarBalancedIndex ⟨balancedIndexValue i, balancedIndexValue_pos i⟩ = i := by
  apply balancedIndexHilbert_linearIndependent.injective
  apply hilbertSequence_injective
  change hilbertSequence (scalarBalancedHilbert _) = _
  rw [hilbertSequence_scalarBalanced, hilbertSequence_balancedIndex]
  exact balancedSelected_eq_rough i.u i.a i.b i.rough

private theorem scalar_targetSpan :
    BalancedExactHeadEnergy.targetSpan =
      Submodule.span ℝ (scalarBalancedHilbert ''
        {m | scalarBalancedIndex m ∈ balancedNonzeroTargetSupport}) := by
  change Submodule.span ℝ _ = Submodule.span ℝ _
  congr 1
  ext f
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨⟨balancedIndexValue i, balancedIndexValue_pos i⟩, ?_, ?_⟩
    · change scalarBalancedIndex (⟨balancedIndexValue i, balancedIndexValue_pos i⟩ : ℕ+) ∈ balancedNonzeroTargetSupport
      rw [scalarIndex_of_value]
      exact hi
    · simp only [scalarBalancedHilbert, scalarIndex_of_value]
  · rintro ⟨m, hm, rfl⟩
    exact ⟨scalarBalancedIndex m, hm, rfl⟩

private theorem coordinate_synthesis (c : ℕ+ →₀ ℝ) (m : ℕ+) :
    scalarBalancedCoefficient m
      (Finsupp.linearCombination ℝ scalarBalancedHilbert c) = c m := by
  classical
  simp [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul,
    scalarBalancedCoefficient_biorthogonal]
  tauto


/-- Every feasible packet is the fixed canonical head plus a finite supported tail. -/
theorem feasible_tail_representation {N : ℕ} {f : ThresholdHilbert}
    (hf : BalancedExactHeadEnergy.Feasible N f) :
    ∃ S : Finset ℕ+, SupportedTail N S ∧ ∃ c : S → ℝ,
      f = balancedTargetHead N + Fintype.linearCombination ℝ (family S) c := by
  classical
  let g := f - balancedTargetHead N
  have hg : g ∈ BalancedExactHeadEnergy.targetSpan :=
    Submodule.sub_mem _ hf.1 (balancedTargetHead_mem_nonzeroTargetSpan N)
  rw [scalar_targetSpan] at hg
  obtain ⟨c, hc, hcg⟩ := (Finsupp.mem_span_image_iff_linearCombination ℝ).mp hg
  have hS : SupportedTail N c.support := by
    intro m hm
    refine ⟨?_, (Finsupp.mem_supported ℝ c).mp hc hm⟩
    by_contra hnot
    have hmN : (m : ℕ) ≤ N := by omega
    have hzero : scalarBalancedCoefficient m g = 0 := by
      have he := scalarBalancedCoefficient_congr_head m g 0 (by
        intro k hk hkm
        change hilbertSequenceLinear (f - balancedTargetHead N) k =
          hilbertSequenceLinear 0 k
        rw [map_sub, map_zero]
        change hilbertSequence f k - hilbertSequence (balancedTargetHead N) k = 0
        rw [hf.2 k hk (hkm.trans hmN), balancedTargetHead_exact N k hk (hkm.trans hmN)]
        ring)
      simpa only [map_zero] using he
    have hcm : c m = 0 := by
      rw [← hcg, coordinate_synthesis] at hzero
      exact hzero
    exact (Finsupp.mem_support_iff.mp hm) hcm
  refine ⟨c.support, hS, fun m => c m.val, ?_⟩
  have hs : Fintype.linearCombination ℝ (family c.support) (fun m => c m.val) = g := by
    rw [← hcg]
    simp [Fintype.linearCombination_apply, family, Finsupp.linearCombination_apply,
      Finsupp.sum]
    exact Finset.sum_attach c.support (fun m => c m • scalarBalancedHilbert m)
  rw [hs]
  dsimp [g]
  abel

theorem exists_schur_le_feasible {N : ℕ} {f : ThresholdHilbert}
    (hf : BalancedExactHeadEnergy.Feasible N f) :
    ∃ S : Finset ℕ+, SupportedTail N S ∧
      ‖balancedTargetHead N‖ ^ 2 - gain N S ≤ ‖f‖ ^ 2 := by
  obtain ⟨S, hS, c, he⟩ := feasible_tail_representation hf
  refine ⟨S, hS, ?_⟩
  rw [he, ← optimizedHead_norm_sq]
  exact FiniteHilbertGram.additive_minimizes (family_independent S) _ c


/-- Each unrestricted optimum is approached by actual finite inverse-Gram optimizers. -/
theorem exists_schur_near_minimizer (N : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ S : Finset ℕ+, SupportedTail N S ∧
      ‖balancedTargetHead N‖ ^ 2 - gain N S <
        BalancedExactHeadEnergy.energy N + ε := by
  obtain ⟨f, hf, he⟩ := BalancedExactHeadEnergy.exists_near_minimizer N hε
  obtain ⟨S, hS, hle⟩ := exists_schur_le_feasible hf
  exact ⟨S, hS, hle.trans_lt he⟩

/-- The full signed Schur values over all finite permitted tails. -/
def schurValues (N : ℕ) : Set ℝ :=
  {e | ∃ S : Finset ℕ+, SupportedTail N S ∧
    ‖balancedTargetHead N‖ ^ 2 - gain N S = e}

theorem schurValues_nonempty (N : ℕ) : (schurValues N).Nonempty :=
  ⟨_, ∅, by simp [SupportedTail], rfl⟩

theorem schurValues_bddBelow (N : ℕ) : BddBelow (schurValues N) := by
  refine ⟨BalancedExactHeadEnergy.energy N, ?_⟩
  rintro e ⟨S, hS, rfl⟩
  exact energy_le_schur_value hS

/-- Exact equality, not only an upper bound from one chosen tail family. -/
theorem energy_eq_sInf_schurValues (N : ℕ) :
    BalancedExactHeadEnergy.energy N = sInf (schurValues N) := by
  apply le_antisymm
  · apply le_csInf (schurValues_nonempty N)
    rintro e ⟨S, hS, rfl⟩
    exact energy_le_schur_value hS
  · apply BalancedExactHeadEnergy.le_energy
    intro f hf
    obtain ⟨S, hS, hle⟩ := exists_schur_le_feasible hf
    exact (csInf_le (schurValues_bddBelow N) ⟨S, hS, rfl⟩).trans hle

/-- Synthesis is equivalent to finite tail gains approaching the unit-energy threshold
for every fixed head. Neither side is asserted without this equivalence's hypothesis. -/
theorem closure_iff_near_unit_schur :
    hilbertOne ∈ BalancedExactHeadEnergy.targetSpan.topologicalClosure ↔
      ∀ N : ℕ, ∀ ε : ℝ, 0 < ε →
        ∃ S : Finset ℕ+, SupportedTail N S ∧
          ‖balancedTargetHead N‖ ^ 2 - gain N S < 1 + ε := by
  constructor
  · intro h N ε hε
    obtain ⟨S, hS, hlt⟩ := exists_schur_near_minimizer N hε
    exact ⟨S, hS, hlt.trans_le (add_le_add
      (BalancedExactHeadEnergy.energy_le_one_of_closure h N) le_rfl)⟩
  · intro h
    apply BalancedExactHeadEnergy.hilbertOne_mem_closure_of_energy_bddAbove
    refine ⟨2, ?_⟩
    rintro e ⟨N, rfl⟩
    obtain ⟨S, hS, hlt⟩ := h N 1 (by norm_num)
    have he := energy_le_schur_value hS
    linarith

/-- The larger two-seed family can only have smaller optimal energy. -/
theorem twoSeed_energy_le (N : ℕ) :
    TwoSeedExactHeadEnergy.energy N ≤ BalancedExactHeadEnergy.energy N := by
  apply BalancedExactHeadEnergy.le_energy
  intro f hf
  exact TwoSeedExactHeadEnergy.energy_le
    ⟨BalancedExactHeadEnergy.targetSpan_le_legal hf.1, hf.2⟩

/-- An off-line zero forces growth of every retained-family optimum, with no
restriction on how distant or numerous its finite corrections may be. -/
theorem energy_power_lower_of_zeta
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) {N : ℕ} (hN : 3 ≤ N) :
    ((2 * s.re - 1) / (4 * ‖s‖ ^ 2)) *
      ((N : ℝ) + 1) ^ (2 * s.re - 1) ≤ BalancedExactHeadEnergy.energy N :=
  (TwoSeedExactHeadEnergy.energy_power_lower_of_zeta s hs hs1 hz hN).trans
    (twoSeed_energy_le N)

/-- CONDITIONAL RESEARCH REDUCTION: the cofinal subpower estimate is open.
Every positive exponent may use a different cofinal sequence of head lengths. -/
theorem riemannHypothesis_of_cofinal_subpower_energy
    (hsub : ∀ p : ℝ, 0 < p → ∃ C : ℝ, ∀ N₀ : ℕ,
      ∃ N : ℕ, N₀ ≤ N ∧
        BalancedExactHeadEnergy.energy N ≤ C * ((N : ℝ) + 1) ^ p) :
    RiemannHypothesis := by
  apply TwoSeedExactHeadEnergy.riemannHypothesis_of_cofinal_subpower
  intro p hp
  obtain ⟨C, hC⟩ := hsub p hp
  refine ⟨C, fun N₀ => ?_⟩
  obtain ⟨N, hN, he⟩ := hC N₀
  exact ⟨N, hN, (twoSeed_energy_le N).trans he⟩

/-- CONDITIONAL RESEARCH REDUCTION: unlike the older uniform-gain criterion,
cofinal subpower control already suffices for actual Mathlib RH. The bound is not proved. -/
theorem riemannHypothesis_of_cofinal_subpower_tail_gain
    (hsub : ∀ p : ℝ, 0 < p → ∃ C : ℝ, ∀ N₀ : ℕ,
      ∃ N : ℕ, N₀ ≤ N ∧ ∃ S : Finset ℕ+, SupportedTail N S ∧
        ‖balancedTargetHead N‖ ^ 2 - gain N S ≤ C * ((N : ℝ) + 1) ^ p) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_subpower_energy
  intro p hp
  obtain ⟨C, hC⟩ := hsub p hp
  refine ⟨C, fun N₀ => ?_⟩
  obtain ⟨N, hN, S, hS, he⟩ := hC N₀
  exact ⟨N, hN, (energy_le_schur_value hS).trans he⟩

end TailExhaustion

end
end RiemannResearch.RH.Pareto.BalancedFiniteTailGram
