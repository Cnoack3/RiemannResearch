import RiemannResearch.RH.BalancedScalarBasis
import RiemannResearch.RH.BalancedMinimalTarget
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp

/-!
# Exact head interpolation by the balanced nonzero-target dictionary

Source: user-provided argument, RH_Minimal_Seeds_Continuation_20260916.md,
Section 10, Theorem 10.1. The existing continuous Möbius cut coordinates are used
without assuming any bound on their norms or on the interpolation operators.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
open RiemannResearch.LinearAlgebra
open RiemannResearch.Analysis
open RiemannResearch.RH.FiniteSeedComponentCharge
noncomputable section

/-- Every vertex in the finite cut is at most its root. -/
theorem balancedArithmeticCut_le (u a b n : ℕ)
    (hn : n ∈ balancedArithmeticCut u a b) : n ≤ 2 ^ a * 3 ^ b * u := by
  obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hi, hj, _, _⟩ := (mem_balancedGridCut a b i j).mp hij
  gcongr <;> norm_num

/-- The arithmetic coefficient at `m` depends only on the first `m` coordinates. -/
theorem scalarBalancedCoefficient_congr_head (m : ℕ+) (f g : ThresholdHilbert)
    (hfg : ∀ n, 0 < n → n ≤ (m : ℕ) → hilbertSequence f n = hilbertSequence g n) :
    scalarBalancedCoefficient m f = scalarBalancedCoefficient m g := by
  let i := scalarBalancedIndex m
  have hS : ∀ n ∈ balancedArithmeticCut i.u i.a i.b,
      0 < n ∧ n ≤ (m : ℕ) := by
    intro n hn
    refine ⟨balancedArithmeticCut_pos _ _ _ i.rough n hn, ?_⟩
    have hnle := balancedArithmeticCut_le i.u i.a i.b n hn
    change n ≤ balancedIndexValue i at hnle
    simpa only [i, scalarBalancedIndex_value] using hnle
  change balancedCoefficientCLM i f = balancedCoefficientCLM i g
  rw [balancedCoefficientCLM_apply, balancedCoefficientCLM_apply,
    componentCharge_eq_row _ m hS _ (by simp),
    componentCharge_eq_row _ m hS _ (by simp)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hfg (k + 1) (by omega) (by have := Finset.mem_range.mp hk; omega)]

private def headIndex (k : ℕ) : ℕ+ := ⟨k + 1, Nat.succ_pos k⟩

private theorem headIndex_injective : Function.Injective headIndex := by
  intro k l h
  have he := congrArg (fun m : ℕ+ => (m : ℕ)) h
  change k + 1 = l + 1 at he
  omega

private def headVector (k : ℕ) : ThresholdHilbert := scalarBalancedHilbert (headIndex k)
private def headCoefficient (k : ℕ) : ThresholdHilbert →L[ℝ] ℝ :=
  scalarBalancedCoefficient (headIndex k)

private theorem head_biorthogonal (k l : ℕ) :
    headCoefficient k (headVector l) = if k = l then 1 else 0 := by
  rw [headCoefficient, headVector, scalarBalancedCoefficient_biorthogonal]
  simp only [headIndex_injective.eq_iff]

private theorem headVector_zero_of_lt (k n : ℕ) (hn : n < k + 1) :
    hilbertSequence (headVector k) n = 0 := by
  rw [headVector, hilbertSequence_scalarBalanced]
  simp [balancedSelected, dilation, residue, headIndex, Nat.div_eq_of_lt hn]

private theorem headVector_diagonal (k : ℕ) :
    hilbertSequence (headVector k) (k + 1) = (k + 1 : ℕ) := by
  rw [headVector, hilbertSequence_scalarBalanced]
  have hp : 1 < balancedSelectedSeed (k + 1) := by
    unfold balancedSelectedSeed
    split_ifs <;> omega
  simp [balancedSelected, dilation, residue, headIndex,
    Nat.div_self (Nat.succ_pos k), Nat.mod_eq_of_lt hp]

/-- Finite natural head of the literal scalar-index dictionary. -/
def balancedHeadSpan (N : ℕ) : Submodule ℝ ThresholdHilbert :=
  Submodule.span ℝ {v | ∃ k : ℕ, k < N ∧ v = headVector k}

private theorem balancedHeadSpan_mono {N M : ℕ} (hNM : N ≤ M) :
    balancedHeadSpan N ≤ balancedHeadSpan M := by
  apply Submodule.span_mono
  rintro v ⟨k, hk, rfl⟩
  exact ⟨k, lt_of_lt_of_le hk hNM, rfl⟩

/-- Every finite positive-coordinate head can be interpolated in its triangular span. -/
theorem exists_balancedHead_interpolant (N : ℕ) (f : ThresholdHilbert) :
    ∃ g ∈ balancedHeadSpan N,
      ∀ n, 0 < n → n ≤ N → hilbertSequence g n = hilbertSequence f n := by
  induction N with
  | zero =>
      exact ⟨0, Submodule.zero_mem _, by intro n hn hnN; omega⟩
  | succ N ih =>
      obtain ⟨g, hg, hhead⟩ := ih
      let c : ℝ := (hilbertSequence f (N + 1) - hilbertSequence g (N + 1)) /
        (N + 1 : ℕ)
      refine ⟨g + c • headVector N,
        Submodule.add_mem _ (balancedHeadSpan_mono (Nat.le_succ N) hg)
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨N, by omega, rfl⟩)), ?_⟩
      intro n hn hnN
      change hilbertSequenceLinear (g + c • headVector N) n = _
      simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      change hilbertSequence g n + c * hilbertSequence (headVector N) n = hilbertSequence f n
      by_cases he : n = N + 1
      · subst n
        rw [headVector_diagonal]
        have hne : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
        dsimp [c]
        field_simp
        ring
      · rw [headVector_zero_of_lt N n (by omega), mul_zero, add_zero]
        exact hhead n hn (by omega)

/-- The canonical finite coefficient projection, using the actual Möbius-cut CLMs. -/
def balancedHeadProjection (N : ℕ) : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  ∑ k ∈ Finset.range N, (headCoefficient k).smulRight (headVector k)

theorem balancedHeadProjection_apply (N : ℕ) (f : ThresholdHilbert) :
    balancedHeadProjection N f =
      ∑ k ∈ Finset.range N, scalarBalancedCoefficient (headIndex k) f •
        scalarBalancedHilbert (headIndex k) := by
  simp [balancedHeadProjection, headCoefficient, headVector]

private theorem balancedHeadProjection_generator (N k : ℕ) (hk : k < N) :
    balancedHeadProjection N (headVector k) = headVector k := by
  rw [balancedHeadProjection_apply]
  change (∑ j ∈ Finset.range N, headCoefficient j (headVector k) • headVector j) = _
  simp [head_biorthogonal, hk]

private theorem balancedHeadProjection_eq_self (N : ℕ) (g : ThresholdHilbert)
    (hg : g ∈ balancedHeadSpan N) : balancedHeadProjection N g = g := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨k, hk, rfl⟩ := hg
      exact balancedHeadProjection_generator N k hk
  | zero => simp
  | add f g hf hg ihf ihg => simp [map_add, ihf, ihg]
  | smul c g hg ih => simp [map_smul, ih]

/-- Canonical truncation preserves every coordinate in its head, unconditionally. -/
theorem balancedHeadProjection_exact_head (N : ℕ) (f : ThresholdHilbert)
    (n : ℕ) (hn : 0 < n) (hnN : n ≤ N) :
    hilbertSequence (balancedHeadProjection N f) n = hilbertSequence f n := by
  obtain ⟨g, hg, hhead⟩ := exists_balancedHead_interpolant N f
  have he : balancedHeadProjection N f = balancedHeadProjection N g := by
    rw [balancedHeadProjection_apply, balancedHeadProjection_apply]
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    apply scalarBalancedCoefficient_congr_head
    intro j hj hjk
    have hkN : k + 1 ≤ N := Nat.succ_le_of_lt (Finset.mem_range.mp hk)
    have hjN : j ≤ N := le_trans hjk hkN
    exact (hhead j hj hjN).symm
  rw [he, balancedHeadProjection_eq_self N g hg]
  exact hhead n hn hnN

/-- Truncating any vector in the supported closure lands in the supported finite
span. This is useful for finite-head corrections to approximating sequences. -/
theorem balancedHeadProjection_mem_nonzeroTargetSpan (N : ℕ) (f : ThresholdHilbert)
    (hf : f ∈ dictionaryClosure balancedIndexHilbert balancedNonzeroTargetSupport) :
    balancedHeadProjection N f ∈
      dictionarySpan balancedIndexHilbert balancedNonzeroTargetSupport := by
  rw [balancedHeadProjection_apply]
  apply Submodule.sum_mem
  intro k hk
  by_cases hz : scalarBalancedCoefficient (headIndex k) f = 0
  · rw [hz, zero_smul]
    exact Submodule.zero_mem _
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨scalarBalancedIndex (headIndex k), ?_, rfl⟩
    exact biorthogonal_nonzero_target_mem balancedIndexHilbert balancedCoefficientCLM
      balancedCoefficientCLM_biorthogonal balancedNonzeroTargetSupport hf
      (scalarBalancedIndex (headIndex k)) hz

/-- The source packet A_N, with the forced coefficients L_m(1). -/
def balancedTargetHead (N : ℕ) : ThresholdHilbert := balancedHeadProjection N hilbertOne

/-- Exact finite interpolation remains possible after simultaneous deletion of all
zero-target generators. This is a finite assertion, with no norm bound. -/
theorem balancedTargetHead_mem_nonzeroTargetSpan (N : ℕ) :
    balancedTargetHead N ∈ dictionarySpan balancedIndexHilbert balancedNonzeroTargetSupport := by
  rw [balancedTargetHead, balancedHeadProjection_apply]
  apply Submodule.sum_mem
  intro k hk
  by_cases hz : scalarBalancedCoefficient (headIndex k) hilbertOne = 0
  · rw [hz, zero_smul]
    exact Submodule.zero_mem _
  · apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨scalarBalancedIndex (headIndex k), ?_, rfl⟩
    change balancedCoefficientTarget (scalarBalancedIndex (headIndex k)) ≠ 0
    rw [← balancedCoefficientCLM_one]
    exact hz

/-- The actual nonzero-target packet is exactly one at every coordinate ≤ N. -/
theorem balancedTargetHead_exact (N n : ℕ) (hn : 0 < n) (hnN : n ≤ N) :
    hilbertSequence (balancedTargetHead N) n = 1 := by
  rw [balancedTargetHead, balancedHeadProjection_exact_head N hilbertOne n hn hnN,
    hilbertOne_sequence]
  simp [zeroAnchor, ne_of_gt hn]

end
end RiemannResearch.RH.Pareto
