import RiemannResearch.RH.TwoSeedAnnihilatorCharge
import RiemannResearch.Analysis.ResidualHarmonicGain
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Actual matched-budget chord observability and the conditional RH reduction

Source: user-provided argument,
RH_Global_Approximation_and_Resonance_Blind_Patterns_Handoff_2026-09-16(1).md,
Sections 17, 20, 26--27. The source supports the statements and proof strategy.

The matched space uses its redundant full-generator presentation:
binary indices through 3M and ternary indices through 2M. Actual orthogonal
residuals satisfy both sets of normal equations. The normalized chord family
may be redundant, and no diagonal-only Gram approximation occurs.

The final RH theorem is a conditional research reduction: the uniform
synthesis bound and constant-target charge lower bound remain Open.
Finite termination is included in the scalar harmonic-loss lemma.
No 4M rank or arbitrary-block LDL factorization is claimed here.
-/

open scoped BigOperators
noncomputable section

namespace RiemannResearch.RH.Pareto.AdjacentPacket
open RiemannResearch.Analysis.ProjectionChordObservability
open RiemannResearch.Analysis.ProjectionSourceImprovement

def matchedFamily (M : ℕ) : Fin (3*M) ⊕ Fin (2*M) → ThresholdHilbert
  | Sum.inl i => generator 2 (i.val+1) (by omega) (by omega)
  | Sum.inr i => generator 3 (i.val+1) (by omega) (by omega)

def matchedSpace (M : ℕ) : Submodule ℝ ThresholdHilbert :=
  Submodule.span ℝ (Set.range (matchedFamily M))

instance matchedSpace_finiteDimensional (M : ℕ) : FiniteDimensional ℝ (matchedSpace M) := by
  exact FiniteDimensional.span_of_finite ℝ (Set.finite_range (matchedFamily M))

instance matchedSpace_hasOrthogonalProjection (M : ℕ) :
    (matchedSpace M).HasOrthogonalProjection := by infer_instance

def matchedResidual (M : ℕ) : ThresholdHilbert :=
  RiemannResearch.Analysis.ProjectionSourceImprovement.residual (matchedSpace M) hilbertOne

def matchedEnergy (M : ℕ) : ℝ := ‖matchedResidual M‖^2

theorem binary_mem_matchedSpace (M m : ℕ) (hm : 0 < m) (hu : m ≤ 3*M) :
    generator 2 m (by omega) hm ∈ matchedSpace M := by
  apply Submodule.subset_span
  refine ⟨Sum.inl ⟨m-1, by omega⟩, ?_⟩
  simp only [matchedFamily, show m-1+1=m by omega]

theorem ternary_mem_matchedSpace (M m : ℕ) (hm : 0 < m) (hu : m ≤ 2*M) :
    generator 3 m (by omega) hm ∈ matchedSpace M := by
  apply Submodule.subset_span
  refine ⟨Sum.inr ⟨m-1, by omega⟩, ?_⟩
  simp only [matchedFamily, show m-1+1=m by omega]

theorem matchedSpace_mono {M N : ℕ} (h : M ≤ N) : matchedSpace M ≤ matchedSpace N := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  cases i with
  | inl i => exact binary_mem_matchedSpace N (i.val+1) (by omega) (by omega)
  | inr i => exact ternary_mem_matchedSpace N (i.val+1) (by omega) (by omega)

theorem matched_binary_normal (M m : ℕ) (hm : 0 < m) (hu : m ≤ 3*M) :
    inner ℝ (matchedResidual M) (generator 2 m (by omega) hm) = 0 :=
  Submodule.starProjection_inner_eq_zero hilbertOne _ (binary_mem_matchedSpace M m hm hu)

theorem matched_ternary_normal (M m : ℕ) (hm : 0 < m) (hu : m ≤ 2*M) :
    inner ℝ (matchedResidual M) (generator 3 m (by omega) hm) = 0 :=
  Submodule.starProjection_inner_eq_zero hilbertOne _ (ternary_mem_matchedSpace M m hm hu)

theorem chord_mem_matchedSpace (N a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (haN : a ≤ N) (hbN : b ≤ N) : chord a b ha hb ∈ matchedSpace N :=
  (matchedSpace N).sub_mem
    (ternary_mem_matchedSpace N (2*b) (by omega) (by omega))
    (ternary_mem_matchedSpace N (2*a) (by omega) (by omega))

variable {ι : Type*} [Fintype ι]

def normalizedChords (a b : ι → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (w : ι → ℝ) (i : ι) : ThresholdHilbert :=
  (1/Real.sqrt (w i)) • chord (a i) (b i) (ha i) (hb i)

theorem normalized_sourceSquare (P : Submodule ℝ ThresholdHilbert)
    [P.HasOrthogonalProjection]
    (a b : ι → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    sourceSquare P hilbertOne (normalizedChords a b ha hb w) =
      ∑ i, (inner ℝ (RiemannResearch.Analysis.ProjectionSourceImprovement.residual P hilbertOne)
        (chord (a i) (b i) (ha i) (hb i)))^2 / w i := by
  unfold sourceSquare source normalizedChords
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_smul_right, mul_pow, div_pow, one_pow, Real.sq_sqrt (hw i).le]
  ring

theorem matched_chord_gain (M : ℕ)
    (a b : ι → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (haM : ∀ i, a i ≤ 2*M) (hbM : ∀ i, b i ≤ 2*M)
    (w : ι → ℝ) (hw : ∀ i, 0 < w i) {C c : ℝ} (hC : 0 < C)
    (hBessel : ∀ t : ι → ℝ,
      ‖Fintype.linearCombination ℝ (normalizedChords a b ha hb w) t‖^2 ≤
        C*∑ i, (t i)^2)
    (hCharge : c * matchedEnergy M ≤
      ∑ i, (inner ℝ (matchedResidual M) (chord (a i) (b i) (ha i) (hb i)))^2/w i) :
    c*matchedEnergy M/C ≤ matchedEnergy M-matchedEnergy (2*M) := by
  apply gain_ge_charge (matchedSpace M) (matchedSpace (2*M))
    (matchedSpace_mono (by omega)) hilbertOne (normalizedChords a b ha hb w)
  · intro i
    exact (matchedSpace (2*M)).smul_mem _ (chord_mem_matchedSpace (2*M)
      (a i) (b i) (ha i) (hb i) (haM i) (hbM i))
  · exact hC
  · exact hBessel
  · rw [normalized_sourceSquare _ a b ha hb w hw]
    exact hCharge

end RiemannResearch.RH.Pareto.AdjacentPacket

namespace RiemannResearch.RH.Pareto.AdjacentPacket
open Filter
open scoped Topology
open RiemannResearch.Analysis.ProjectionSourceImprovement
open RiemannResearch.Analysis.ProjectionChordObservability

theorem matchedSpace_le_twoSeedClosure (M : ℕ) :
    matchedSpace M ≤ hilbertLegalClosure {2,3} := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  cases i with
  | inl i => exact generator_mem_twoSeedClosure 2 (i.val+1) (by omega) (by omega) (Or.inl rfl)
  | inr i => exact generator_mem_twoSeedClosure 3 (i.val+1) (by omega) (by omega) (Or.inr rfl)

theorem riemannHypothesis_of_matchedEnergy_convergence (J : ℕ → ℕ)
    (h : Tendsto (fun n => matchedEnergy (J n)) atTop (𝓝 0)) :
    RiemannHypothesis := by
  have hn : Tendsto (fun n => ‖matchedResidual (J n)‖) atTop (𝓝 0) := by
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp h
    simpa [Function.comp_def, matchedEnergy, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using hs
  have hp : Tendsto (fun n => (matchedSpace (J n)).starProjection hilbertOne)
      atTop (𝓝 hilbertOne) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa [matchedResidual, RiemannResearch.Analysis.ProjectionSourceImprovement.residual,
      norm_sub_rev] using hn
  have hc : IsClosed (hilbertLegalClosure {2,3} : Set ThresholdHilbert) :=
    (hilbertLegalSubspace {2,3}).isClosed_topologicalClosure
  apply riemannHypothesis_of_twoSeed_closure
  apply hc.mem_of_tendsto hp
  exact Filter.Eventually.of_forall (fun n =>
    matchedSpace_le_twoSeedClosure (J n) (Submodule.starProjection_apply_mem _ _))

theorem riemannHypothesis_of_dyadic_chord_bessel_charge
    {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    (a b : ∀ n, ι n → ℕ)
    (ha : ∀ n i, 0 < a n i) (hb : ∀ n i, 0 < b n i)
    (haM : ∀ n i, a n i ≤ 2*2^n) (hbM : ∀ n i, b n i ≤ 2*2^n)
    (w : ∀ n, ι n → ℝ) (hw : ∀ n i, 0 < w n i)
    {B c : ℝ} (hB : 0 < B) (hc : 0 < c)
    (hBessel : ∀ n (t : ι n → ℝ),
      ‖Fintype.linearCombination ℝ (normalizedChords (a n) (b n) (ha n) (hb n) (w n)) t‖^2 ≤
        (B*((n:ℝ)+1))*∑ i, (t i)^2)
    (hCharge : ∀ n, c*matchedEnergy (2^n) ≤
      ∑ i, (inner ℝ (matchedResidual (2^n))
        (chord (a n i) (b n i) (ha n i) (hb n i)))^2/w n i) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_matchedEnergy_convergence (fun n => 2^n)
  apply RiemannResearch.Analysis.ResidualGain.tendsto_zero_of_harmonic_loss
    (a := c/B) (fun n => sq_nonneg _) (div_pos hc hB)
  intro n
  have hg := matched_chord_gain (2^n) (a n) (b n) (ha n) (hb n) (haM n) (hbM n)
    (w n) (hw n) (C := B*((n:ℝ)+1)) (c := c) (by positivity)
    (hBessel n) (hCharge n)
  have he : 2*2^n = 2^(n+1) := by simp [pow_succ, Nat.mul_comm]
  rw [he] at hg
  have hs : c/B/((n:ℝ)+1)*matchedEnergy (2^n) =
      c*matchedEnergy (2^n)/(B*((n:ℝ)+1)) := by
    field_simp
  change c/B/((n:ℝ)+1)*matchedEnergy (2^n) ≤
    matchedEnergy (2^n)-matchedEnergy (2^(n+1))
  rw [hs]
  exact hg

end RiemannResearch.RH.Pareto.AdjacentPacket
