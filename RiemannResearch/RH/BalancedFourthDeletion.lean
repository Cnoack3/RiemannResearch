import RiemannResearch.RH.BalancedResidueDictionary
import RiemannResearch.RH.ParetoCoordinateEvaluation
import RiemannResearch.RH.DilationWaveletAlgebra
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Removing the fourth balanced generator in the actual Pareto topology

Source: RH_Minimal_Seeds_Canonical_Basis_and_Arithmetic_Charge_20260914.md,
Section 5. The removed generator is exactly R₁₂-R₄. Its continuous coefficient
is (f(4)-f(3)-f(2)+f(1))/4, which vanishes at the constant target.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

def fourthCoefficientLinear : (ℕ → ℝ) →ₗ[ℝ] ℝ where
  toFun f := (f 4 - f 3 - f 2 + f 1) / 4
  map_add' f g := by simp only [Pi.add_apply]; ring
  map_smul' c f := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring


def fourthCoefficientCLM : ThresholdHilbert →L[ℝ] ℝ :=
  (1 / 4 : ℝ) • (physicalEvaluationCLM 3 - physicalEvaluationCLM 2 -
    physicalEvaluationCLM 1 + physicalEvaluationCLM 0)

@[simp] theorem fourthCoefficientCLM_apply (f : ThresholdHilbert) :
    fourthCoefficientCLM f = fourthCoefficientLinear (hilbertSequence f) := by
  simp only [fourthCoefficientCLM, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    physicalEvaluationCLM_apply, smul_eq_mul]
  change (1 / 4 : ℝ) * (hilbertSequence f 4 - hilbertSequence f 3 -
    hilbertSequence f 2 + hilbertSequence f 1) = _
  simp only [fourthCoefficientLinear, LinearMap.coe_mk, AddHom.coe_mk]
  ring

def balancedFourthSequence : ℕ → ℝ := dilation 4 (residue 3)

def balancedFourthHilbert : ThresholdHilbert :=
  (4 : ℝ) • digitHilbert 3 4 (by decide) (by decide)

@[simp] theorem hilbertSequence_balancedFourth :
    hilbertSequence balancedFourthHilbert = balancedFourthSequence := by
  change hilbertSequenceLinear ((4 : ℝ) • digitHilbert 3 4 _ _) = _
  rw [map_smul]
  change (4 : ℝ) • hilbertSequence (digitHilbert 3 4 _ _) = _
  rw [hilbertSequence_digitHilbert, digitSequence_eq_scaled_generator 3 4 (by decide)]
  simp [balancedFourthSequence, smul_smul]

@[simp] theorem fourthCoefficient_balancedFourth :
    fourthCoefficientLinear balancedFourthSequence = 1 := by
  norm_num [fourthCoefficientLinear, balancedFourthSequence, dilation, residue]

@[simp] theorem fourthCoefficient_one : fourthCoefficientCLM hilbertOne = 0 := by
  rw [fourthCoefficientCLM_apply]
  norm_num [fourthCoefficientLinear, hilbertOne_sequence, zeroAnchor]

/-- On the selected dictionary, this functional is nonzero only on R₁₂-R₄. -/
theorem fourthCoefficient_balanced_zero_or_eq
    (u a b : ℕ) (hu : IsTwoThreeRough u) :
    fourthCoefficientLinear (balancedResidueEdge u a b) = 0 ∨
      balancedResidueEdge u a b = balancedFourthSequence := by
  by_cases hsmall : 2 ^ a * 3 ^ b * u ≤ 4
  · rcases rough_grid_le_four u a b hu hsmall with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · left; norm_num [fourthCoefficientLinear, balancedResidueEdge_eq, dilation, residue]
    · left; norm_num [fourthCoefficientLinear, balancedResidueEdge_eq, dilation, residue]
    · left; norm_num [fourthCoefficientLinear, balancedResidueEdge_eq, dilation, residue]
    · right; simp [balancedResidueEdge_eq, balancedFourthSequence]
  · left
    have hm : 4 < 2 ^ a * 3 ^ b * u := by omega
    have he (p n : ℕ) (hn : n ≤ 4) :
        dilation (2 ^ a * 3 ^ b * u) (residue p) n = 0 := by
      simp [dilation, Nat.div_eq_of_lt (lt_of_le_of_lt hn hm), residue]
    rw [balancedResidueEdge_eq]
    split_ifs <;>
      simp [fourthCoefficientLinear, he 2 1 (by omega), he 2 2 (by omega),
        he 2 3 (by omega), he 2 4 (by omega), he 3 1 (by omega),
        he 3 2 (by omega), he 3 3 (by omega), he 3 4 (by omega)]

def balancedWithoutFourthSpan : Submodule ℝ (ℕ → ℝ) :=
  Submodule.span ℝ (balancedResidueDictionary \ {balancedFourthSequence})

def balancedWithoutFourthHilbertSpace : Submodule ℝ ThresholdHilbert :=
  balancedWithoutFourthSpan.comap hilbertSequenceLinear

def balancedWithoutFourthClosure : Submodule ℝ ThresholdHilbert :=
  balancedWithoutFourthHilbertSpace.topologicalClosure

def deleteFourthLinear : (ℕ → ℝ) →ₗ[ℝ] (ℕ → ℝ) :=
  LinearMap.id - fourthCoefficientLinear.smulRight balancedFourthSequence

def deleteFourthContinuous : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  ContinuousLinearMap.id ℝ ThresholdHilbert -
    fourthCoefficientCLM.smulRight balancedFourthHilbert

theorem deleteFourth_sequence (f : ThresholdHilbert) :
    hilbertSequence (deleteFourthContinuous f) =
      deleteFourthLinear (hilbertSequence f) := by
  change hilbertSequenceLinear (f - fourthCoefficientCLM f • balancedFourthHilbert) = _
  rw [map_sub, map_smul]
  change hilbertSequence f - fourthCoefficientCLM f • hilbertSequence balancedFourthHilbert = _
  simp only [fourthCoefficientCLM_apply, hilbertSequence_balancedFourth]
  rfl

theorem deleteFourth_mem_removed_span {f : ℕ → ℝ} (hf : f ∈ balancedResidueSpan) :
    deleteFourthLinear f ∈ balancedWithoutFourthSpan := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨u, a, b, hu, rfl⟩ := hf
      rcases fourthCoefficient_balanced_zero_or_eq u a b hu with hz | he
      · have hne : balancedResidueEdge u a b ≠ balancedFourthSequence := by
          intro he
          rw [he, fourthCoefficient_balancedFourth] at hz
          norm_num at hz
        change balancedResidueEdge u a b -
          fourthCoefficientLinear (balancedResidueEdge u a b) • balancedFourthSequence ∈ _
        rw [hz, zero_smul, sub_zero]
        exact Submodule.subset_span ⟨⟨u, a, b, hu, rfl⟩, hne⟩
      · rw [he]
        change balancedFourthSequence -
          fourthCoefficientLinear balancedFourthSequence • balancedFourthSequence ∈ _
        simp
  | zero => simpa using balancedWithoutFourthSpan.zero_mem
  | add f g hf hg ihf ihg => simpa only [map_add] using
      balancedWithoutFourthSpan.add_mem ihf ihg
  | smul c f hf ih => simpa only [map_smul] using
      balancedWithoutFourthSpan.smul_mem c ih

/-- The actual continuous finite-rank deletion preserves constant approximation. -/
theorem hilbertOne_mem_balancedWithoutFourth_iff :
    hilbertOne ∈ balancedWithoutFourthClosure ↔
      hilbertOne ∈ hilbertLegalClosure ({2, 3} : Set ℕ) := by
  constructor
  · intro hx
    have hs : balancedWithoutFourthHilbertSpace ≤ hilbertLegalSubspace {2, 3} := by
      intro f hf
      change hilbertSequence f ∈ legalSeedSpan {2, 3}
      rw [← balancedResidueSpan_eq_twoSeedSpan]
      exact Submodule.span_mono Set.diff_subset hf
    exact Submodule.topologicalClosure_mono hs hx
  · intro hx
    have hm : Set.MapsTo deleteFourthContinuous
        (hilbertLegalSubspace {2, 3} : Set ThresholdHilbert)
        (balancedWithoutFourthHilbertSpace : Set ThresholdHilbert) := by
      intro f hf
      change hilbertSequence (deleteFourthContinuous f) ∈ balancedWithoutFourthSpan
      rw [deleteFourth_sequence]
      apply deleteFourth_mem_removed_span
      rw [balancedResidueSpan_eq_twoSeedSpan]
      exact hf
    have h := hm.closure deleteFourthContinuous.continuous hx
    have he : deleteFourthContinuous hilbertOne = hilbertOne := by
      change hilbertOne - fourthCoefficientCLM hilbertOne • balancedFourthHilbert = _
      rw [fourthCoefficient_one, zero_smul, sub_zero]
    change hilbertOne ∈ (balancedWithoutFourthHilbertSpace.topologicalClosure :
      Set ThresholdHilbert)
    rw [Submodule.topologicalClosure_coe]
    simpa only [he] using h

theorem fourthCoefficient_zero_on_removed_closure
    {f : ThresholdHilbert} (hf : f ∈ balancedWithoutFourthClosure) :
    fourthCoefficientCLM f = 0 := by
  have hs : ∀ g ∈ balancedWithoutFourthSpan, fourthCoefficientLinear g = 0 := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
        obtain ⟨⟨u, a, b, hu, rfl⟩, hne⟩ := hg
        rcases fourthCoefficient_balanced_zero_or_eq u a b hu with hz | he
        · exact hz
        · exact False.elim (hne he)
    | zero => simp
    | add g k hg hk ihg ihk => simp [map_add, ihg, ihk]
    | smul c g hg ih => simp [map_smul, ih]
  have hsub : (balancedWithoutFourthHilbertSpace : Set ThresholdHilbert) ⊆
      {g | fourthCoefficientCLM g = 0} := by
    intro g hg
    change fourthCoefficientCLM g = 0
    rw [fourthCoefficientCLM_apply]
    exact hs _ hg
  exact (closure_minimal hsub
    (isClosed_eq fourthCoefficientCLM.continuous continuous_const)) hf

/-- Deleting h₄ preserves the particular constant approximation problem while
always destroying density of the whole ambient Hilbert space. -/
theorem balancedWithoutFourthClosure_ne_top : balancedWithoutFourthClosure ≠ ⊤ := by
  intro he
  have hf : balancedFourthHilbert ∈ balancedWithoutFourthClosure := by rw [he]; trivial
  have hz := fourthCoefficient_zero_on_removed_closure hf
  rw [fourthCoefficientCLM_apply, hilbertSequence_balancedFourth,
    fourthCoefficient_balancedFourth] at hz
  norm_num at hz

end
end RiemannResearch.RH.Pareto
