import RiemannResearch.RH.MobiusResidualFirstCoordinate
import RiemannResearch.RH.ParetoPointClosure
import RiemannResearch.Analysis.FiniteGramCapacity

/-!
# Actual full-tail capacity for the residue dictionary

Source: user-provided continuation
`RH_First_Coordinate_and_Tail_Capacity_Continuation_2026-09-19.md`,
Sections 12, 14 and 15, for statements and proof strategy.
The first physical coordinate is removed from actual Hilbert vectors.
No arithmetic divergence estimate or unconditional RH is assumed.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteGramCapacity
open RiemannResearch.RH.ArithmeticCumulative

local notation "e₁" => paretoPointHilbert 0

@[simp] theorem firstPoint_evaluation : anchoredEvaluationCLM 1 e₁ = 1 := by
  rw [anchoredEvaluationCLM_apply, hilbertSequence_paretoPoint]
  norm_num [paretoPointSequence]

@[simp] theorem residueAtom_evaluation (i : ℕ) :
    anchoredEvaluationCLM 1 (residueAtom i) = 1 / ((i + 2 : ℕ) : ℝ) := by
  rw [anchoredEvaluationCLM_apply, residueAtom, normalizedResidueHilbert_sequence]
  simp [residueFraction, Nat.mod_eq_of_lt (by omega : 1 < i + 2)]

theorem inner_firstPoint (f : ThresholdHilbert) :
    inner ℝ f e₁ = (1 / 2 : ℝ) * anchoredEvaluationCLM 1 f := by
  simpa [paretoWeight, hilbertGibbsPhysical_eq, anchoredEvaluationCLM_apply] using
    inner_paretoPoint f 0

theorem firstPoint_norm_sq : ‖e₁‖ ^ 2 = (1 / 2 : ℝ) := by
  rw [← real_inner_self_eq_norm_sq, inner_firstPoint, firstPoint_evaluation, mul_one]

/-- Remove only the physical value at one; retain the entire infinite tail. -/
def tailMap : ThresholdHilbert →ₗ[ℝ] ThresholdHilbert where
  toFun f := f - (anchoredEvaluationCLM 1 f) • e₁
  map_add' f g := by simp only [map_add, add_smul]; abel
  map_smul' c f := by
    simp only [map_smul, smul_eq_mul, RingHom.id_apply]
    rw [smul_sub, smul_smul]

@[simp] theorem tailMap_evaluation (f : ThresholdHilbert) :
    anchoredEvaluationCLM 1 (tailMap f) = 0 := by
  change anchoredEvaluationCLM 1 (f - (anchoredEvaluationCLM 1 f) • e₁) = 0
  simp only [map_sub, map_smul, firstPoint_evaluation, smul_eq_mul, mul_one, sub_self]

theorem tailMap_inner (f g : ThresholdHilbert) :
    inner ℝ (tailMap f) (tailMap g) = inner ℝ f g -
      (1 / 2 : ℝ) * (anchoredEvaluationCLM 1 f) * (anchoredEvaluationCLM 1 g) := by
  have hleft : inner ℝ e₁ g = (1 / 2 : ℝ) * anchoredEvaluationCLM 1 g := by
    rw [real_inner_comm, inner_firstPoint]
  change inner ℝ (f - (anchoredEvaluationCLM 1 f) • e₁)
    (g - (anchoredEvaluationCLM 1 g) • e₁) = _
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, inner_smul_right,
    inner_firstPoint, hleft, firstPoint_evaluation]
  ring

theorem tailMap_norm_sq (f : ThresholdHilbert) :
    ‖tailMap f‖ ^ 2 = ‖f‖ ^ 2 - (1 / 2 : ℝ) * (anchoredEvaluationCLM 1 f) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, tailMap_inner, real_inner_self_eq_norm_sq]
  ring

private theorem tailMap_eq_zero_of_legal {f : ThresholdHilbert}
    (hf : f ∈ hilbertLegalSubspace {n : ℕ | 0 < n}) (h : tailMap f = 0) : f = 0 := by
  have he : f = (anchoredEvaluationCLM 1 f) • e₁ := sub_eq_zero.mp h
  by_cases hz : anchoredEvaluationCLM 1 f = 0
  · simpa only [hz, zero_smul] using he
  · have hmem : (anchoredEvaluationCLM 1 f) • e₁ ∈
        hilbertLegalSubspace {n : ℕ | 0 < n} := he ▸ hf
    have hh := (hilbertLegalSubspace {n : ℕ | 0 < n}).smul_mem
      (anchoredEvaluationCLM 1 f)⁻¹ hmem
    have hp : e₁ ∈ hilbertLegalSubspace {n : ℕ | 0 < n} := by
      simpa only [smul_smul, inv_mul_cancel₀ hz, one_smul] using hh
    exact (paretoPoint_zero_not_mem_legalSubspace _ (fun _ hn => hn) hp).elim

def tailAtom (i : ℕ) : ThresholdHilbert := tailMap (residueAtom i)

def reciprocalSource (n : ℕ) (i : Fin n) : ℝ := 1 / ((i.val + 2 : ℕ) : ℝ)

theorem finiteAtom_independent (n : ℕ) :
    LinearIndependent ℝ (fun i : Fin n => residueAtom i.val) :=
  residueAtom_linearIndependent.comp (fun i : Fin n => i.val) Fin.val_injective

theorem finiteTailAtom_independent (n : ℕ) :
    LinearIndependent ℝ (fun i : Fin n => tailAtom i.val) := by
  apply Fintype.linearIndependent_iff.mpr
  intro a ha
  have hsum : tailMap (∑ i : Fin n, a i • residueAtom i.val) = 0 := by
    simpa only [map_sum, map_smul, tailAtom] using ha
  have hlegal : (∑ i : Fin n, a i • residueAtom i.val) ∈
      hilbertLegalSubspace {n : ℕ | 0 < n} := by
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (residueAtom_mem_legal i.val)
  exact Fintype.linearIndependent_iff.mp (finiteAtom_independent n) a
    (tailMap_eq_zero_of_legal hlegal hsum)

theorem gram_rank_one (n : ℕ) (a : Fin n → ℝ) (i : Fin n) :
    gram (fun j : Fin n => residueAtom j.val) a i =
      gram (fun j : Fin n => tailAtom j.val) a i +
        (1 / 2 : ℝ) * reciprocalSource n i *
          (∑ j, a j * reciprocalSource n j) := by
  simp only [gram_apply, tailAtom, tailMap_inner, residueAtom_evaluation, reciprocalSource]
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  have he : (∑ j : Fin n,
      ((1 / 2 : ℝ) * (1 / ((i.val + 2 : ℕ) : ℝ)) *
        (1 / ((j.val + 2 : ℕ) : ℝ))) * a j) =
      ∑ j : Fin n, (1 / 2 : ℝ) * (1 / ((i.val + 2 : ℕ) : ℝ)) *
        (a j * (1 / ((j.val + 2 : ℕ) : ℝ))) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  ring

/-- Stage n contains g₂,...,g_(n+1), consistently with finiteSpace. -/
def tailCapacity (n : ℕ) : ℝ :=
  capacity (finiteTailAtom_independent n) (reciprocalSource n)

def fullCapacity (n : ℕ) : ℝ :=
  capacity (finiteAtom_independent n) (reciprocalSource n)

def pointError (n : ℕ) : ℝ := walkError residueAtom id e₁ n

theorem tailCapacity_nonneg (n : ℕ) : 0 ≤ tailCapacity n :=
  capacity_nonneg (finiteTailAtom_independent n) (reciprocalSource n)

theorem fullCapacity_eq (n : ℕ) :
    fullCapacity n = 2 * tailCapacity n / (tailCapacity n + 2) :=
  capacity_rank_one_half (finiteAtom_independent n) (finiteTailAtom_independent n)
    (reciprocalSource n) (gram_rank_one n)

theorem pointProjection_eq_synthesis (n : ℕ) :
    (finiteSpace n).starProjection e₁ =
      Fintype.linearCombination ℝ (fun i : Fin n => residueAtom i.val)
        (inverseCoeff (finiteAtom_independent n) e₁) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [Fintype.linearCombination_apply]
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨i, rfl⟩
  · intro w hw
    obtain ⟨a, ha⟩ := finiteSpace_expansion n w hw
    rw [ha]
    simpa only [Fintype.linearCombination_apply] using
      residual_orthogonal (finiteAtom_independent n) e₁ a

theorem pointError_eq_deficit (n : ℕ) :
    pointError n = (1 / 2 : ℝ) - (1 / 4 : ℝ) * fullCapacity n := by
  unfold pointError walkError
  change ‖e₁ - (finiteSpace n).starProjection e₁‖ ^ 2 = _
  rw [pointProjection_eq_synthesis]
  apply point_target_deficit (finiteAtom_independent n) (reciprocalSource n) e₁
    firstPoint_norm_sq
  intro i
  change inner ℝ (residueAtom i.val) e₁ = _
  rw [inner_firstPoint, residueAtom_evaluation]
  rfl

theorem pointError_eq_inv_capacity (n : ℕ) :
    pointError n = 1 / (tailCapacity n + 2) := by
  rw [pointError_eq_deficit]
  exact pointDeficit_rank_one_half (finiteAtom_independent n) (finiteTailAtom_independent n)
    (reciprocalSource n) (gram_rank_one n)

theorem pointError_pos (n : ℕ) : 0 < pointError n := by
  rw [pointError_eq_inv_capacity]
  apply one_div_pos.mpr
  linarith [tailCapacity_nonneg n]

/-- The arithmetic statement required for RH; no provider is asserted. -/
def TailCapacityDivergence : Prop := Tendsto tailCapacity atTop atTop

/-- Divergence is exactly the remaining point-approximation limit. -/
theorem tailCapacity_tendsto_iff :
    Tendsto tailCapacity atTop atTop ↔ Tendsto pointError atTop (𝓝 0) := by
  constructor
  · intro ht
    have hs : Tendsto (fun n => tailCapacity n + 2) atTop atTop := by
      apply tendsto_atTop.mpr
      intro b
      filter_upwards [(tendsto_atTop.mp ht) (b - 2)] with n hn
      linarith
    have hi := tendsto_inv_atTop_zero.comp hs
    simpa only [Function.comp_def, ← one_div, ← pointError_eq_inv_capacity] using hi
  · intro he
    have hp : Tendsto pointError atTop (𝓝[>] (0 : ℝ)) := by
      apply tendsto_nhdsWithin_iff.mpr
      exact ⟨he, Filter.Eventually.of_forall pointError_pos⟩
    have hi := tendsto_inv_nhdsGT_zero.comp hp
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [(tendsto_atTop.mp hi) (b + 2)] with n hn
    have hn' : b + 2 ≤ tailCapacity n + 2 := by
      simpa only [Function.comp_def, pointError_eq_inv_capacity, one_div,
        inv_inv] using hn
    linarith

/-- Conditional RH endpoint. No proof of TailCapacityDivergence is supplied. -/
theorem riemannHypothesis_of_tailCapacity_tendsto
    (h : TailCapacityDivergence) : RiemannHypothesis :=
  riemannHypothesis_of_firstPoint_error_tendsto_zero
    (tailCapacity_tendsto_iff.mp h)

/-- The equivalent scalar saturation criterion for the full Gram matrix. -/
theorem fullCapacity_tendsto_two_iff :
    Tendsto fullCapacity atTop (𝓝 2) ↔ Tendsto pointError atTop (𝓝 0) := by
  constructor
  · intro hk
    have hh : Tendsto (fun n => (1 / 2 : ℝ) - (1 / 4 : ℝ) * fullCapacity n)
        atTop (𝓝 ((1 / 2 : ℝ) - (1 / 4 : ℝ) * 2)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul hk)
    simpa only [← pointError_eq_deficit, show (1 / 2 : ℝ) - (1 / 4 : ℝ) * 2 = 0
      by norm_num] using hh
  · intro he
    have hkap (n : ℕ) : fullCapacity n = 2 - 4 * pointError n := by
      linarith [pointError_eq_deficit n]
    have hh : Tendsto (fun n => (2 : ℝ) - 4 * pointError n) atTop (𝓝 (2 - 4 * 0)) :=
      tendsto_const_nhds.sub (tendsto_const_nhds.mul he)
    simpa only [← hkap, mul_zero, sub_zero] using hh

theorem riemannHypothesis_of_fullCapacity_tendsto
    (h : Tendsto fullCapacity atTop (𝓝 2)) : RiemannHypothesis :=
  riemannHypothesis_of_firstPoint_error_tendsto_zero
    (fullCapacity_tendsto_two_iff.mp h)

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
