import RiemannResearch.Analysis.FiniteHilbertGramProjection
import RiemannResearch.RH.IntegerDPPClosure
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import RiemannResearch.RH.ParetoResidueMean

/-!
# Actual residue Gram–Schmidt coordinates and exact saturation criteria

Source: user-provided orthonormal/Gram/DPP conversation, 2026-09-20.
Mathlib supplies Gram–Schmidt and finite Bessel theory. These are exact
identities for the actual full-norm residue span. RH is a proved consequence
of saturation; the separate converse from RH is not assumed or asserted.

The continuous Möbius coordinate functional provides unconditional absolute
convergence of every fixed coefficient series. This does not prove that its
sum equals the Möbius target. The target equality is equivalent to Parseval
saturation for the constant, and to the vanishing first-site vacancy.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.FiniteHilbertGram

/-- Index j denotes the mode obtained after adjoining conductor j+2. -/
def residueMode : ℕ → ThresholdHilbert :=
  InnerProductSpace.gramSchmidtNormed ℝ residueAtom

theorem residueMode_orthonormal : Orthonormal ℝ residueMode :=
  InnerProductSpace.gramSchmidtNormed_orthonormal residueAtom_linearIndependent

theorem residueMode_span :
    Submodule.span ℝ (Set.range residueMode) =
      Submodule.span ℝ (Set.range residueAtom) := by
  exact (InnerProductSpace.span_gramSchmidtNormed_range residueAtom).trans
    (InnerProductSpace.span_gramSchmidt ℝ residueAtom)

theorem residueMode_closedSpace : dictionaryClosure residueMode = closedSpace := by
  unfold dictionaryClosure
  rw [residueMode_span]
  rfl

private theorem walkSpan_eq_image (v : ℕ → ThresholdHilbert) (n : ℕ) :
    walkSpan v id n = Submodule.span ℝ (v '' Set.Iio n) := by
  unfold walkSpan
  congr 1
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, i.isLt, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩

theorem residueMode_finiteSpace (n : ℕ) :
    synthesisSpan (fun i : Fin n => residueMode i.val) = finiteSpace n := by
  change walkSpan residueMode id n = walkSpan residueAtom id n
  rw [walkSpan_eq_image, walkSpan_eq_image]
  exact (InnerProductSpace.span_gramSchmidtNormed residueAtom (Set.Iio n)).trans
    (InnerProductSpace.span_gramSchmidt_Iio ℝ residueAtom n)

def modeAlpha (j : ℕ) : ℝ := inner ℝ (residueMode j) hilbertOne
def modeCoefficient (m j : ℕ) : ℝ := coefficientCLM m (residueMode j)

theorem modeCoefficient_eq_zero_of_lt {i j : ℕ} (hji : j < i) :
    modeCoefficient (i + 2) j = 0 := by
  have hm : residueMode j ∈ finiteSpace (j + 1) := by
    rw [← residueMode_finiteSpace (j + 1)]
    exact Submodule.subset_span ⟨⟨j, Nat.lt_succ_self j⟩, rfl⟩
  obtain ⟨a, ha⟩ := finiteSpace_expansion (j + 1) (residueMode j) hm
  unfold modeCoefficient
  rw [ha, map_sum]
  apply Finset.sum_eq_zero
  intro k hk
  rw [map_smul, coefficientCLM_biorthogonal]
  have hik : i ≠ k.val := by
    have hklt := k.isLt
    omega
  simp [hik]

theorem projection_eq_mode_sum (n : ℕ) :
    projection n = ∑ j : Fin n, modeAlpha j.val • residueMode j.val := by
  have hn : Orthonormal ℝ (fun i : Fin n => residueMode i.val) :=
    residueMode_orthonormal.comp (fun i : Fin n => i.val) Fin.val_injective
  simpa only [residueMode_finiteSpace, projection, modeAlpha] using
    projection_eq_orthonormal_sum hn hilbertOne

theorem energy_eq_one_sub_mode_sum (n : ℕ) :
    energy n = 1 - ∑ j : Fin n, (modeAlpha j.val) ^ 2 := by
  have hn : Orthonormal ℝ (fun i : Fin n => residueMode i.val) :=
    residueMode_orthonormal.comp (fun i : Fin n => i.val) Fin.val_injective
  change ‖hilbertOne - (finiteSpace n).starProjection hilbertOne‖ ^ 2 = _
  simpa only [residueMode_finiteSpace, hilbertOne_norm_sq, modeAlpha] using
    projection_error_eq_orthonormal_sum hn hilbertOne

theorem mode_sum_eq_one_sub_energy (n : ℕ) :
    (∑ j ∈ Finset.range n, (modeAlpha j) ^ 2) = 1 - energy n := by
  have h := energy_eq_one_sub_mode_sum n
  rw [Fin.sum_univ_eq_sum_range (fun j => (modeAlpha j) ^ 2) n] at h
  linarith

theorem modeAlpha_sq_hasSum :
    HasSum (fun j => (modeAlpha j) ^ 2) (1 - limitEnergy) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun j => sq_nonneg _) _).mpr
  simpa only [mode_sum_eq_one_sub_energy] using
    (tendsto_const_nhds.sub energy_tendsto :
      Tendsto (fun n => 1 - energy n) atTop (𝓝 (1 - limitEnergy)))

theorem modeAlpha_sq_tsum :
    (∑' j, (modeAlpha j) ^ 2) = 1 - limitEnergy := modeAlpha_sq_hasSum.tsum_eq

theorem mode_parseval_iff_one_mem :
    (∑' j, (modeAlpha j) ^ 2) = 1 ↔ hilbertOne ∈ closedSpace := by
  rw [modeAlpha_sq_tsum, ← limitEnergy_zero_iff_mem]
  constructor <;> intro h <;> linarith

theorem mode_parseval_iff_vacancy :
    (∑' j, (modeAlpha j) ^ 2) = 1 ↔
      Tendsto IntegerDPP.vacancy atTop (𝓝 0) :=
  mode_parseval_iff_one_mem.trans IntegerDPP.vacancy_tendsto_zero_iff_one_mem.symm

theorem mode_parseval_iff_mobius :
    (∑' j, (modeAlpha j) ^ 2) = 1 ↔
      ∀ m : ℕ, 1 < m → limitCoefficient m = -(ArithmeticFunction.moebius m : ℝ) :=
  mode_parseval_iff_one_mem.trans limitCoefficients_eq_mobius_iff_mem.symm

theorem riemannHypothesis_of_mode_parseval
    (h : (∑' j, (modeAlpha j) ^ 2) = 1) : RiemannHypothesis :=
  riemannHypothesis_of_limitCoefficients (mode_parseval_iff_mobius.mp h)

theorem coefficient_eq_mode_sum (n m : ℕ) :
    coefficient n m =
      ∑ j : Fin n, modeAlpha j.val * modeCoefficient m j.val := by
  unfold coefficient
  rw [projection_eq_mode_sum]
  simp only [map_sum, map_smul, smul_eq_mul, modeCoefficient]

theorem modeCoefficient_sq_summable (m : ℕ) :
    Summable (fun j => (modeCoefficient m j) ^ 2) := by
  have h := Orthonormal.inner_products_summable
    (mobiusRieszHilbert m) residueMode_orthonormal
  have hp (j : ℕ) :
      ‖inner ℝ (residueMode j) (mobiusRieszHilbert m)‖ ^ 2 =
        (modeCoefficient m j) ^ 2 := by
    rw [real_inner_comm, mobiusRieszHilbert_inner]
    simp only [Real.norm_eq_abs, sq_abs, modeCoefficient,
      coefficientCLM, neg_apply, neg_sq]
  simpa only [hp] using h

/-- Absolute convergence is unconditional; it does not assert Möbius values. -/
theorem mode_coefficient_series_norm_summable (m : ℕ) :
    Summable (fun j => ‖modeAlpha j * modeCoefficient m j‖) := by
  apply Summable.of_nonneg_of_le (fun j => norm_nonneg _)
    (fun j => ?_) (modeAlpha_sq_hasSum.summable.add
      (modeCoefficient_sq_summable m))
  simp only [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|modeAlpha j| - |modeCoefficient m j|),
    sq_abs (modeAlpha j), sq_abs (modeCoefficient m j)]

theorem mode_coefficient_series_hasSum (m : ℕ) :
    HasSum (fun j => modeAlpha j * modeCoefficient m j) (limitCoefficient m) := by
  apply (mode_coefficient_series_norm_summable m).of_norm.hasSum_iff_tendsto_nat.mpr
  have he (n : ℕ) :
      (∑ j ∈ Finset.range n, modeAlpha j * modeCoefficient m j) =
        coefficient n m := by
    rw [← Fin.sum_univ_eq_sum_range
      (fun j => modeAlpha j * modeCoefficient m j) n]
    exact (coefficient_eq_mode_sum n m).symm
  simpa only [he] using coefficient_tendsto m

theorem limitCoefficient_eq_mode_tsum (m : ℕ) :
    limitCoefficient m = ∑' j, modeAlpha j * modeCoefficient m j :=
  (mode_coefficient_series_hasSum m).tsum_eq.symm

/-- Triangularity removes all modes before conductor i+2. -/
theorem mode_coefficient_tail_hasSum (i : ℕ) :
    HasSum (fun j => modeAlpha (j + i) * modeCoefficient (i + 2) (j + i))
      (limitCoefficient (i + 2)) := by
  have h := (hasSum_nat_add_iff'
    (f := fun j => modeAlpha j * modeCoefficient (i + 2) j)
    (g := limitCoefficient (i + 2)) i).mpr (mode_coefficient_series_hasSum (i + 2))
  have hz : (∑ j ∈ Finset.range i, modeAlpha j * modeCoefficient (i + 2) j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [modeCoefficient_eq_zero_of_lt (Finset.mem_range.mp hj), mul_zero]
  simpa only [hz, sub_zero] using h

theorem limitCoefficient_eq_mode_tail (i : ℕ) :
    limitCoefficient (i + 2) =
      ∑' j, modeAlpha (j + i) * modeCoefficient (i + 2) (j + i) :=
  (mode_coefficient_tail_hasSum i).tsum_eq.symm

theorem mode_mobius_tsum_iff_parseval :
    (∀ m : ℕ, 1 < m →
      (∑' j, modeAlpha j * modeCoefficient m j) =
        -(ArithmeticFunction.moebius m : ℝ)) ↔
      (∑' j, (modeAlpha j) ^ 2) = 1 := by
  simp only [← limitCoefficient_eq_mode_tsum]
  exact mode_parseval_iff_mobius.symm

theorem residueMode_complete_iff_parseval :
    dictionaryClosure residueMode = ⊤ ↔
      (∑' j, (modeAlpha j) ^ 2) = 1 := by
  rw [residueMode_closedSpace, closedSpace_eq_top_iff_one_mem]
  exact mode_parseval_iff_one_mem.symm

theorem limitProjection_eq_one_iff_mode_parseval :
    limitProjection = hilbertOne ↔ (∑' j, (modeAlpha j) ^ 2) = 1 := by
  change closedSpace.starProjection hilbertOne = hilbertOne ↔ _
  rw [Submodule.starProjection_eq_self_iff]
  exact mode_parseval_iff_one_mem.symm

/-- The canonical vector expansion converges to the actual projection. -/
theorem mode_partialSums_tendsto :
    Tendsto (fun n => ∑ j ∈ Finset.range n, modeAlpha j • residueMode j)
      atTop (𝓝 limitProjection) := by
  have he (n : ℕ) :
      (∑ j ∈ Finset.range n, modeAlpha j • residueMode j) = projection n := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => modeAlpha j • residueMode j) n]
    exact (projection_eq_mode_sum n).symm
  simpa only [he] using projection_tendsto

theorem mode_expansion_iff_parseval :
    Tendsto (fun n => ∑ j ∈ Finset.range n, modeAlpha j • residueMode j)
      atTop (𝓝 hilbertOne) ↔ (∑' j, (modeAlpha j) ^ 2) = 1 := by
  constructor
  · intro h
    exact limitProjection_eq_one_iff_mode_parseval.mp
      (tendsto_nhds_unique mode_partialSums_tendsto h)
  · intro h
    have he := limitProjection_eq_one_iff_mode_parseval.mpr h
    simpa only [he] using mode_partialSums_tendsto

/-- A residual expansion in the legal mode closure would prove its vanishing.
Gram–Schmidt alone only puts the projected component in that closure. -/
theorem limitResidual_mem_modeClosure_iff_zero :
    limitResidual ∈ dictionaryClosure residueMode ↔ limitResidual = 0 := by
  rw [residueMode_closedSpace]
  constructor
  · intro h
    have hi := (closedSpace.mem_orthogonal limitResidual).mp
      limitResidual_mem_orthogonal limitResidual h
    rw [real_inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero] at hi
    exact hi
  · intro h
    rw [h]
    exact closedSpace.zero_mem

theorem riemannHypothesis_of_residual_mem_modeClosure
    (h : limitResidual ∈ dictionaryClosure residueMode) : RiemannHypothesis :=
  riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_residual_zero.mpr
      (limitResidual_mem_modeClosure_iff_zero.mp h))

/-- Any Hilbert-convergent expansion of the limiting residual in legal modes
would supply the remaining membership claim and therefore prove RH. -/
theorem riemannHypothesis_of_residual_mode_series (a : ℕ → ℝ)
    (h : HasSum (fun j => a j • residueMode j) limitResidual) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_residual_mem_modeClosure
  have hc : IsClosed (dictionaryClosure residueMode : Set ThresholdHilbert) :=
    Submodule.isClosed_topologicalClosure _
  apply hc.mem_of_tendsto h.tendsto_sum_nat
  apply Eventually.of_forall
  intro n
  apply (dictionaryClosure residueMode).sum_mem
  intro j hj
  apply (dictionaryClosure residueMode).smul_mem
  exact (Submodule.span ℝ (Set.range residueMode)).le_topologicalClosure
    (Submodule.subset_span ⟨j, rfl⟩)

theorem mode_parseval_strict_of_not_RH (h : ¬ RiemannHypothesis) :
    (∑' j, (modeAlpha j) ^ 2) < 1 := by
  have hle : (∑' j, (modeAlpha j) ^ 2) ≤ 1 := by
    rw [modeAlpha_sq_tsum]
    exact sub_le_self _ (sq_nonneg _)
  by_contra hn
  have he : (∑' j, (modeAlpha j) ^ 2) = 1 :=
    le_antisymm hle (le_of_not_gt hn)
  exact h (riemannHypothesis_of_mode_parseval he)

theorem residueAtom_inner_one (i : ℕ) :
    inner ℝ (residueAtom i) hilbertOne =
      Real.log ((i + 2 : ℕ) : ℝ) / ((i + 2 : ℕ) : ℝ) := by
  rw [residueAtom, normalizedResidueHilbert, real_inner_smul_left,
    hilbert_inner_one, hilbertSequence_digitHilbert]
  have he : digitSequence (i + 2) 1 = residue (i + 2) := by
    funext k
    simp [digitSequence, residue]
  rw [he, paretoMean_residue (i + 2) (by omega)]
  ring

theorem residueMode_expansion (j : ℕ) :
    residueMode j = ∑ k : Fin (j + 1),
      modeCoefficient (k.val + 2) j • residueAtom k.val := by
  have hm : residueMode j ∈ finiteSpace (j + 1) := by
    rw [← residueMode_finiteSpace (j + 1)]
    exact Submodule.subset_span ⟨⟨j, Nat.lt_succ_self j⟩, rfl⟩
  obtain ⟨a, ha⟩ := finiteSpace_expansion (j + 1) (residueMode j) hm
  have hc (k : Fin (j + 1)) : modeCoefficient (k.val + 2) j = a k := by
    unfold modeCoefficient
    rw [ha]
    exact coefficient_finite_sum (j + 1) a k
  simpa only [hc] using ha

theorem modeAlpha_eq_log_sum (j : ℕ) :
    modeAlpha j = ∑ k : Fin (j + 1), modeCoefficient (k.val + 2) j *
      (Real.log ((k.val + 2 : ℕ) : ℝ) / ((k.val + 2 : ℕ) : ℝ)) := by
  unfold modeAlpha
  rw [residueMode_expansion, sum_inner]
  simp only [real_inner_smul_left, residueAtom_inner_one]

end RiemannResearch.RH.Pareto.CoefficientStabilization
