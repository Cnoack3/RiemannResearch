import RiemannResearch.RH.ParetoTailCapacityDuality
import RiemannResearch.RH.TailCapacityDilationCorrection
import RiemannResearch.LinearAlgebra.FiniteHilbertSchur

/-!
# Joint screened corrections for the actual first-coordinate optimizer

Source: user-provided argument,
`RH_First_Coordinate_and_Tail_Capacity_Continuation_2026-09-19.md`, Section 29,
for the signed objective, covariance, reciprocal-defect source, and proposed
divergent-gain criterion. The coefficient optimizer is obtained from actual
finite normal equations, including dependent trial directions. The arithmetic
divergence assertion remains an explicit conditional research obligation.

The stage `n` contains moduli 2 through n+1, so it is N=n+1 in the source.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteHilbertConstraints
open RiemannResearch.Analysis.FiniteGramCapacity
open RiemannResearch.LinearAlgebra
open RiemannResearch.RH.ArithmeticCumulative

theorem reciprocalSource_ne_zero (n : ℕ) (hn : 0 < n) : reciprocalSource n ≠ 0 := by
  intro hz
  have h := congrFun hz ⟨0, hn⟩
  norm_num [reciprocalSource] at h

theorem tailCapacity_pos (n : ℕ) (hn : 0 < n) : 0 < tailCapacity n :=
  capacity_pos (finiteTailAtom_independent n) (reciprocalSource n)
    (reciprocalSource_ne_zero n hn)

/-- The exact minimum tail energy at first coordinate one. -/
def constrainedTailEnergy (n : ℕ) : ℝ := 1 / tailCapacity n

def headMinimizer (n : ℕ) : ThresholdHilbert :=
  (tailCapacity n)⁻¹ • finiteSchurCombination
    (fun i : Fin n => residueAtom i.val)
    (inverseSource (finiteTailAtom_independent n) (reciprocalSource n))

theorem atomCombination_evaluation (n : ℕ) (a : Fin n → ℝ) :
    anchoredEvaluationCLM 1
      (finiteSchurCombination (fun i : Fin n => residueAtom i.val) a) =
      ∑ i, a i * reciprocalSource n i := by
  simp only [finiteSchurCombination, map_sum, map_smul, smul_eq_mul,
    residueAtom_evaluation, reciprocalSource]

theorem atomCombination_mem (n : ℕ) (a : Fin n → ℝ) :
    finiteSchurCombination (fun i : Fin n => residueAtom i.val) a ∈ finiteSpace n := by
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem headMinimizer_mem (n : ℕ) : headMinimizer n ∈ finiteSpace n :=
  Submodule.smul_mem _ _ (atomCombination_mem n _)

theorem headMinimizer_evaluation (n : ℕ) (hn : 0 < n) :
    anchoredEvaluationCLM 1 (headMinimizer n) = 1 := by
  rw [headMinimizer, map_smul, atomCombination_evaluation]
  change (tailCapacity n)⁻¹ * tailCapacity n = 1
  exact inv_mul_cancel₀ (ne_of_gt (tailCapacity_pos n hn))

theorem headMinimizer_tail (n : ℕ) :
    tailMap (headMinimizer n) = (tailCapacity n)⁻¹ • tailMinimum n := by
  simp only [headMinimizer, finiteSchurCombination, map_smul, map_sum, tailAtom,
    tailMinimum, minimumVector, Fintype.linearCombination_apply, inverseSource]

theorem headMinimizer_tail_energy (n : ℕ) (hn : 0 < n) :
    ‖tailMap (headMinimizer n)‖ ^ 2 = constrainedTailEnergy n := by
  rw [headMinimizer_tail]
  exact normalized_energy (finiteTailAtom_independent n) (reciprocalSource n)
    (reciprocalSource_ne_zero n hn)

theorem headMinimizer_norm_sq (n : ℕ) (hn : 0 < n) :
    ‖headMinimizer n‖ ^ 2 = 1 / 2 + constrainedTailEnergy n := by
  have h := headMinimizer_tail_energy n hn
  rw [tailMap_norm_sq, headMinimizer_evaluation n hn] at h
  norm_num at h
  linarith

/-- The finite dual representer exactly evaluates the first coordinate on
the old legal space after removing its physical first coordinate. -/
theorem tailMinimum_pairing_old (n : ℕ) (S : ThresholdHilbert)
    (hS : S ∈ finiteSpace n) :
    inner ℝ (tailMinimum n) (tailMap S) = anchoredEvaluationCLM 1 S := by
  obtain ⟨a, rfl⟩ := finiteSpace_expansion n S hS
  have ho (i : Fin n) : inner ℝ (tailMinimum n) (tailMap (residueAtom i.val)) =
      reciprocalSource n i := by
    rw [real_inner_comm]
    exact tailMinimum_observation n i
  simp only [map_sum, map_smul, inner_sum, real_inner_smul_right, ho,
    smul_eq_mul, residueAtom_evaluation, reciprocalSource]

theorem headMinimizer_pairing_old (n : ℕ) (hn : 0 < n)
    (S : ThresholdHilbert) (hS : S ∈ finiteSpace n) :
    inner ℝ (headMinimizer n) S =
      (1 / 2 + constrainedTailEnergy n) * anchoredEvaluationCLM 1 S := by
  have h := tailMap_inner (headMinimizer n) S
  rw [headMinimizer_evaluation n hn, headMinimizer_tail,
    real_inner_smul_left, tailMinimum_pairing_old n S hS] at h
  simp only [constrainedTailEnergy, one_div] at *
  linarith

/-- The full old coefficient space with first coordinate zero. -/
def zeroHeadSpace (n : ℕ) : Submodule ℝ ThresholdHilbert :=
  Submodule.span ℝ (Set.range (fun i : Fin n =>
    residueAtom i.val - reciprocalSource n i • headMinimizer n))

instance zeroHeadSpace_finiteDimensional (n : ℕ) :
    FiniteDimensional ℝ (zeroHeadSpace n) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

theorem zeroHeadSpace_le (n : ℕ) : zeroHeadSpace n ≤ finiteSpace n := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact Submodule.sub_mem _ (Submodule.subset_span ⟨i, rfl⟩)
    (Submodule.smul_mem _ _ (headMinimizer_mem n))

theorem zeroHeadSpace_evaluation (n : ℕ) (hn : 0 < n) (u : ThresholdHilbert)
    (hu : u ∈ zeroHeadSpace n) : anchoredEvaluationCLM 1 u = 0 := by
  have hle : zeroHeadSpace n ≤ LinearMap.ker (anchoredEvaluationCLM 1).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change anchoredEvaluationCLM 1
      (residueAtom i.val - reciprocalSource n i • headMinimizer n) = 0
    simp only [map_sub, map_smul, headMinimizer_evaluation n hn, smul_eq_mul,
      mul_one, residueAtom_evaluation, reciprocalSource, sub_self]
  exact hle hu

theorem zeroHeadSpace_mem_iff (n : ℕ) (hn : 0 < n) (u : ThresholdHilbert) :
    u ∈ zeroHeadSpace n ↔ u ∈ finiteSpace n ∧ anchoredEvaluationCLM 1 u = 0 := by
  constructor
  · intro hu
    exact ⟨zeroHeadSpace_le n hu, zeroHeadSpace_evaluation n hn u hu⟩
  · rintro ⟨hu, hh⟩
    obtain ⟨a, rfl⟩ := finiteSpace_expansion n u hu
    have hh' : (∑ i : Fin n, a i * reciprocalSource n i) = 0 := by
      simpa only [map_sum, map_smul, smul_eq_mul, residueAtom_evaluation,
        reciprocalSource] using hh
    have he : (∑ i : Fin n, a i • residueAtom i.val) =
        ∑ i : Fin n, a i • (residueAtom i.val -
          reciprocalSource n i • headMinimizer n) := by
      simp only [smul_sub, smul_smul, Finset.sum_sub_distrib,
        ← Finset.sum_smul, hh', zero_smul, sub_zero]
    rw [he]
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem headMinimizer_orthogonal (n : ℕ) (hn : 0 < n)
    (u : ThresholdHilbert) (hu : u ∈ zeroHeadSpace n) :
    inner ℝ (headMinimizer n) u = 0 := by
  rw [headMinimizer_pairing_old n hn u (zeroHeadSpace_le n hu),
    zeroHeadSpace_evaluation n hn u hu, mul_zero]

/-- Remove the first-coordinate constraint and then reoptimize every old
zero-head coefficient. -/
def screenedTrial (n : ℕ) (S : ThresholdHilbert) : ThresholdHilbert :=
  let W := S - anchoredEvaluationCLM 1 S • headMinimizer n
  W - (zeroHeadSpace n).starProjection W

theorem screenedTrial_evaluation (n : ℕ) (hn : 0 < n) (S : ThresholdHilbert) :
    anchoredEvaluationCLM 1 (screenedTrial n S) = 0 := by
  unfold screenedTrial
  rw [map_sub, zeroHeadSpace_evaluation n hn _
    ((zeroHeadSpace n).starProjection_apply_mem _)]
  simp only [map_sub, map_smul, headMinimizer_evaluation n hn,
    smul_eq_mul, mul_one, sub_self]

theorem screenedTrial_mem (n m : ℕ) (hnm : n ≤ m)
    (S : ThresholdHilbert) (hS : S ∈ finiteSpace m) :
    screenedTrial n S ∈ finiteSpace m := by
  apply Submodule.sub_mem
  · exact Submodule.sub_mem _ hS (Submodule.smul_mem _ _
      (walkSpan_mono residueAtom id hnm (headMinimizer_mem n)))
  · exact walkSpan_mono residueAtom id hnm
      (zeroHeadSpace_le n ((zeroHeadSpace n).starProjection_apply_mem _))

/-- Equation (29.2), with the signed first-coordinate term retained. -/
theorem screenedTrial_source (n : ℕ) (hn : 0 < n) (S : ThresholdHilbert) :
    inner ℝ (headMinimizer n) (screenedTrial n S) =
      inner ℝ (headMinimizer n) S -
        anchoredEvaluationCLM 1 S * ‖headMinimizer n‖ ^ 2 := by
  unfold screenedTrial
  rw [inner_sub_right, headMinimizer_orthogonal n hn _
    ((zeroHeadSpace n).starProjection_apply_mem _), sub_zero,
    inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]

/-- Equation (29.3): the complete projection covariance is subtracted. -/
theorem screenedTrial_covariance (n : ℕ) (S T : ThresholdHilbert) :
    inner ℝ (screenedTrial n S) (screenedTrial n T) =
      inner ℝ (S - anchoredEvaluationCLM 1 S • headMinimizer n)
        (T - anchoredEvaluationCLM 1 T • headMinimizer n) -
      inner ℝ ((zeroHeadSpace n).starProjection
        (S - anchoredEvaluationCLM 1 S • headMinimizer n))
        ((zeroHeadSpace n).starProjection
        (T - anchoredEvaluationCLM 1 T • headMinimizer n)) :=
  inner_residualized_eq_schur (zeroHeadSpace n) _ _

variable {ι : Type*} [Fintype ι]

def jointTrial (n : ℕ) (S : ι → ThresholdHilbert) (c : ι → ℝ) : ThresholdHilbert :=
  finiteSchurResidual (headMinimizer n) (fun i => screenedTrial n (S i)) c

theorem jointTrial_evaluation (n : ℕ) (hn : 0 < n)
    (S : ι → ThresholdHilbert) (c : ι → ℝ) :
    anchoredEvaluationCLM 1 (jointTrial n S c) = 1 := by
  simp only [jointTrial, finiteSchurResidual, finiteSchurCombination, map_sub,
    map_sum, map_smul, screenedTrial_evaluation n hn, smul_zero,
    Finset.sum_const_zero, sub_zero, headMinimizer_evaluation n hn]

theorem jointTrial_mem (n m : ℕ) (hnm : n ≤ m) (S : ι → ThresholdHilbert)
    (hS : ∀ i, S i ∈ finiteSpace m) (c : ι → ℝ) :
    jointTrial n S c ∈ finiteSpace m := by
  apply Submodule.sub_mem
  · exact walkSpan_mono residueAtom id hnm (headMinimizer_mem n)
  · apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (screenedTrial_mem n m hnm (S i) (hS i))

/-- Equation (29.4), including every signed mixed Gram entry. -/
theorem jointTrial_signed_energy (n : ℕ) (hn : 0 < n)
    (S : ι → ThresholdHilbert) (c : ι → ℝ) :
    ‖tailMap (jointTrial n S c)‖ ^ 2 = constrainedTailEnergy n -
      2 * (∑ i, c i * inner ℝ (headMinimizer n) (screenedTrial n (S i))) +
      ∑ i, ∑ j, c i * c j *
        inner ℝ (screenedTrial n (S i)) (screenedTrial n (S j)) := by
  have hnorm : ‖finiteSchurCombination (fun i => screenedTrial n (S i)) c‖ ^ 2 =
      ∑ i, ∑ j, c i * c j *
        inner ℝ (screenedTrial n (S i)) (screenedTrial n (S j)) := by
    change ‖Fintype.linearCombination ℝ (fun i => screenedTrial n (S i)) c‖ ^ 2 = _
    rw [gram_quadratic]
    simp only [gram_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hcross : inner ℝ (headMinimizer n)
      (finiteSchurCombination (fun i => screenedTrial n (S i)) c) =
      ∑ i, c i * inner ℝ (headMinimizer n) (screenedTrial n (S i)) := by
    simp only [finiteSchurCombination, inner_sum, real_inner_smul_right]
  rw [tailMap_norm_sq, jointTrial_evaluation n hn]
  unfold jointTrial finiteSchurResidual
  rw [norm_sub_sq_real, headMinimizer_norm_sq n hn, hnorm, hcross]
  ring

/-- Choose a normal-equation solution, allowing singular or repeated columns. -/
def jointCoefficients (n : ℕ) (S : ι → ThresholdHilbert) : ι → ℝ :=
  Classical.choose (finiteSchur_exists_normal (headMinimizer n)
    (fun i => screenedTrial n (S i)))

theorem jointCoefficients_normal (n : ℕ) (S : ι → ThresholdHilbert) (i : ι) :
    inner ℝ (screenedTrial n (S i))
      (finiteSchurCombination (fun j => screenedTrial n (S j)) (jointCoefficients n S)) =
      inner ℝ (screenedTrial n (S i)) (headMinimizer n) :=
  Classical.choose_spec (finiteSchur_exists_normal (headMinimizer n)
    (fun j => screenedTrial n (S j))) i

/-- The inverse-free value of dᵀH†d, defined by its actual Hilbert projection. -/
def jointGain (n : ℕ) (S : ι → ThresholdHilbert) : ℝ :=
  ‖finiteSchurCombination (fun i => screenedTrial n (S i)) (jointCoefficients n S)‖ ^ 2

theorem jointGain_source (n : ℕ) (S : ι → ThresholdHilbert) :
    jointGain n S = ∑ i, jointCoefficients n S i *
      inner ℝ (headMinimizer n) (screenedTrial n (S i)) := by
  unfold jointGain
  rw [← real_inner_self_eq_norm_sq]
  conv_lhs => arg 2; unfold finiteSchurCombination
  simp only [sum_inner, real_inner_smul_left, jointCoefficients_normal]
  apply Finset.sum_congr rfl
  intro i hi
  rw [real_inner_comm]

theorem jointTrial_optimal_energy (n : ℕ) (hn : 0 < n) (S : ι → ThresholdHilbert) :
    ‖tailMap (jointTrial n S (jointCoefficients n S))‖ ^ 2 =
      constrainedTailEnergy n - jointGain n S := by
  rw [tailMap_norm_sq, jointTrial_evaluation n hn]
  have h := finiteSchurResidual_norm_sq (headMinimizer n)
    (fun i => screenedTrial n (S i)) (jointCoefficients n S) (jointCoefficients_normal n S)
  change ‖jointTrial n S (jointCoefficients n S)‖ ^ 2 = _ at h
  rw [h, headMinimizer_norm_sq n hn, jointGain_source]
  have hsum : (∑ i, jointCoefficients n S i *
      inner ℝ (screenedTrial n (S i)) (headMinimizer n)) =
      ∑ i, jointCoefficients n S i *
      inner ℝ (headMinimizer n) (screenedTrial n (S i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [real_inner_comm]
  rw [hsum]
  ring

theorem jointTrial_completion (n : ℕ) (hn : 0 < n)
    (S : ι → ThresholdHilbert) (c : ι → ℝ) :
    ‖tailMap (jointTrial n S c)‖ ^ 2 =
      constrainedTailEnergy n - jointGain n S +
      ‖finiteSchurCombination (fun i => screenedTrial n (S i)) c -
        finiteSchurCombination (fun i => screenedTrial n (S i)) (jointCoefficients n S)‖ ^ 2 := by
  have h := finiteSchurResidual_completion (headMinimizer n)
    (fun i => screenedTrial n (S i)) c (jointCoefficients n S) (jointCoefficients_normal n S)
  change ‖jointTrial n S c‖ ^ 2 =
    ‖jointTrial n S (jointCoefficients n S)‖ ^ 2 + _ at h
  have he := jointTrial_optimal_energy n hn S
  rw [tailMap_norm_sq, jointTrial_evaluation n hn] at he ⊢
  linarith

/-- The actual reciprocal defect; `i` denotes modulus i+2. -/
def reciprocalDefect (n i : ℕ) : ℝ :=
  1 / ((i + 2 : ℕ) : ℝ) - inner ℝ (tailMinimum n) (tailAtom i)

theorem reciprocalDefect_old (n : ℕ) (i : Fin n) : reciprocalDefect n i.val = 0 := by
  unfold reciprocalDefect
  rw [real_inner_comm, tailMinimum_observation]
  simp only [reciprocalSource, sub_self]

/-- Equation (29.7) before deleting the old indices whose defects are zero. -/
theorem screenedTrial_actual_source (n m : ℕ) (hn : 0 < n) (β : Fin m → ℝ) :
    inner ℝ (headMinimizer n)
        (screenedTrial n (finiteSchurCombination (fun i : Fin m => residueAtom i.val) β)) /
      constrainedTailEnergy n = -∑ i, β i * reciprocalDefect n i.val := by
  let S := finiteSchurCombination (fun i : Fin m => residueAtom i.val) β
  have htail : inner ℝ (tailMinimum n) (tailMap S) =
      ∑ i, β i * inner ℝ (tailMinimum n) (tailAtom i.val) := by
    simp only [S, finiteSchurCombination, map_sum, map_smul, inner_sum,
      real_inner_smul_right, tailAtom]
  have hsplit := tailMap_inner (headMinimizer n) S
  rw [headMinimizer_tail, real_inner_smul_left, htail,
    headMinimizer_evaluation n hn] at hsplit
  have heval := atomCombination_evaluation m β
  change anchoredEvaluationCLM 1 S = _ at heval
  have hnum := screenedTrial_source n hn S
  rw [headMinimizer_norm_sq n hn] at hnum
  have hsum : (∑ i, β i * reciprocalDefect n i.val) =
      anchoredEvaluationCLM 1 S -
        ∑ i, β i * inner ℝ (tailMinimum n) (tailAtom i.val) := by
    simp only [reciprocalDefect, mul_sub, Finset.sum_sub_distrib]
    rw [heval]
    rfl
  change inner ℝ (headMinimizer n) (screenedTrial n S) /
    constrainedTailEnergy n = _
  rw [hsum]
  apply (div_eq_iff (ne_of_gt (one_div_pos.mpr (tailCapacity_pos n hn)))).mpr
  simp only [constrainedTailEnergy, one_div] at *
  nlinarith [hsplit, hnum]

/-- The true finite tail minimum bounds every legal first-coordinate-one trial. -/
theorem constrainedTailEnergy_le_trial (n : ℕ) (hn : 0 < n)
    (F : ThresholdHilbert) (hF : F ∈ finiteSpace n)
    (hhead : anchoredEvaluationCLM 1 F = 1) :
    constrainedTailEnergy n ≤ ‖tailMap F‖ ^ 2 := by
  obtain ⟨a, rfl⟩ := finiteSpace_expansion n F hF
  have hc : (∑ i : Fin n, a i * reciprocalSource n i) = 1 := by
    simpa only [map_sum, map_smul, smul_eq_mul, residueAtom_evaluation,
      reciprocalSource] using hhead
  have h := constrained_completion (finiteTailAtom_independent n)
    (reciprocalSource n) a (reciprocalSource_ne_zero n hn) hc
  have ht : tailMap (∑ i : Fin n, a i • residueAtom i.val) =
      Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) a := by
    simp only [map_sum, map_smul, Fintype.linearCombination_apply, tailAtom]
  rw [ht, h]
  exact le_add_of_nonneg_right (sq_nonneg _)

theorem jointGain_bounds (n m : ℕ) (hn : 0 < n) (hnm : n ≤ m)
    (S : ι → ThresholdHilbert) (hS : ∀ i, S i ∈ finiteSpace m) :
    0 ≤ jointGain n S ∧ jointGain n S < constrainedTailEnergy n := by
  have hm : 0 < m := lt_of_lt_of_le hn hnm
  have hlo := constrainedTailEnergy_le_trial m hm
    (jointTrial n S (jointCoefficients n S))
    (jointTrial_mem n m hnm S hS _) (jointTrial_evaluation n hn S _)
  rw [jointTrial_optimal_energy n hn S] at hlo
  have hp : 0 < constrainedTailEnergy m := one_div_pos.mpr (tailCapacity_pos m hm)
  exact ⟨sq_nonneg _, by linarith⟩

/-- The exact reciprocal-capacity improvement induced by the optimized block. -/
def jointCapacityGain (n : ℕ) (S : ι → ThresholdHilbert) : ℝ :=
  jointGain n S /
    (constrainedTailEnergy n * (constrainedTailEnergy n - jointGain n S))

/-- Equation (29.5), using the actual next constrained minimum. -/
theorem jointCapacityGain_le (n m : ℕ) (hn : 0 < n) (hnm : n ≤ m)
    (S : ι → ThresholdHilbert) (hS : ∀ i, S i ∈ finiteSpace m) :
    jointCapacityGain n S ≤ tailCapacity m - tailCapacity n := by
  have hm : 0 < m := lt_of_lt_of_le hn hnm
  have hlo := constrainedTailEnergy_le_trial m hm
    (jointTrial n S (jointCoefficients n S))
    (jointTrial_mem n m hnm S hS _) (jointTrial_evaluation n hn S _)
  rw [jointTrial_optimal_energy n hn S] at hlo
  have h := (reciprocal_capacity_gain (constrainedTailEnergy n)
    (constrainedTailEnergy m) (jointGain n S)
    (one_div_pos.mpr (tailCapacity_pos m hm)) (sq_nonneg _) hlo).2
  simpa only [jointCapacityGain, constrainedTailEnergy, one_div, inv_inv] using h

theorem jointCapacityGain_nonneg (n m : ℕ) (hn : 0 < n) (hnm : n ≤ m)
    (S : ι → ThresholdHilbert) (hS : ∀ i, S i ∈ finiteSpace m) :
    0 ≤ jointCapacityGain n S := by
  have h := jointGain_bounds n m hn hnm S hS
  exact div_nonneg h.1 (mul_nonneg
    (le_of_lt (one_div_pos.mpr (tailCapacity_pos n hn))) (le_of_lt (sub_pos.mpr h.2)))

/-- The gain cannot be supplied by a null Gram direction. The identity
and existence theorem retain redundant trial columns without assuming independence. -/
theorem jointGain_eq_zero_iff (n : ℕ) (S : ι → ThresholdHilbert) :
    jointGain n S = 0 ↔
      ∀ i, inner ℝ (headMinimizer n) (screenedTrial n (S i)) = 0 := by
  have h := finiteSchurResidual_gain_zero_iff (headMinimizer n)
    (fun i => screenedTrial n (S i)) (jointCoefficients n S) (jointCoefficients_normal n S)
  have he := finiteSchurResidual_norm_sq (headMinimizer n)
    (fun i => screenedTrial n (S i)) (jointCoefficients n S) (jointCoefficients_normal n S)
  have hg : jointGain n S = ∑ i, jointCoefficients n S i *
      inner ℝ (screenedTrial n (S i)) (headMinimizer n) := by
    rw [jointGain_source]
    apply Finset.sum_congr rfl
    intro i hi
    rw [real_inner_comm]
  rw [he, sub_sub_cancel, ← hg] at h
  simpa only [real_inner_comm (headMinimizer n)] using h

/-- Finite telescoping requires only actual one-step capacity lower bounds. -/
theorem jointCapacityGain_partial_sum_le (N r : ℕ → ℕ)
    (hN : ∀ j, 0 < N j) (hstep : ∀ j, N j ≤ N (j + 1))
    (S : (j : ℕ) → Fin (r j) → ThresholdHilbert)
    (hS : ∀ j i, S j i ∈ finiteSpace (N (j + 1))) (J : ℕ) :
    tailCapacity (N 0) + (∑ j ∈ Finset.range J, jointCapacityGain (N j) (S j)) ≤
      tailCapacity (N J) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ]
    have h := jointCapacityGain_le (N J) (N (J + 1)) (hN J) (hstep J) (S J) (hS J)
    linarith

/-- Open arithmetic target: the accumulated actual screened gains are
unbounded. Their nonnegativity makes this equivalent to divergence to +∞. -/
def JointScreenedGainDivergence (N r : ℕ → ℕ)
    (S : (j : ℕ) → Fin (r j) → ThresholdHilbert) : Prop :=
  ∀ B : ℝ, ∃ J : ℕ, B < ∑ j ∈ Finset.range J, jointCapacityGain (N j) (S j)

/-- Conditional research reduction corresponding to (29.8).
The open premise is divergence of the actual gains; no provider is asserted. -/
theorem riemannHypothesis_of_jointScreenedGainDivergence (N r : ℕ → ℕ)
    (hN : ∀ j, 0 < N j) (hstep : ∀ j, N j ≤ N (j + 1))
    (S : (j : ℕ) → Fin (r j) → ThresholdHilbert)
    (hS : ∀ j i, S j i ∈ finiteSpace (N (j + 1)))
    (hdiv : JointScreenedGainDivergence N r S) : RiemannHypothesis := by
  apply riemannHypothesis_of_no_tailCertificate
  rintro ⟨z, hz⟩
  obtain ⟨J, hJ⟩ := hdiv (‖z‖ ^ 2 - tailCapacity (N 0))
  have htel := jointCapacityGain_partial_sum_le N r hN hstep S hS J
  have hbound := tailCapacity_le_certificate_energy z hz (N J)
  linarith

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity


noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
open RiemannResearch.RH.ArithmeticCumulative

/-- Source: user-provided continuation, Sections 29.1 and 31. Under the
certificate alternative, every reciprocal defect is an actual dual error pairing. -/
theorem reciprocalDefect_eq_certificate_error (z : ThresholdHilbert)
    (hz : IsResidueTailCertificate z) (n i : ℕ) :
    reciprocalDefect n i = inner ℝ (z - tailMinimum n) (tailAtom i) := by
  have h := tailCertificate_observation z hz (i + 1) ⟨i, Nat.lt_succ_self i⟩
  change inner ℝ (tailAtom i) z = 1 / ((i + 2 : ℕ) : ℝ) at h
  unfold reciprocalDefect
  rw [inner_sub_left]
  exact congrArg (fun r : ℝ => r - inner ℝ (tailMinimum n) (tailAtom i))
    ((real_inner_comm z (tailAtom i)).symm.trans h).symm

/-- A tail certificate represents the head functional on every finite legal space. -/
theorem tailCertificate_pairing_finiteSpace (z : ThresholdHilbert)
    (hz : IsResidueTailCertificate z) (m : ℕ) (S : ThresholdHilbert)
    (hS : S ∈ finiteSpace m) :
    inner ℝ z S = anchoredEvaluationCLM 1 S := by
  obtain ⟨a, rfl⟩ := finiteSpace_expansion m S hS
  have ho (i : Fin m) : inner ℝ z (residueAtom i.val) =
      reciprocalSource m i := hz.2 (i.val + 2) (by omega)
  simp only [inner_sum, real_inner_smul_right, ho, map_sum, map_smul,
    smul_eq_mul, residueAtom_evaluation, reciprocalSource]

/-- The exact screened source is the signed correlation with the dual error.
No decay rate, summability, or divergent-gain estimate is asserted. -/
theorem screenedTrial_source_certificate_error (n m : ℕ) (hn : 0 < n)
    (hnm : n ≤ m) (z : ThresholdHilbert) (hz : IsResidueTailCertificate z)
    (S : ThresholdHilbert) (hS : S ∈ finiteSpace m) :
    inner ℝ (headMinimizer n) (screenedTrial n S) =
      -constrainedTailEnergy n * inner ℝ (z - tailMinimum n) (screenedTrial n S) := by
  have hy := screenedTrial_evaluation n hn S
  have hcert := tailCertificate_pairing_finiteSpace z hz m (screenedTrial n S)
    (screenedTrial_mem n m hnm S hS)
  rw [hy] at hcert
  have htail : tailMap (screenedTrial n S) = screenedTrial n S := by
    change screenedTrial n S - anchoredEvaluationCLM 1 (screenedTrial n S) • _ = _
    rw [hy, zero_smul, sub_zero]
  have he := tailMap_inner (headMinimizer n) (screenedTrial n S)
  rw [headMinimizer_tail, htail, real_inner_smul_left, hy, mul_zero, sub_zero] at he
  rw [inner_sub_left, hcert, zero_sub]
  simpa only [constrainedTailEnergy, one_div, neg_mul_neg] using he.symm

end RiemannResearch.RH.Pareto.CoefficientStabilization.TailCapacity
