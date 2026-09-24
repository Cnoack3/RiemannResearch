import RiemannResearch.RH.ReciprocalGramCorrection
import RiemannResearch.RH.ResidueSchurLimits
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Signed reciprocal Schur increments and their absolute variation

Source: RH_Research_Agenda_2026-09-24(1).md, Priority 1, for the statements
and proof strategy. The proof uses the already established actual Pareto
projection identities and ordinary Bessel/Cauchy--Schwarz inequalities.
No signed saturation or unconditional RH conclusion is asserted.

Stage n adds conductor n+2. Only the mixed projection increments are
absolutely summable: the separate Möbius reciprocal increments are retained.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.GramMobiusCorrection
open RiemannResearch.Analysis.FiniteHilbertGram
open TailCapacity ProjectionSchur
open IntegerDPP (fullGram)

/-- The reciprocal Schur numerator is physical evaluation of the innovation. -/
def reciprocalEta (n : ℕ) : ℝ := anchoredEvaluationCLM 1 (innovation n)

/-- This is signed: it is a product of two different target numerators. -/
def mixedSchurIncrement (n : ℕ) : ℝ :=
  reciprocalEta n * schurEta n / schurSigma n

theorem reciprocalEta_eq_eliminated (n : ℕ) :
    reciprocalEta n = 1 / ((n + 2 : ℕ) : ℝ) -
      dotProduct (reciprocalSource n) (eliminated n) := by
  have hz : eliminated n = inverseCoeff (finiteAtom_independent n) (residueAtom n) := by
    rw [eliminated, fullGram, gramMatrix_inverseSource]
    rfl
  have hp : (finiteSpace n).starProjection (residueAtom n) =
      ∑ i : Fin n, eliminated n i • residueAtom i.val := by
    rw [hz]
    change (synthesisSpan (fun i : Fin n => residueAtom i.val)).starProjection
      (residueAtom n) = _
    simpa only [Fintype.linearCombination_apply] using
      (synthesis_inverseCoeff_eq_projection (finiteAtom_independent n) (residueAtom n)).symm
  rw [reciprocalEta, innovation, map_sub, residueAtom_evaluation, hp, map_sum]
  simp only [map_smul, smul_eq_mul, residueAtom_evaluation,
    dotProduct, reciprocalSource, mul_comm]

/-- Symmetric orientation of the reciprocal numerator used in the agenda. -/
theorem reciprocalEta_eq_gram_schur (n : ℕ) :
    reciprocalEta n = 1 / ((n + 2 : ℕ) : ℝ) -
      dotProduct (coupling n) ((fullGram n)⁻¹.mulVec (reciprocalSource n)) := by
  have hG : (fullGram n).IsSymm := by
    ext i j
    change inner ℝ (residueAtom j.val) (residueAtom i.val) =
      inner ℝ (residueAtom i.val) (residueAtom j.val)
    exact real_inner_comm (residueAtom i.val) (residueAtom j.val)
  have hI (i j : Fin n) : (fullGram n)⁻¹ i j = (fullGram n)⁻¹ j i := by
    have he : ((fullGram n)⁻¹).transpose = (fullGram n)⁻¹ := hG.inv
    exact (congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => M i j) he).symm
  rw [reciprocalEta_eq_eliminated, eliminated]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hI j i]
  ring

theorem reciprocalEta_eq_scale_mode (n : ℕ) :
    reciprocalEta n = residueModeScale n * anchoredEvaluationCLM 1 (residueMode n) := by
  rw [reciprocalEta, innovation_eq_scale_mode, map_smul]
  rfl

theorem mixedSchurIncrement_eq_mode (n : ℕ) :
    mixedSchurIncrement n = modeAlpha n * anchoredEvaluationCLM 1 (residueMode n) := by
  rw [mixedSchurIncrement, reciprocalEta_eq_scale_mode, eta_eq_scale_alpha,
    sigma_eq_scale_sq]
  field_simp [ne_of_gt (residueModeScale_pos n)]
  <;> ring

theorem projection_firstCoordinate_schur_step (n : ℕ) :
    anchoredEvaluationCLM 1 (projection (n + 1)) =
      anchoredEvaluationCLM 1 (projection n) + mixedSchurIncrement n := by
  rw [projection_succ_mode, map_add, map_smul, mixedSchurIncrement_eq_mode]
  rfl

/-- Exact signed mixed Schur recurrence, including the Möbius increment. -/
theorem reciprocalCorrection_schur_step (n : ℕ) :
    reciprocalCorrection (n + 1) - reciprocalCorrection n =
      mixedSchurIncrement n +
        (ArithmeticFunction.moebius (n + 2) : ℝ) / ((n + 2 : ℕ) : ℝ) := by
  rw [reciprocalCorrection_eq_firstCoordinate, reciprocalCorrection_eq_firstCoordinate,
    projection_firstCoordinate_schur_step]
  have hm := mobiusReciprocalSum_succ (n + 1)
  simp only [Nat.add_assoc] at hm ⊢
  rw [hm]
  ring

/-- The exact Riesz vector for physical evaluation at one. -/
def firstEvaluationVector : ThresholdHilbert := (2 : ℝ) • paretoPointHilbert 0

theorem inner_firstEvaluationVector (f : ThresholdHilbert) :
    inner ℝ f firstEvaluationVector = anchoredEvaluationCLM 1 f := by
  rw [firstEvaluationVector, real_inner_smul_right, inner_firstPoint]
  ring

theorem firstEvaluationVector_norm_sq : ‖firstEvaluationVector‖ ^ 2 = (2 : ℝ) := by
  rw [firstEvaluationVector, norm_smul, Real.norm_eq_abs, mul_pow, firstPoint_norm_sq]
  norm_num

theorem modeEvaluation_sq_summable :
    Summable (fun j => (anchoredEvaluationCLM 1 (residueMode j)) ^ 2) := by
  simpa only [inner_firstEvaluationVector, Real.norm_eq_abs, sq_abs] using
    (Orthonormal.inner_products_summable firstEvaluationVector residueMode_orthonormal)

theorem reciprocalEta_sq_div_sigma (n : ℕ) :
    (reciprocalEta n)^2 / schurSigma n =
      (anchoredEvaluationCLM 1 (residueMode n))^2 := by
  rw [reciprocalEta_eq_scale_mode, sigma_eq_scale_sq]
  field_simp [ne_of_gt (residueModeScale_pos n)]
  <;> ring

/-- The exact two finite projection budgets for the squared Schur numerators. -/
theorem mixedSchur_prefix_budgets (n : ℕ) :
    (∑ j : Fin n, (reciprocalEta j.val)^2 / schurSigma j.val) = fullCapacity n ∧
    (∑ j : Fin n, (schurEta j.val)^2 / schurSigma j.val) = captured n := by
  constructor
  · simp only [reciprocalEta_sq_div_sigma]
    exact (fullCapacity_eq_mode_evaluation_sum n).symm
  · simp only [schur_gain_eq_mode_sq]
    have he := energy_eq_one_sub_mode_sum n
    have hc := error_eq_one_sub_captured n
    change energy n = _ at hc
    linarith

/-- Squared Cauchy--Schwarz, valid on every finite set (in particular every interval). -/
theorem mixedSchur_sum_abs_sq_le_budgets (s : Finset ℕ) :
    (∑ j ∈ s, |mixedSchurIncrement j|)^2 ≤
      (∑ j ∈ s, (reciprocalEta j)^2 / schurSigma j) *
        (∑ j ∈ s, (schurEta j)^2 / schurSigma j) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s
    (fun j => |modeAlpha j|) (fun j => |anchoredEvaluationCLM 1 (residueMode j)|)
  simp only [sq_abs, ← abs_mul] at h
  simp only [mixedSchurIncrement_eq_mode, reciprocalEta_sq_div_sigma,
    schur_gain_eq_mode_sq]
  calc
    (∑ j ∈ s, |modeAlpha j * anchoredEvaluationCLM 1 (residueMode j)|)^2 ≤
        (∑ j ∈ s, (modeAlpha j)^2) *
          (∑ j ∈ s, (anchoredEvaluationCLM 1 (residueMode j))^2) := h
    _ = _ := mul_comm _ _

/-- The absolute variation is at most sqrt(2), without any arithmetic sign input. -/
theorem mixedSchur_sum_abs_le_sqrt_two (s : Finset ℕ) :
    (∑ j ∈ s, |mixedSchurIncrement j|) ≤ Real.sqrt 2 := by
  have he : (∑ j ∈ s, (anchoredEvaluationCLM 1 (residueMode j))^2) ≤ 2 := by
    simpa only [inner_firstEvaluationVector, Real.norm_eq_abs, sq_abs,
      firstEvaluationVector_norm_sq] using
      (Orthonormal.sum_inner_products_le firstEvaluationVector residueMode_orthonormal
        (s := s))
  have ha : (∑ j ∈ s, (modeAlpha j)^2) ≤ 1 := by
    simpa only [modeAlpha, Real.norm_eq_abs, sq_abs, hilbertOne_norm_sq] using
      (Orthonormal.sum_inner_products_le hilbertOne residueMode_orthonormal (s := s))
  have hea := mixedSchur_sum_abs_sq_le_budgets s
  simp only [reciprocalEta_sq_div_sigma, schur_gain_eq_mode_sq] at hea
  have hen : 0 ≤ ∑ j ∈ s, (anchoredEvaluationCLM 1 (residueMode j))^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have han : 0 ≤ ∑ j ∈ s, (modeAlpha j)^2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hprod := mul_le_mul he ha han (by norm_num : (0 : ℝ) ≤ 2)
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsqrt0 := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

theorem mixedSchur_norm_summable : Summable (fun j => ‖mixedSchurIncrement j‖) := by
  apply Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    (modeAlpha_sq_hasSum.summable.add modeEvaluation_sq_summable)
  rw [mixedSchurIncrement_eq_mode]
  simp only [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|modeAlpha j| - |anchoredEvaluationCLM 1 (residueMode j)|),
    sq_abs (modeAlpha j), sq_abs (anchoredEvaluationCLM 1 (residueMode j))]

/-- The sum is the actual projection coordinate; it is not asserted equal to one. -/
theorem mixedSchur_hasSum : HasSum mixedSchurIncrement
    (anchoredEvaluationCLM 1 limitProjection) := by
  apply mixedSchur_norm_summable.of_norm.hasSum_iff_tendsto_nat.mpr
  have he (n : ℕ) : (∑ j ∈ Finset.range n, mixedSchurIncrement j) =
      anchoredEvaluationCLM 1 (projection n) := by
    simp only [mixedSchurIncrement_eq_mode]
    rw [← Fin.sum_univ_eq_sum_range]
    exact (projection_firstCoordinate_eq_mode_sum n).symm
  simpa only [Function.comp_def, he] using
    ((anchoredEvaluationCLM 1).continuous.tendsto limitProjection).comp projection_tendsto

theorem mixedSchur_tsum_eq_one_sub_residual :
    (∑' j, mixedSchurIncrement j) = 1 - hilbertSequence limitResidual 1 := by
  rw [mixedSchur_hasSum.tsum_eq, ← anchoredEvaluationCLM_apply 1 limitResidual]
  change anchoredEvaluationCLM 1 limitProjection =
    1 - anchoredEvaluationCLM 1 (hilbertOne - limitProjection)
  rw [map_sub]
  have hone : anchoredEvaluationCLM 1 hilbertOne = 1 := by
    rw [anchoredEvaluationCLM_apply, hilbertOne_sequence]
    norm_num [zeroAnchor]
  rw [hone]
  ring

theorem mixedSchur_abs_tsum_le_sqrt_two :
    (∑' j, |mixedSchurIncrement j|) ≤ Real.sqrt 2 := by
  exact tsum_le_of_sum_le' (Real.sqrt_nonneg 2) mixedSchur_sum_abs_le_sqrt_two

end RiemannResearch.RH.Pareto.CoefficientStabilization.GramMobiusCorrection
