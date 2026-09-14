import RiemannResearch.RH.BalancedArithmeticCuts
import RiemannResearch.RH.ParetoCoordinateEvaluation
import RiemannResearch.RH.DilationWaveletAlgebra
import RiemannResearch.Analysis.ContinuousBiorthogonalDeletion
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Continuous coordinates of the actual balanced dictionary

Source: RH_Minimal_Seeds_Canonical_Basis_and_Arithmetic_Charge_20260914.md,
Sections 4 and 5. Each coordinate is a finite sum of actual positive-coordinate
evaluations, so its continuity holds on the entire Pareto Hilbert space.
-/

namespace RiemannResearch.RH.Pareto

open scoped BigOperators
open RiemannResearch.RH.FiniteSeedComponentCharge

noncomputable section

structure BalancedArithmeticIndex where
  u : ℕ
  a : ℕ
  b : ℕ
  rough : IsTwoThreeRough u
  deriving DecidableEq

def balancedIndexValue (i : BalancedArithmeticIndex) : ℕ := 2 ^ i.a * 3 ^ i.b * i.u

theorem balancedIndexValue_pos (i : BalancedArithmeticIndex) : 0 < balancedIndexValue i := by
  have := i.rough.1
  unfold balancedIndexValue
  positivity

def balancedIndexHilbert (i : BalancedArithmeticIndex) : ThresholdHilbert :=
  if i.a ≤ i.b then
    (balancedIndexValue i : ℝ) • digitHilbert 2 (balancedIndexValue i)
      (by decide) (balancedIndexValue_pos i)
  else
    (balancedIndexValue i : ℝ) • digitHilbert 3 (balancedIndexValue i)
      (by decide) (balancedIndexValue_pos i)

theorem hilbertSequence_balancedIndex (i : BalancedArithmeticIndex) :
    hilbertSequence (balancedIndexHilbert i) = balancedResidueEdge i.u i.a i.b := by
  rw [balancedIndexHilbert, balancedResidueEdge_eq]
  split_ifs with h
  · change hilbertSequenceLinear
      ((balancedIndexValue i : ℝ) • digitHilbert 2 (balancedIndexValue i) _ _) = _
    rw [map_smul]
    change (balancedIndexValue i : ℝ) •
      hilbertSequence (digitHilbert 2 (balancedIndexValue i) _ _) = _
    rw [hilbertSequence_digitHilbert,
      digitSequence_eq_scaled_generator 2 _ (balancedIndexValue_pos i)]
    have hm : (balancedIndexValue i : ℝ) ≠ 0 := by
      exact_mod_cast ne_of_gt (balancedIndexValue_pos i)
    simp only [smul_smul, one_div, mul_inv_cancel₀ hm, one_smul] <;> rfl
  · change hilbertSequenceLinear
      ((balancedIndexValue i : ℝ) • digitHilbert 3 (balancedIndexValue i) _ _) = _
    rw [map_smul]
    change (balancedIndexValue i : ℝ) •
      hilbertSequence (digitHilbert 3 (balancedIndexValue i) _ _) = _
    rw [hilbertSequence_digitHilbert,
      digitSequence_eq_scaled_generator 3 _ (balancedIndexValue_pos i)]
    have hm : (balancedIndexValue i : ℝ) ≠ 0 := by
      exact_mod_cast ne_of_gt (balancedIndexValue_pos i)
    simp only [smul_smul, one_div, mul_inv_cancel₀ hm, one_smul] <;> rfl

def anchoredEvaluationCLM (n : ℕ) : ThresholdHilbert →L[ℝ] ℝ :=
  match n with
  | 0 => 0
  | k + 1 => physicalEvaluationCLM k

@[simp] theorem anchoredEvaluationCLM_apply (n : ℕ) (f : ThresholdHilbert) :
    anchoredEvaluationCLM n f = hilbertSequence f n := by
  cases n <;> simp [anchoredEvaluationCLM]

def mobiusDifferenceCLM (n : ℕ) : ThresholdHilbert →L[ℝ] ℝ :=
  ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℝ) •
    (anchoredEvaluationCLM d - anchoredEvaluationCLM (d - 1))

@[simp] theorem mobiusDifferenceCLM_apply (n : ℕ) (f : ThresholdHilbert) :
    mobiusDifferenceCLM n f = mobiusDifference n (hilbertSequence f) := by
  simp [mobiusDifferenceCLM, mobiusDifference, smul_eq_mul]

def balancedCoefficientCLM (i : BalancedArithmeticIndex) : ThresholdHilbert →L[ℝ] ℝ :=
  ∑ n ∈ balancedArithmeticCut i.u i.a i.b, (1 / (n : ℝ)) • mobiusDifferenceCLM n

@[simp] theorem balancedCoefficientCLM_apply (i : BalancedArithmeticIndex)
    (f : ThresholdHilbert) :
    balancedCoefficientCLM i f =
      componentCharge (balancedArithmeticCut i.u i.a i.b) (hilbertSequence f) := by
  simp [balancedCoefficientCLM, componentCharge, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- Fully proved continuous biorthogonality, with no coordinate-provider hypothesis. -/
theorem balancedCoefficientCLM_biorthogonal (i j : BalancedArithmeticIndex) :
    balancedCoefficientCLM i (balancedIndexHilbert j) = if i = j then 1 else 0 := by
  rw [balancedCoefficientCLM_apply, hilbertSequence_balancedIndex,
    balancedArithmeticCut_biorthogonal i.u i.a i.b j.u j.a j.b i.rough j.rough]
  have he : (i.u = j.u ∧ i.a = j.a ∧ i.b = j.b) ↔ i = j := by
    constructor
    · rintro ⟨hu, ha, hb⟩
      cases i
      cases j
      simp_all
    · rintro rfl
      exact ⟨rfl, rfl, rfl⟩
  simp only [he]

def balancedCoefficientTarget (i : BalancedArithmeticIndex) : ℝ :=
  componentSignal (balancedArithmeticCut i.u i.a i.b)

/-- The prescribed coefficient is the actual finite Möbius sum on the cut. -/
theorem balancedCoefficientCLM_one (i : BalancedArithmeticIndex) :
    balancedCoefficientCLM i hilbertOne = balancedCoefficientTarget i := by
  rw [balancedCoefficientCLM_apply, hilbertOne_sequence]
  exact componentCharge_target _ (balancedArithmeticCut_pos _ _ _ i.rough)

/-- The chosen original legal generators are linearly independent in the actual normed space. -/
theorem balancedIndexHilbert_linearIndependent : LinearIndependent ℝ balancedIndexHilbert := by
  exact RiemannResearch.Analysis.continuous_biorthogonal_linearIndependent
    balancedIndexHilbert balancedCoefficientCLM balancedCoefficientCLM_biorthogonal

/-- Every convergent legal coefficient array has the individually forced coordinate limit. -/
theorem balancedCoefficient_tendsto {ι : Type*} {l : Filter ι}
    (F : ι → ThresholdHilbert) (hF : Filter.Tendsto F l (nhds hilbertOne))
    (i : BalancedArithmeticIndex) :
    Filter.Tendsto (fun j => balancedCoefficientCLM i (F j)) l
      (nhds (balancedCoefficientTarget i)) := by
  rw [← balancedCoefficientCLM_one i]
  exact (balancedCoefficientCLM i).continuous.tendsto _ |>.comp hF

end
end RiemannResearch.RH.Pareto
