import RiemannResearch.RH.ParetoInverseGramDual
import Mathlib.Tactic.Linarith

/-!
# Complete Pareto inverse-Gram defect and physical-dual transfer

Source: user-provided `Prime_Phases_Agenda_Proof_Attempts.tex`, section
"Full inverse bounds and an exact controlled-transfer test".
Every stage uses the actual complete dictionary `g_2,...,g_(n+1)`.
The approximant's support-error estimate is deliberately a separate obligation;
none of the statements below assumes RH or vanishing inverse saturation.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- The full physical-dual combination on the first `n` conductors. -/
def physicalDualCombination (n : ℕ) (a : Fin n → ℝ) : ThresholdHilbert :=
  ∑ i, a i • coefficientDual i.val

/-- Actual residual against the complete legal dictionary, including composites. -/
def completeResidual (n : ℕ) (x : ThresholdHilbert) : ThresholdHilbert :=
  x - (finiteSpace n).starProjection x

/-- Quadratic form of the complete physical Gram minus actual inverse Gram. -/
def physicalInverseDefect (n : ℕ) (a : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, (a i * a j) *
    (inner ℝ (coefficientDual i.val) (coefficientDual j.val) -
      residueInverseEntry n i j)

theorem residueInverseEntry_diagonal_nonneg (n : ℕ) (i : Fin n) :
    0 ≤ residueInverseEntry n i i := by
  rw [residueInverseEntry_projection, real_inner_self_eq_norm_sq]
  positivity

theorem residueInverseEntry_diagonal_le_physical (n : ℕ) (i : Fin n) :
    residueInverseEntry n i i ≤ ‖coefficientDual i.val‖ ^ 2 := by
  have h := residueInverseEntry_diagonal n i
  nlinarith [sq_nonneg
    ‖coefficientDual i.val - (finiteSpace n).starProjection (coefficientDual i.val)‖]

theorem physicalInverseDefect_eq_residual_sq (n : ℕ) (a : Fin n → ℝ) :
    physicalInverseDefect n a =
      ‖completeResidual n (physicalDualCombination n a)‖ ^ 2 := by
  have hr : completeResidual n (physicalDualCombination n a) =
      ∑ i, a i • completeResidual n (coefficientDual i.val) := by
    simp only [completeResidual, physicalDualCombination, map_sum, map_smul,
      smul_sub, Finset.sum_sub_distrib]
  rw [hr, ← real_inner_self_eq_norm_sq, sum_inner]
  simp_rw [real_inner_smul_left, inner_sum, real_inner_smul_right, Finset.mul_sum]
  unfold physicalInverseDefect completeResidual
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [residueInverseEntry_residual]
  ring

/-- Positive-semidefinite comparison in quadratic-form form: `G⁻¹ ≤ U`. -/
theorem physicalInverseDefect_nonneg (n : ℕ) (a : Fin n → ℝ) :
    0 ≤ physicalInverseDefect n a := by
  rw [physicalInverseDefect_eq_residual_sq]
  positivity

theorem completeResidual_norm_le (n : ℕ) (x : ThresholdHilbert) :
    ‖completeResidual n x‖ ≤ ‖x‖ := by
  have ho : inner ℝ (x - (finiteSpace n).starProjection x)
      ((finiteSpace n).starProjection x) = 0 := by
    rw [real_inner_comm]
    exact ((finiteSpace n).mem_orthogonal _).mp
      (Submodule.sub_starProjection_mem_orthogonal x) _
      ((finiteSpace n).starProjection_apply_mem _)
  rw [inner_sub_left, real_inner_self_eq_norm_sq] at ho
  have he : ‖completeResidual n x‖ ^ 2 +
      ‖(finiteSpace n).starProjection x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [completeResidual, norm_sub_sq_real]
    linarith
  nlinarith [sq_nonneg ‖(finiteSpace n).starProjection x‖,
    norm_nonneg (completeResidual n x), norm_nonneg x]

theorem completeResidual_norm_triangle (n : ℕ) (x y : ThresholdHilbert) :
    ‖completeResidual n x‖ ≤ ‖x - y‖ + ‖completeResidual n y‖ := by
  have he : completeResidual n x =
      completeResidual n (x - y) + completeResidual n y := by
    simp only [completeResidual, map_sub]
    abel
  calc
    ‖completeResidual n x‖ =
        ‖completeResidual n (x - y) + completeResidual n y‖ := by rw [he]
    _ ≤ ‖completeResidual n (x - y)‖ + ‖completeResidual n y‖ := norm_add_le _ _
    _ ≤ ‖x - y‖ + ‖completeResidual n y‖ :=
      add_le_add (completeResidual_norm_le n (x - y)) le_rfl

/-- Exact transfer error applies to every actual physical-dual approximant. -/
theorem completeResidual_norm_transfer (n : ℕ) (x y : ThresholdHilbert) :
    |‖completeResidual n x‖ - ‖completeResidual n y‖| ≤ ‖x - y‖ := by
  have hxy := completeResidual_norm_triangle n x y
  have hyx := completeResidual_norm_triangle n y x
  rw [norm_sub_rev] at hyx
  rw [abs_le]
  constructor <;> linarith

/-- An unconditional finite-cutoff certificate, with the complete inverse. -/
theorem physicalInverseDefect_support_transfer (n : ℕ) (a : Fin n → ℝ) :
    |‖completeResidual n hilbertOne‖ -
      Real.sqrt (physicalInverseDefect n a)| ≤
      ‖hilbertOne - physicalDualCombination n a‖ := by
  rw [physicalInverseDefect_eq_residual_sq, Real.sqrt_sq
    (norm_nonneg (completeResidual n (physicalDualCombination n a)))]
  exact completeResidual_norm_transfer n hilbertOne (physicalDualCombination n a)

/-- The small-support block is taken only after the full stage-`n` inverse. -/
def physicalPrefixInverseDefect (k n : ℕ) (hkn : k ≤ n) (a : Fin k → ℝ) : ℝ :=
  ∑ i, ∑ j, (a i * a j) *
    (inner ℝ (coefficientDual i.val) (coefficientDual j.val) -
      residueInverseEntry n ⟨i.val, Nat.lt_of_lt_of_le i.isLt hkn⟩
        ⟨j.val, Nat.lt_of_lt_of_le j.isLt hkn⟩)

theorem physicalPrefixInverseDefect_eq_residual_sq
    (k n : ℕ) (hkn : k ≤ n) (a : Fin k → ℝ) :
    physicalPrefixInverseDefect k n hkn a =
      ‖completeResidual n (physicalDualCombination k a)‖ ^ 2 := by
  have hr : completeResidual n (physicalDualCombination k a) =
      ∑ i, a i • completeResidual n (coefficientDual i.val) := by
    simp only [completeResidual, physicalDualCombination, map_sum, map_smul,
      smul_sub, Finset.sum_sub_distrib]
  rw [hr, ← real_inner_self_eq_norm_sq, sum_inner]
  simp_rw [real_inner_smul_left, inner_sum, real_inner_smul_right, Finset.mul_sum]
  unfold physicalPrefixInverseDefect completeResidual
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hd := residueInverseEntry_residual n
    (⟨i.val, Nat.lt_of_lt_of_le i.isLt hkn⟩ : Fin n)
    (⟨j.val, Nat.lt_of_lt_of_le j.isLt hkn⟩ : Fin n)
  simp only at hd
  rw [hd]
  ring

theorem physicalPrefixInverseDefect_nonneg
    (k n : ℕ) (hkn : k ≤ n) (a : Fin k → ℝ) :
    0 ≤ physicalPrefixInverseDefect k n hkn a := by
  rw [physicalPrefixInverseDefect_eq_residual_sq]
  positivity

/-- Complete screened transfer with the exact small-support inverse defect. -/
theorem physicalPrefixInverseDefect_support_transfer
    (k n : ℕ) (hkn : k ≤ n) (a : Fin k → ℝ) :
    |‖completeResidual n hilbertOne‖ -
      Real.sqrt (physicalPrefixInverseDefect k n hkn a)| ≤
      ‖hilbertOne - physicalDualCombination k a‖ := by
  rw [physicalPrefixInverseDefect_eq_residual_sq, Real.sqrt_sq
    (norm_nonneg (completeResidual n (physicalDualCombination k a)))]
  exact completeResidual_norm_transfer n hilbertOne (physicalDualCombination k a)

theorem physicalPrefixInverseDefect_finite_certificate
    (k n : ℕ) (hkn : k ≤ n) (a : Fin k → ℝ) :
    ‖completeResidual n hilbertOne‖ ^ 2 ≤
      (‖hilbertOne - physicalDualCombination k a‖ +
        Real.sqrt (physicalPrefixInverseDefect k n hkn a)) ^ 2 := by
  have h := (abs_le.mp
    (physicalPrefixInverseDefect_support_transfer k n hkn a)).2
  have hs := Real.sqrt_nonneg (physicalPrefixInverseDefect k n hkn a)
  have he := norm_nonneg (hilbertOne - physicalDualCombination k a)
  have hr := norm_nonneg (completeResidual n hilbertOne)
  nlinarith

/-- The exact physical coefficient extractor, with the original Möbius sign. -/
theorem inner_coefficientDual_eq_coefficientCLM (i : ℕ) (x : ThresholdHilbert) :
    inner ℝ x (coefficientDual i) = coefficientCLM (i + 2) x := by
  rw [real_inner_comm]
  simp only [coefficientDual, inner_neg_left, mobiusRieszHilbert_inner,
    coefficientCLM, neg_apply]

theorem completeResidual_inner_target (n : ℕ) (x : ThresholdHilbert) :
    inner ℝ (completeResidual n x) x = ‖completeResidual n x‖ ^ 2 := by
  have ho : inner ℝ (completeResidual n x) ((finiteSpace n).starProjection x) = 0 := by
    rw [real_inner_comm]
    exact ((finiteSpace n).mem_orthogonal _).mp
      (Submodule.sub_starProjection_mem_orthogonal x) _
      ((finiteSpace n).starProjection_apply_mem _)
  have hx : x = completeResidual n x + (finiteSpace n).starProjection x := by
    simp [completeResidual]
  calc
    inner ℝ (completeResidual n x) x =
        inner ℝ (completeResidual n x)
          (completeResidual n x + (finiteSpace n).starProjection x) := by rw [← hx]
    _ = ‖completeResidual n x‖ ^ 2 := by
      rw [inner_add_right, real_inner_self_eq_norm_sq, ho, add_zero]

def physicalSignedCharge (k n : ℕ) (a : Fin k → ℝ) : ℝ :=
  ∑ i, a i *
    (coefficient n (i.val + 2) + (ArithmeticFunction.moebius (i.val + 2) : ℝ))

/-- Exact signed equality, retaining the residual pairing before estimation. -/
theorem physicalSignedCharge_exact (k n : ℕ) (a : Fin k → ℝ) :
    ‖completeResidual n hilbertOne‖ ^ 2 + physicalSignedCharge k n a =
      inner ℝ (completeResidual n hilbertOne)
        (hilbertOne - physicalDualCombination k a) := by
  have hc (i : Fin k) :
      inner ℝ (completeResidual n hilbertOne) (coefficientDual i.val) =
        -(coefficient n (i.val + 2) +
          (ArithmeticFunction.moebius (i.val + 2) : ℝ)) := by
    rw [inner_coefficientDual_eq_coefficientCLM, completeResidual, map_sub]
    change -(mobiusDifferenceCLM (i.val + 2) hilbertOne) -
      coefficient n (i.val + 2) = _
    rw [mobius_coordinate_one (i.val + 2) (by omega)]
    ring
  have hp : inner ℝ (completeResidual n hilbertOne) (physicalDualCombination k a) =
      -physicalSignedCharge k n a := by
    simp only [physicalDualCombination, inner_sum, real_inner_smul_right, hc,
      physicalSignedCharge]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [inner_sub_right, completeResidual_inner_target, hp]
  ring

theorem physicalSignedCharge_error_bound (k n : ℕ) (a : Fin k → ℝ) :
    |‖completeResidual n hilbertOne‖ ^ 2 + physicalSignedCharge k n a| ≤
      ‖completeResidual n hilbertOne‖ * ‖hilbertOne - physicalDualCombination k a‖ := by
  rw [physicalSignedCharge_exact]
  exact abs_real_inner_le_norm _ _

end RiemannResearch.RH.Pareto.CoefficientStabilization
