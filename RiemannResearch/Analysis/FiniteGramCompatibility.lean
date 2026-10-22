import RiemannResearch.Analysis.FiniteHilbertGramMatrix

/-!
# Exact compatibility cost for a finite Gram optimizer

The normal-equation mismatch for arbitrary coefficients is measured in the
actual inverse Gram form. This identifies the full remainder in the existing
finite Hilbert completion, including all signed cross terms. The dual
certificate is attained and retains its complete nonnegative remainder.

Source: `RH/CRTPrimitiveTransferAudit20260929.md`, Section 6, for the
primitive/derivative compatibility question; the proofs use the existing
finite Hilbert Gram and capacity theorems.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.FiniteHilbertGram

open FiniteGramCapacity FiniteHilbertConstraints

variable {ι H : Type*} [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Signed normal-equation mismatch of the proposed coefficients. -/
def compatibilitySource (v : ι → H) (f : H) (c : ι → ℝ) : ι → ℝ :=
  cross v f - gram v c

/-- The complete inverse-Gram mismatch cost. -/
def compatibilityEnergy {v : ι → H} (hv : LinearIndependent ℝ v)
    (f : H) (c : ι → ℝ) : ℝ :=
  capacity hv (compatibilitySource v f c)

theorem compatibilitySource_eq_cross (v : ι → H) (f : H) (c : ι → ℝ) :
    compatibilitySource v f c = cross v (f - Fintype.linearCombination ℝ v c) := by
  funext i
  simp only [compatibilitySource, Pi.sub_apply, cross, inner_sub_right]
  rfl

/-- Applying the actual Gram inverse recovers precisely the coefficient
correction, without a bound on the inverse operator. -/
theorem inverseSource_compatibility {v : ι → H} (hv : LinearIndependent ℝ v)
    (f : H) (c : ι → ℝ) :
    inverseSource hv (compatibilitySource v f c) = inverseCoeff hv f - c := by
  apply gram_injective hv
  funext i
  rw [inverseSource_normal, map_sub]
  change cross v f i - gram v c i =
    inner ℝ (v i) (Fintype.linearCombination ℝ v (inverseCoeff hv f)) - gram v c i
  rw [inverseCoeff_normal]

theorem compatibilityEnergy_eq_norm_sq {v : ι → H} (hv : LinearIndependent ℝ v)
    (f : H) (c : ι → ℝ) :
    compatibilityEnergy hv f c =
      ‖Fintype.linearCombination ℝ v (inverseCoeff hv f - c)‖ ^ 2 := by
  rw [compatibilityEnergy, capacity_eq_norm_sq]
  change ‖Fintype.linearCombination ℝ v
    (inverseSource hv (compatibilitySource v f c))‖ ^ 2 = _
  rw [inverseSource_compatibility]

theorem compatibilityEnergy_nonneg {v : ι → H} (hv : LinearIndependent ℝ v)
    (f : H) (c : ι → ℝ) : 0 ≤ compatibilityEnergy hv f c :=
  capacity_nonneg hv _

/-- The actual error is the attained optimal error plus the full
inverse-Gram mismatch energy. -/
theorem residual_compatibility {v : ι → H} (hv : LinearIndependent ℝ v)
    (f : H) (c : ι → ℝ) :
    ‖f - Fintype.linearCombination ℝ v c‖ ^ 2 =
      ‖f - Fintype.linearCombination ℝ v (inverseCoeff hv f)‖ ^ 2 +
        compatibilityEnergy hv f c := by
  rw [residual_completion hv f c, compatibilityEnergy_eq_norm_sq]
  congr 1
  rw [map_sub, map_sub, norm_sub_rev]

theorem compatibilityEnergy_zero_iff {v : ι → H} (hv : LinearIndependent ℝ v)
    (f : H) (c : ι → ℝ) :
    compatibilityEnergy hv f c = 0 ↔ c = inverseCoeff hv f := by
  rw [compatibilityEnergy_eq_norm_sq]
  constructor
  · intro hz
    have hn : ‖Fintype.linearCombination ℝ v (inverseCoeff hv f - c)‖ = 0 := by
      nlinarith [norm_nonneg (Fintype.linearCombination ℝ v (inverseCoeff hv f - c))]
    have he : inverseCoeff hv f - c = 0 := by
      apply hv.fintypeLinearCombination_injective
      simpa only [map_zero] using norm_eq_zero.mp hn
    exact (sub_eq_zero.mp he).symm
  · rintro rfl
    simp

/-- Every trial direction gives a rigorous lower certificate for mismatch;
the difference from the exact answer is a complete square. -/
theorem compatibilityEnergy_dual_completion {v : ι → H}
    (hv : LinearIndependent ℝ v) (f : H) (c a : ι → ℝ) :
    2 * (∑ i, a i * compatibilitySource v f c i) -
        ‖Fintype.linearCombination ℝ v a‖ ^ 2 =
      compatibilityEnergy hv f c -
        ‖Fintype.linearCombination ℝ v (inverseCoeff hv f - c) -
          Fintype.linearCombination ℝ v a‖ ^ 2 := by
  have h := capacity_completion hv (compatibilitySource v f c) a
  change _ = compatibilityEnergy hv f c -
    ‖Fintype.linearCombination ℝ v
      (inverseSource hv (compatibilitySource v f c)) -
      Fintype.linearCombination ℝ v a‖ ^ 2 at h
  rw [inverseSource_compatibility] at h
  exact h

/-- The inverse-Gram compatibility energy is an attained dual supremum. -/
theorem compatibilityEnergy_isGreatest {v : ι → H} (hv : LinearIndependent ℝ v)
    (f : H) (c : ι → ℝ) :
    IsGreatest {t : ℝ | ∃ a : ι → ℝ,
      2 * (∑ i, a i * compatibilitySource v f c i) -
        ‖Fintype.linearCombination ℝ v a‖ ^ 2 = t}
      (compatibilityEnergy hv f c) := by
  constructor
  · refine ⟨inverseCoeff hv f - c, ?_⟩
    rw [compatibilityEnergy_dual_completion hv]
    simp
  · rintro t ⟨a, rfl⟩
    exact quadratic_le_capacity hv _ a

section Matrix
variable [DecidableEq ι]

omit [DecidableEq ι] in
theorem compatibilitySource_eq_matrix (v : ι → H) (f : H) (c : ι → ℝ) :
    compatibilitySource v f c = cross v f - (gramMatrix v).mulVec c := by
  rw [gramMatrix_mulVec]
  rfl

theorem compatibilityEnergy_eq_matrix {v : ι → H} (hv : LinearIndependent ℝ v)
    (f : H) (c : ι → ℝ) :
    compatibilityEnergy hv f c =
      dotProduct (compatibilitySource v f c)
        ((gramMatrix v)⁻¹.mulVec (compatibilitySource v f c)) := by
  rw [gramMatrix_inverseSource hv]
  simp only [compatibilityEnergy, capacity, dotProduct, mul_comm]

/-- Matrix form `error = optimal error + hᵀ D⁻¹ h`, with
`h = d - D c` and `D` the actual Hilbert Gram matrix. -/
theorem residual_compatibility_matrix {v : ι → H} (hv : LinearIndependent ℝ v)
    (f : H) (c : ι → ℝ) :
    ‖f - Fintype.linearCombination ℝ v c‖ ^ 2 =
      ‖f - Fintype.linearCombination ℝ v ((gramMatrix v)⁻¹.mulVec (cross v f))‖ ^ 2 +
      dotProduct (cross v f - (gramMatrix v).mulVec c)
        ((gramMatrix v)⁻¹.mulVec (cross v f - (gramMatrix v).mulVec c)) := by
  rw [residual_compatibility hv f c, compatibilityEnergy_eq_matrix,
    compatibilitySource_eq_matrix, gramMatrix_inverseSource hv]
  rw [gramMatrix_inverseSource hv]
  rfl

end Matrix
end RiemannResearch.Analysis.FiniteHilbertGram
