import RiemannResearch.RH.ThresholdHilbertAdjoint

/-!
# The actual infinite weighted block projection

Source: independently developed from the weighted dilation definitions used
in Christian Noack's RH_Two_Seed_Threshold.tex (8 September 2026). The source
motivates the range-projection problem; the complete-H proofs use the
previously verified exact inner-product scaling and adjoint block law.

For every positive integer m, the existing complete-H dilation satisfies
T_m^* T_m = m I. Thus P_m = (1/m) T_m T_m^* is an actual bounded,
self-adjoint, idempotent operator, with an exact Pythagorean defect identity.
This is an infinite-space operator construction, not a supplied projection
provider. It makes no assertion about legal seed approximation or RH.
-/
namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

theorem hilbertDilation_inner (m : ℕ) (hm : 0 < m)
    (f g : ThresholdHilbert) :
    inner ℝ (hilbertDilation m hm f) (hilbertDilation m hm g) =
      (m : ℝ) * inner ℝ f g := by
  rw [hilbert_inner_weighted, hilbertDilation_sequence,
    hilbertDilation_sequence, hilbert_inner_weighted]
  exact paretoInner_dilation_of_square
    (hilbertSequence_square_summable f) (hilbertSequence_square_summable g)
    (hilbertSequence_zero f) m hm

theorem hilbertDilation_smul (m : ℕ) (hm : 0 < m) (c : ℝ)
    (f : ThresholdHilbert) :
    hilbertDilation m hm (c • f) = c • hilbertDilation m hm f :=
  (hilbertDilationLinear m hm).map_smul c f

/-- The exact adjoint-isometry identity on every vector in the complete H. -/
theorem hilbertDilationAdjoint_dilation (m : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) :
    hilbertDilationAdjoint m hm (hilbertDilation m hm f) = (m : ℝ) • f := by
  apply ext_inner_left ℝ
  intro g
  change inner ℝ g ((hilbertDilationContinuous m hm).adjoint
    (hilbertDilationContinuous m hm f)) = _
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (hilbertDilation m hm g) (hilbertDilation m hm f) = _
  rw [hilbertDilation_inner, real_inner_smul_right]

/-- Genuine bounded orthogonal projection onto the dilation range. -/
def hilbertBlockProjection (m : ℕ) (hm : 0 < m) :
    ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  (1 / (m : ℝ)) •
    ((hilbertDilationContinuous m hm).comp (hilbertDilationAdjoint m hm))

theorem hilbertBlockProjection_apply (m : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) :
    hilbertBlockProjection m hm f =
      (1 / (m : ℝ)) • hilbertDilation m hm (hilbertDilationAdjoint m hm f) := rfl

theorem hilbertBlockProjection_dilation (m : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) :
    hilbertBlockProjection m hm (hilbertDilation m hm f) =
      hilbertDilation m hm f := by
  rw [hilbertBlockProjection_apply, hilbertDilationAdjoint_dilation,
    hilbertDilation_smul, smul_smul]
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  simp [hm0]

theorem hilbertBlockProjection_idempotent (m : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) :
    hilbertBlockProjection m hm (hilbertBlockProjection m hm f) =
      hilbertBlockProjection m hm f := by
  rw [hilbertBlockProjection_apply m hm f, map_smul,
    hilbertBlockProjection_dilation]

theorem hilbertBlockProjection_inner (m : ℕ) (hm : 0 < m)
    (f g : ThresholdHilbert) :
    inner ℝ (hilbertBlockProjection m hm f) g =
      (1 / (m : ℝ)) *
        inner ℝ (hilbertDilationAdjoint m hm f) (hilbertDilationAdjoint m hm g) := by
  rw [hilbertBlockProjection_apply, real_inner_smul_left]
  congr 1
  exact (ContinuousLinearMap.adjoint_inner_right (hilbertDilationContinuous m hm)
    (hilbertDilationAdjoint m hm f) g).symm

theorem hilbertBlockProjection_symmetric (m : ℕ) (hm : 0 < m)
    (f g : ThresholdHilbert) :
    inner ℝ (hilbertBlockProjection m hm f) g =
      inner ℝ f (hilbertBlockProjection m hm g) := by
  calc
    _ = (1 / (m : ℝ)) *
        inner ℝ (hilbertDilationAdjoint m hm f) (hilbertDilationAdjoint m hm g) :=
      hilbertBlockProjection_inner m hm f g
    _ = (1 / (m : ℝ)) *
        inner ℝ (hilbertDilationAdjoint m hm g) (hilbertDilationAdjoint m hm f) := by
      rw [real_inner_comm]
    _ = inner ℝ (hilbertBlockProjection m hm g) f :=
      (hilbertBlockProjection_inner m hm g f).symm
    _ = _ := real_inner_comm _ _

theorem hilbertBlockProjection_orthogonal_defect (m : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) :
    inner ℝ (hilbertBlockProjection m hm f) (f - hilbertBlockProjection m hm f) = 0 := by
  rw [inner_sub_right]
  have h := hilbertBlockProjection_symmetric m hm (hilbertBlockProjection m hm f) f
  rw [hilbertBlockProjection_idempotent] at h
  exact sub_eq_zero.mpr h

/-- Exact retained energy plus exact discarded energy, with no inequality. -/
theorem hilbertBlockProjection_pythagoras (m : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) :
    ‖f‖^2 = ‖hilbertBlockProjection m hm f‖^2 +
      ‖f - hilbertBlockProjection m hm f‖^2 := by
  have h := hilbertBlockProjection_orthogonal_defect m hm f
  have he : f = hilbertBlockProjection m hm f +
      (f - hilbertBlockProjection m hm f) := by abel
  have h' : inner ℝ (f - hilbertBlockProjection m hm f)
      (hilbertBlockProjection m hm f) = 0 := by
    rw [real_inner_comm]
    exact h
  conv_lhs => rw [he]
  rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    inner_add_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, h, h']
  ring

/-- Physical projection coordinates vanish on the exceptional initial block. -/
theorem hilbertBlockProjection_head (m : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) (k : ℕ) (hk : k < m) :
    hilbertSequence (hilbertBlockProjection m hm f) k = 0 := by
  rw [hilbertBlockProjection_apply, hilbertSequence_smul, hilbertDilation_sequence]
  simp [dilation, Nat.div_eq_of_lt hk, hilbertSequence_zero]

/-- Each positive block is replaced by its exact Pareto-weighted mean.
The denominator w_(k/m)/m is precisely the total mass of that block. -/
theorem hilbertBlockProjection_coordinate (m : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) (k : ℕ) (hk : m ≤ k) :
    hilbertSequence (hilbertBlockProjection m hm f) k =
      (m : ℝ) / positiveWeight (k / m) *
        ∑ n ∈ Finset.Ico (m * (k / m)) (m * (k / m + 1)),
          positiveWeight n * hilbertSequence f n := by
  have hq : 0 < k / m := Nat.div_pos_iff.mpr ⟨hm, hk⟩
  rw [hilbertBlockProjection_apply, hilbertSequence_smul, hilbertDilation_sequence]
  change (1 / (m : ℝ)) * ((m : ℝ) *
    hilbertSequence (hilbertDilationAdjoint m hm f) (k / m)) = _
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  rw [← mul_assoc, one_div_mul_cancel hm0, one_mul]
  exact hilbertDilationAdjoint_coordinate m (k / m) hm hq f

/-- The actual block projection is contractive, as a consequence of exact energy splitting. -/
theorem hilbertBlockProjection_norm_le (m : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) :
    ‖hilbertBlockProjection m hm f‖ ≤ ‖f‖ := by
  nlinarith [hilbertBlockProjection_pythagoras m hm f,
    sq_nonneg ‖f - hilbertBlockProjection m hm f‖,
    norm_nonneg (hilbertBlockProjection m hm f), norm_nonneg f]

/-- Exact excess above the best approximation by a vector in the dilation range. -/
theorem hilbertBlockProjection_best_approximation (m : ℕ) (hm : 0 < m)
    (f g : ThresholdHilbert) :
    ‖f - hilbertDilation m hm g‖^2 =
      ‖f - hilbertBlockProjection m hm f‖^2 +
      ‖hilbertBlockProjection m hm f - hilbertDilation m hm g‖^2 := by
  have h := hilbertBlockProjection_pythagoras m hm (f - hilbertDilation m hm g)
  simp only [map_sub, hilbertBlockProjection_dilation] at h
  have he : f - hilbertDilation m hm g -
      (hilbertBlockProjection m hm f - hilbertDilation m hm g) =
        f - hilbertBlockProjection m hm f := by abel
  rw [he] at h
  linarith

end
end RiemannResearch.RH.Pareto
