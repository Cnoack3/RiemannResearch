import RiemannResearch.RH.DyadicStepGram
import RiemannResearch.RH.DyadicBoundaryCompleteness
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Parseval coordinates for the completed physical dyadic quotient

Source: user-provided DyadicRegularizedVerificationContinuation20260910 (2).md,
September 10, 2026, boundary-completeness continuation. This supplies the
infinite boundary-coordinate norm identity; it does not identify the separate
fold/martingale expression or supply arithmetic estimates or legal witnesses.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

local instance : CompleteSpace dyadicQuotientSubspace := by
  let : IsClosed (dyadicQuotientSubspace : Set ThresholdHilbert) :=
    Submodule.isClosed_orthogonal _
  infer_instance

/-- The mean followed by the normalized physical projected boundaries. -/
def dyadicBoundaryOrthonormalVector : ℕ → dyadicQuotientSubspace
  | 0 => ⟨hilbertOne, by
      rw [← dyadicQuotientProjection_one]
      exact dyadicQuotientProjection_mem _⟩
  | n+1 => ⟨(2 : ℝ) • dyadicQuotientProjection
      (dyadicStepBoundary (n+1) (by positivity)),
      dyadicQuotientSubspace.smul_mem _ (dyadicQuotientProjection_mem _)⟩

theorem dyadicBoundaryOrthonormalVector_orthonormal :
    Orthonormal ℝ dyadicBoundaryOrthonormalVector := by
  rw [orthonormal_iff_ite]
  intro i j
  cases i with
  | zero =>
    cases j with
    | zero =>
      change inner ℝ hilbertOne hilbertOne = _
      rw [real_inner_self_eq_norm_sq, hilbertOne_norm_sq]
      simp
    | succ j =>
      change inner ℝ hilbertOne ((2 : ℝ) • dyadicQuotientProjection
        (dyadicStepBoundary (j+1) (by positivity))) = _
      rw [real_inner_smul_right, real_inner_comm,
        dyadicProjectedBoundary_inner_one]
      simp
  | succ i =>
    cases j with
    | zero =>
      change inner ℝ ((2 : ℝ) • dyadicQuotientProjection
        (dyadicStepBoundary (i+1) (by positivity))) hilbertOne = _
      rw [real_inner_smul_left, dyadicProjectedBoundary_inner_one]
      simp
    | succ j =>
      change inner ℝ ((2 : ℝ) • dyadicQuotientProjection
        (dyadicStepBoundary (i+1) (by positivity)))
        ((2 : ℝ) • dyadicQuotientProjection
        (dyadicStepBoundary (j+1) (by positivity))) = _
      rw [real_inner_smul_left, real_inner_smul_right]
      by_cases h : i = j
      · subst j
        rw [real_inner_self_eq_norm_sq, dyadicProjectedBoundary_norm_sq]
        norm_num
      · rw [dyadicProjectedBoundary_inner_boundary (i+1) (j+1)
          (by positivity) (by positivity) (by omega)]
        simp [h]

theorem dyadicBoundaryOrthonormalVector_orthogonal_eq_bot :
    (Submodule.span ℝ (Set.range dyadicBoundaryOrthonormalVector))ᗮ = ⊥ := by
  apply le_antisymm
  · intro f hf
    change f = 0
    apply Subtype.ext
    change (f : ThresholdHilbert) = 0
    apply dyadicQuotient_eq_zero_of_boundary_inner (f : ThresholdHilbert) f.property
    · have h := (Submodule.mem_orthogonal _ _).mp hf
        (dyadicBoundaryOrthonormalVector 0) (Submodule.subset_span ⟨0, rfl⟩)
      exact h
    · intro l hl
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hl)
      have h := (Submodule.mem_orthogonal _ _).mp hf
        (dyadicBoundaryOrthonormalVector (n+1))
        (Submodule.subset_span ⟨n+1, rfl⟩)
      change inner ℝ ((2 : ℝ) • dyadicQuotientProjection
        (dyadicStepBoundary (n+1) (by positivity))) (f : ThresholdHilbert) = 0 at h
      rw [real_inner_smul_left] at h
      linarith
  · exact bot_le

/-- A complete Hilbert basis built from the actual weighted boundaries. -/
def dyadicBoundaryHilbertBasis : HilbertBasis ℕ ℝ dyadicQuotientSubspace :=
  HilbertBasis.mkOfOrthogonalEqBot dyadicBoundaryOrthonormalVector_orthonormal
    dyadicBoundaryOrthonormalVector_orthogonal_eq_bot

theorem dyadicBoundaryHilbertBasis_apply (n : ℕ) :
    dyadicBoundaryHilbertBasis n = dyadicBoundaryOrthonormalVector n := by
  exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) n

/-- The actual quotient projection viewed in its closed range. -/
def dyadicQuotientVector (f : ThresholdHilbert) : dyadicQuotientSubspace :=
  ⟨dyadicQuotientProjection f, dyadicQuotientProjection_mem f⟩

theorem dyadicBoundaryHilbertBasis_inner_zero (f : ThresholdHilbert) :
    inner ℝ (dyadicBoundaryHilbertBasis 0) (dyadicQuotientVector f) =
      inner ℝ hilbertOne f := by
  rw [dyadicBoundaryHilbertBasis_apply]
  change inner ℝ hilbertOne (dyadicQuotientProjection f) = _
  rw [← dyadicQuotientProjection_inner, dyadicQuotientProjection_one]

theorem dyadicBoundaryHilbertBasis_inner_succ (f : ThresholdHilbert) (n : ℕ) :
    inner ℝ (dyadicBoundaryHilbertBasis (n+1)) (dyadicQuotientVector f) =
      2 * inner ℝ (dyadicQuotientProjection
        (dyadicStepBoundary (n+1) (by positivity))) f := by
  rw [dyadicBoundaryHilbertBasis_apply]
  change inner ℝ ((2 : ℝ) • dyadicQuotientProjection
    (dyadicStepBoundary (n+1) (by positivity))) (dyadicQuotientProjection f) = _
  rw [real_inner_smul_left, ← dyadicQuotientProjection_inner,
    dyadicQuotientProjection_idempotent]

/-- The complete boundary pairing series converges for arbitrary physical
vectors, so the following infinite Gram identity is an actual convergent sum. -/
theorem dyadicBoundary_mixed_pairings_summable (f g : ThresholdHilbert) :
    Summable (fun n : ℕ => 4 *
      inner ℝ (dyadicQuotientProjection (dyadicStepBoundary (n+1) (by positivity))) f *
      inner ℝ (dyadicQuotientProjection (dyadicStepBoundary (n+1) (by positivity))) g) := by
  have h := (dyadicBoundaryHilbertBasis.hasSum_inner_mul_inner
    (dyadicQuotientVector f) (dyadicQuotientVector g)).summable.comp_injective
      Nat.succ_injective
  apply h.congr
  intro n
  change inner ℝ (dyadicQuotientVector f) (dyadicBoundaryHilbertBasis (n+1)) *
    inner ℝ (dyadicBoundaryHilbertBasis (n+1)) (dyadicQuotientVector g) = _
  have hc : inner ℝ (dyadicQuotientVector f) (dyadicBoundaryHilbertBasis (n+1)) =
      inner ℝ (dyadicBoundaryHilbertBasis (n+1)) (dyadicQuotientVector f) :=
    real_inner_comm _ _
  rw [hc, dyadicBoundaryHilbertBasis_inner_succ,
    dyadicBoundaryHilbertBasis_inner_succ]
  ring

/-- Parseval in the completed quotient, including every signed mixed pairing. -/
theorem dyadicBoundary_parseval_inner (f g : ThresholdHilbert) :
    inner ℝ (dyadicQuotientProjection f) (dyadicQuotientProjection g) =
      inner ℝ hilbertOne f * inner ℝ hilbertOne g +
      ∑' n : ℕ, 4 *
        inner ℝ (dyadicQuotientProjection (dyadicStepBoundary (n+1) (by positivity))) f *
        inner ℝ (dyadicQuotientProjection (dyadicStepBoundary (n+1) (by positivity))) g := by
  have hs := dyadicBoundaryHilbertBasis.hasSum_inner_mul_inner
    (dyadicQuotientVector f) (dyadicQuotientVector g)
  have hcomm (n : ℕ) :
      inner ℝ (dyadicQuotientVector f) (dyadicBoundaryHilbertBasis n) =
      inner ℝ (dyadicBoundaryHilbertBasis n) (dyadicQuotientVector f) :=
    real_inner_comm _ _
  change inner ℝ (dyadicQuotientVector f) (dyadicQuotientVector g) = _
  rw [← hs.tsum_eq, hs.summable.tsum_eq_zero_add]
  rw [hcomm 0,
    dyadicBoundaryHilbertBasis_inner_zero, dyadicBoundaryHilbertBasis_inner_zero]
  congr 1
  apply tsum_congr
  intro n
  rw [hcomm (n+1),
    dyadicBoundaryHilbertBasis_inner_succ, dyadicBoundaryHilbertBasis_inner_succ]
  ring

/-- The norm formula for every physical vector; no summability is assumed. -/
theorem dyadicBoundary_parseval_norm_sq (f : ThresholdHilbert) :
    ‖dyadicQuotientProjection f‖^2 = (inner ℝ hilbertOne f)^2 +
      ∑' n : ℕ, 4 * (inner ℝ (dyadicQuotientProjection
        (dyadicStepBoundary (n+1) (by positivity))) f)^2 := by
  rw [← real_inner_self_eq_norm_sq, dyadicBoundary_parseval_inner]
  congr 1
  · ring
  · apply tsum_congr
    intro n
    ring

/-- The full physical approximation error: mean defect, all quotient details,
and the complementary energy. This is an equality for every physical vector. -/
theorem dyadicBoundary_full_error_sq (f : ThresholdHilbert) :
    ‖hilbertOne - f‖^2 = (1 - inner ℝ hilbertOne f)^2 +
      (∑' n : ℕ, 4 * (inner ℝ (dyadicQuotientProjection
        (dyadicStepBoundary (n+1) (by positivity))) f)^2) +
      ‖f - dyadicQuotientProjection f‖^2 := by
  have hp := dyadicQuotientProjection_pythagoras (hilbertOne - f)
  have hparse := dyadicBoundary_parseval_norm_sq (hilbertOne - f)
  have hmean : inner ℝ hilbertOne (hilbertOne - f) =
      1 - inner ℝ hilbertOne f := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq, hilbertOne_norm_sq]
  have hb (n : ℕ) : inner ℝ (dyadicQuotientProjection
        (dyadicStepBoundary (n+1) (by positivity))) (hilbertOne - f) =
      -inner ℝ (dyadicQuotientProjection
        (dyadicStepBoundary (n+1) (by positivity))) f := by
    rw [inner_sub_right, dyadicProjectedBoundary_inner_one, zero_sub]
  rw [hparse, hmean] at hp
  simp_rw [hb, neg_sq] at hp
  rw [map_sub, dyadicQuotientProjection_one] at hp
  have he : hilbertOne - f - (hilbertOne - dyadicQuotientProjection f) =
      -(f - dyadicQuotientProjection f) := by abel
  simpa only [he, norm_neg] using hp

end
end RiemannResearch.RH.Pareto
