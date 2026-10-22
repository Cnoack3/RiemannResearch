import RiemannResearch.RH.ParetoPacketCoordinates
import Mathlib.Analysis.InnerProductSpace.l2Space
import RiemannResearch.Analysis.CoefficientShift

/-!
# Pareto tail averages and full Hilbert coordinates
Source: user-provided Pareto_Lean_Research_Connections_2026-09-23(1).md,
equations (7)--(16), for the normalization and statements.
Index n below denotes the physical tail beginning at n+1.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto

def fullTailFamily : ℕ → ThresholdHilbert
  | 0 => -hilbertOne
  | n + 1 => tailBasisHilbert n

theorem fullTailFamily_orthonormal : Orthonormal ℝ fullTailFamily := by
  apply orthonormal_iff_ite.mpr
  intro i j
  cases i with
  | zero =>
    cases j with
    | zero => simp [fullTailFamily, hilbertOne_norm_sq]
    | succ j =>
      simp only [fullTailFamily, inner_neg_left, Nat.zero_ne_add_one, if_false]
      rw [real_inner_comm, tailBasis_inner_one, neg_zero]
  | succ i =>
    cases j with
    | zero => simp [fullTailFamily, tailBasis_inner_one]
    | succ j => simpa only [fullTailFamily, Nat.add_right_cancel_iff] using tailBasis_inner i j

theorem fullTailFamily_orthogonal_eq_bot :
    (Submodule.span ℝ (Set.range fullTailFamily))ᗮ = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro f hf
  change f = 0
  have hp (n : ℕ) : inner ℝ f (fullTailFamily n) = 0 := by
    rw [real_inner_comm]
    exact hf _ (Submodule.subset_span ⟨n, rfl⟩)
  apply tailBasis_total
  · have h := hp 0
    simpa [fullTailFamily] using h
  · intro n
    exact hp (n + 1)

/-- The existing wavelets, augmented by the negative constant. -/
def fullTailBasis : HilbertBasis ℕ ℝ ThresholdHilbert :=
  HilbertBasis.mkOfOrthogonalEqBot fullTailFamily_orthonormal
    fullTailFamily_orthogonal_eq_bot

@[simp] theorem fullTailBasis_apply (n : ℕ) : fullTailBasis n = fullTailFamily n := by
  exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot
    fullTailFamily_orthonormal fullTailFamily_orthogonal_eq_bot) n

/-- The codomain is ordinary coefficient l2, the same lp carrier as ThresholdHilbert. -/
def hardyCoordinates : ThresholdHilbert ≃ₗᵢ[ℝ] ThresholdHilbert := fullTailBasis.repr

theorem hardyCoordinates_apply (f : ThresholdHilbert) (n : ℕ) :
    hardyCoordinates f n = inner ℝ f (fullTailFamily n) := by
  rw [hardyCoordinates, HilbertBasis.repr_apply_apply, fullTailBasis_apply, real_inner_comm]

/-- T_(n+1), defined by an exact mean-minus-head expression. -/
def tailAverage (f : ThresholdHilbert) (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) * (inner ℝ f hilbertOne -
    ∑ k ∈ Finset.range n, paretoWeight k * hilbertGibbsPhysical f k)

theorem weighted_physical_summable (f : ThresholdHilbert) :
    Summable (fun k => paretoWeight k * hilbertGibbsPhysical f k) := by
  apply Summable.of_norm
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (paretoWeight_pos _)] using
    hilbertGibbsPhysical_abs_summable f

/-- The full infinite tail is retained; its series is absolutely convergent. -/
theorem tailAverage_eq_tsum (f : ThresholdHilbert) (n : ℕ) :
    tailAverage f n =
      ((n : ℝ) + 1) * ∑' k, paretoWeight (k + n) * hilbertGibbsPhysical f (k + n) := by
  have hs := (weighted_physical_summable f).sum_add_tsum_nat_add n
  have hm : inner ℝ f hilbertOne =
      ∑' k, paretoWeight k * hilbertGibbsPhysical f k := by
    simp only [hilbertGibbs_inner_physical, hilbertGibbs_one_physical, mul_one]
  unfold tailAverage
  rw [hm, ← hs]
  ring

@[simp] theorem tailAverage_zero (f : ThresholdHilbert) :
    tailAverage f 0 = inner ℝ f hilbertOne := by simp [tailAverage]

theorem tailAverage_sub_succ (f : ThresholdHilbert) (n : ℕ) :
    tailAverage f n - tailAverage f (n + 1) = inner ℝ f (tailBasisHilbert n) := by
  rw [tailBasis_coefficient_formula]
  simp only [tailAverage, Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
  unfold paretoWeight
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

@[simp] theorem hardyCoordinates_zero (f : ThresholdHilbert) :
    hardyCoordinates f 0 = -tailAverage f 0 := by
  simp [hardyCoordinates_apply, fullTailFamily]

theorem hardyCoordinates_succ (f : ThresholdHilbert) (n : ℕ) :
    hardyCoordinates f (n + 1) = tailAverage f n - tailAverage f (n + 1) := by
  rw [hardyCoordinates_apply, fullTailFamily, tailAverage_sub_succ]

theorem hardyCoordinates_partial_sum (f : ThresholdHilbert) (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), hardyCoordinates f j) = -tailAverage f n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, hardyCoordinates_succ]
    ring

/-- Exact inverse coordinate relation at physical index n+1. -/
theorem hardyCoordinates_reconstruction (f : ThresholdHilbert) (n : ℕ) :
    hilbertGibbsPhysical f n =
      ((n : ℝ) + 1) * hardyCoordinates f (n + 1) -
        ∑ j ∈ Finset.range (n + 1), hardyCoordinates f j := by
  rw [hardyCoordinates_succ, hardyCoordinates_partial_sum,
    tailAverage_sub_succ, tailBasis_coefficient_formula]
  unfold tailAverage
  have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem tailAverage_parseval (f : ThresholdHilbert) :
    ‖f‖ ^ 2 = |tailAverage f 0| ^ 2 +
      ∑' n, |tailAverage f n - tailAverage f (n + 1)| ^ 2 := by
  have hs := hilbert_coordinate_square_summable (hardyCoordinates f)
  have he := hs.tsum_eq_zero_add
  rw [← hilbert_norm_sq, hardyCoordinates.norm_map, hardyCoordinates_zero] at he
  simpa only [hardyCoordinates_succ, neg_sq, sq_abs] using he

/-- The square-summability required by the local Dirichlet criterion. -/
def TailRegular (f : ThresholdHilbert) : Prop :=
  ∃ L : ℝ, Summable (fun n => |tailAverage f n - L| ^ 2)

/-- Coefficient form of A+(z-1)b, with b in the actual coefficient l2. -/
def LocalDirichlet (a : ThresholdHilbert) : Prop :=
  ∃ A : ℝ, ∃ b : ThresholdHilbert,
    a 0 = A - b 0 ∧ ∀ n, a (n + 1) = b n - b (n + 1)

theorem localDirichlet_iff_tailRegular (f : ThresholdHilbert) :
    LocalDirichlet (hardyCoordinates f) ↔ TailRegular f := by
  constructor
  · rintro ⟨A, b, h0, hb⟩
    have hpartial (n : ℕ) :
        (∑ j ∈ Finset.range (n + 1), hardyCoordinates f j) = A - b n := by
      induction n with
      | zero => simpa using h0
      | succ n ih =>
        rw [Finset.sum_range_succ, ih, hb]
        ring
    have htail (n : ℕ) : tailAverage f n - (-A) = b n := by
      have he := hpartial n
      rw [hardyCoordinates_partial_sum] at he
      linarith
    refine ⟨-A, ?_⟩
    simpa only [htail, sq_abs] using hilbert_coordinate_square_summable b
  · rintro ⟨L, hL⟩
    let b := RiemannResearch.Analysis.CoefficientShift.ofSquareSummable (fun n => tailAverage f n - L)
      (by simpa only [sq_abs] using hL)
    refine ⟨-L, b, ?_, ?_⟩
    · rw [hardyCoordinates_zero]
      change -tailAverage f 0 = -L - (tailAverage f 0 - L)
      ring
    · intro n
      rw [hardyCoordinates_succ]
      change tailAverage f n - tailAverage f (n + 1) =
        (tailAverage f n - L) - (tailAverage f (n + 1) - L)
      ring

end RiemannResearch.RH.Pareto
