import RiemannResearch.RH.ParetoHilbertPhysical
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# An explicit orthonormal system for the mean-zero Pareto space

Source: elementary tail-martingale construction developed for the Gibbs
spectral-gap formalization. The vectors are actual members of the existing
weighted Hilbert space. Their physical coordinates are n+1 at n, -1 after
n, and zero before n (indices here begin at zero).
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

def paretoPointSequence (n k : ℕ) : ℝ := if k = n+1 then 1 else 0

private theorem paretoPoint_square_summable (n : ℕ) :
    Summable (fun k => positiveWeight k * paretoPointSequence n k ^ 2) := by
  apply weighted_summable_of_bounded (C := 1)
  intro k
  simp only [paretoPointSequence]
  split_ifs <;> norm_num

def paretoPointHilbert (n : ℕ) : ThresholdHilbert :=
  sequenceHilbert (paretoPointSequence n) (paretoPoint_square_summable n)

@[simp] theorem hilbertSequence_paretoPoint (n : ℕ) :
    hilbertSequence (paretoPointHilbert n) = paretoPointSequence n := by
  apply hilbertSequence_sequenceHilbert
  simp [paretoPointSequence]

@[simp] theorem hilbertGibbsPhysical_paretoPoint (n k : ℕ) :
    hilbertGibbsPhysical (paretoPointHilbert n) k = if k = n then 1 else 0 := by
  rw [hilbertGibbsPhysical_eq, hilbertSequence_paretoPoint]
  simp [paretoPointSequence]

theorem inner_paretoPoint (f : ThresholdHilbert) (n : ℕ) :
    inner ℝ f (paretoPointHilbert n) = paretoWeight n * hilbertGibbsPhysical f n := by
  rw [hilbertGibbs_inner_physical]
  simp only [hilbertGibbsPhysical_paretoPoint, mul_ite, mul_one, mul_zero]
  simp

theorem paretoPoint_inner_one (n : ℕ) :
    inner ℝ (paretoPointHilbert n) hilbertOne = paretoWeight n := by
  rw [real_inner_comm, inner_paretoPoint, hilbertGibbs_one_physical]
  simp

/-- A finite expression for the actual tail vector; the constant term retains
its complete infinite tail. -/
def tailBasisHilbert (n : ℕ) : ThresholdHilbert :=
  ((n : ℝ)+2) • paretoPointHilbert n +
    (∑ k ∈ Finset.range n, paretoPointHilbert k) - hilbertOne

def tailBasisPhysical (n k : ℕ) : ℝ :=
  if k = n then (n : ℝ)+1 else if n < k then -1 else 0

private theorem physical_sum (s : Finset ℕ) (f : ℕ → ThresholdHilbert) (k : ℕ) :
    hilbertGibbsPhysical (∑ n ∈ s, f n) k = ∑ n ∈ s, hilbertGibbsPhysical (f n) k := by
  change hilbertSequenceLinear (∑ n ∈ s, f n) (k+1) =
    ∑ n ∈ s, hilbertSequenceLinear (f n) (k+1)
  rw [map_sum]
  simp only [Finset.sum_apply]

@[simp] theorem hilbertGibbsPhysical_tailBasis (n k : ℕ) :
    hilbertGibbsPhysical (tailBasisHilbert n) k = tailBasisPhysical n k := by
  unfold tailBasisHilbert
  have hsub (f g : ThresholdHilbert) : hilbertGibbsPhysical (f-g) k =
      hilbertGibbsPhysical f k - hilbertGibbsPhysical g k := by
    simp [hilbertGibbsPhysical, sub_div]
  rw [hsub, hilbertGibbsPhysical_add, hilbertGibbsPhysical_smul]
  change ((n : ℝ)+2) * hilbertGibbsPhysical (paretoPointHilbert n) k +
    hilbertGibbsPhysical (∑ j ∈ Finset.range n, paretoPointHilbert j) k -
      hilbertGibbsPhysical hilbertOne k = _
  rw [physical_sum, hilbertGibbs_one_physical]
  simp only [hilbertGibbsPhysical_paretoPoint]
  have hs : (∑ j ∈ Finset.range n, if k = j then (1 : ℝ) else 0) =
      if k < n then 1 else 0 := by simp
  rw [hs]
  unfold tailBasisPhysical
  by_cases hkn : k = n
  · subst k
    simp
    ring
  · by_cases hlt : n < k
    · have hnlt : ¬ k < n := by omega
      simp [hkn, hlt, hnlt]
    · have hklt : k < n := by omega
      simp [hkn, hlt, hklt]

/-- Every tail vector has weighted mean exactly zero. -/
theorem tailBasis_inner_one (n : ℕ) :
    inner ℝ (tailBasisHilbert n) hilbertOne = 0 := by
  unfold tailBasisHilbert
  rw [inner_sub_left, inner_add_left, inner_smul_left, sum_inner]
  simp only [paretoPoint_inner_one, RCLike.conj_to_real]
  rw [real_inner_self_eq_norm_sq, hilbertOne_norm_sq, paretoWeight_partial_sum]
  unfold paretoWeight
  have h1 : (n : ℝ)+1 ≠ 0 := by positivity
  have h2 : (n : ℝ)+2 ≠ 0 := by positivity
  field_simp
  ring

private theorem tailBasis_inner_point_of_lt (n k : ℕ) (hk : k < n) :
    inner ℝ (tailBasisHilbert n) (paretoPointHilbert k) = 0 := by
  rw [inner_paretoPoint, hilbertGibbsPhysical_tailBasis]
  have hne : k ≠ n := by omega
  have hnl : ¬n < k := by omega
  simp [tailBasisPhysical, hne, hnl]

theorem tailBasis_inner_self (n : ℕ) :
    inner ℝ (tailBasisHilbert n) (tailBasisHilbert n) = 1 := by
  conv_lhs => rhs; unfold tailBasisHilbert
  rw [inner_sub_right, inner_add_right, inner_smul_right, inner_sum,
    tailBasis_inner_one, inner_paretoPoint, hilbertGibbsPhysical_tailBasis]
  have hz : (∑ k ∈ Finset.range n,
      inner ℝ (tailBasisHilbert n) (paretoPointHilbert k)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    exact tailBasis_inner_point_of_lt n k (Finset.mem_range.1 hk)
  rw [hz]
  simp only [tailBasisPhysical, ↓reduceIte, add_zero, sub_zero]
  unfold paretoWeight
  have h1 : (n : ℝ)+1 ≠ 0 := by positivity
  have h2 : (n : ℝ)+2 ≠ 0 := by positivity
  field_simp

theorem tailBasis_inner_of_lt (n m : ℕ) (hmn : m < n) :
    inner ℝ (tailBasisHilbert n) (tailBasisHilbert m) = 0 := by
  conv_lhs => rhs; unfold tailBasisHilbert
  rw [inner_sub_right, inner_add_right, inner_smul_right, inner_sum,
    tailBasis_inner_one, tailBasis_inner_point_of_lt n m hmn]
  have hz : (∑ k ∈ Finset.range m,
      inner ℝ (tailBasisHilbert n) (paretoPointHilbert k)) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    exact tailBasis_inner_point_of_lt n k (lt_trans (Finset.mem_range.1 hk) hmn)
  rw [hz]
  simp

theorem tailBasis_inner (n m : ℕ) :
    inner ℝ (tailBasisHilbert n) (tailBasisHilbert m) = if n = m then 1 else 0 := by
  by_cases he : n = m
  · subst m
    rw [if_pos rfl]
    exact tailBasis_inner_self n
  · rw [if_neg he]
    rcases lt_or_gt_of_ne he with h | h
    · rw [real_inner_comm]
      exact tailBasis_inner_of_lt m n h
    · exact tailBasis_inner_of_lt n m h

theorem tailBasis_orthonormal : Orthonormal ℝ tailBasisHilbert :=
  orthonormal_iff_ite.2 tailBasis_inner

/-- A vector orthogonal to the constant and every tail wavelet is zero. -/
theorem tailBasis_total (f : ThresholdHilbert)
    (hmean : inner ℝ f hilbertOne = 0)
    (horth : ∀ n, inner ℝ f (tailBasisHilbert n) = 0) : f = 0 := by
  have hp : ∀ n, inner ℝ f (paretoPointHilbert n) = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      have h := horth n
      unfold tailBasisHilbert at h
      rw [inner_sub_right, inner_add_right, inner_smul_right, inner_sum, hmean] at h
      have hz : (∑ k ∈ Finset.range n, inner ℝ f (paretoPointHilbert k)) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        exact ih k (Finset.mem_range.1 hk)
      rw [hz] at h
      have hn0 : (n : ℝ)+2 ≠ 0 := by positivity
      exact (mul_eq_zero.mp (by simpa using h)).resolve_left hn0
  apply Subtype.ext
  funext n
  have h := hp n
  rw [inner_paretoPoint] at h
  have hf : hilbertGibbsPhysical f n = 0 :=
    (mul_eq_zero.mp h).resolve_left (ne_of_gt (paretoWeight_pos n))
  unfold hilbertGibbsPhysical at hf
  have hs : Real.sqrt (paretoWeight n) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (paretoWeight_pos n))
  change f n = 0
  exact (div_eq_zero_iff.mp hf).resolve_right hs

def tailBasisSpan : Submodule ℝ ThresholdHilbert :=
  Submodule.span ℝ (Set.range tailBasisHilbert)

theorem tailBasisSpan_orthogonal :
    tailBasisSpanᗮ = Submodule.span ℝ {hilbertOne} := by
  apply le_antisymm
  · intro f hf
    have hf' : ∀ g ∈ tailBasisSpan, inner ℝ g f = 0 := hf
    let c := inner ℝ f hilbertOne
    have hzero : f - c • hilbertOne = 0 := by
      apply tailBasis_total
      · rw [inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq,
          hilbertOne_norm_sq]
        simp [c]
      · intro n
        rw [inner_sub_left, inner_smul_left]
        have h1 : inner ℝ f (tailBasisHilbert n) = 0 := by
          rw [real_inner_comm]
          exact hf' _ (Submodule.subset_span ⟨n, rfl⟩)
        have h2 : inner ℝ hilbertOne (tailBasisHilbert n) = 0 := by
          rw [real_inner_comm]
          exact tailBasis_inner_one n
        simp only [h1, h2, mul_zero, sub_zero]
    rw [sub_eq_zero.mp hzero]
    exact (Submodule.span ℝ {hilbertOne}).smul_mem c
      (Submodule.subset_span (by simp))
  · apply Submodule.span_le.2
    intro f hf
    have he : f = hilbertOne := Set.mem_singleton_iff.1 hf
    subst f
    change ∀ y ∈ tailBasisSpan, inner ℝ y hilbertOne = 0
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨n, rfl⟩ := hz
      exact tailBasis_inner_one n
    | zero => simp
    | add x y hx hy ihx ihy => simp [inner_add_left, ihx, ihy]
    | smul c x hx ih => simp [inner_smul_left, ih]

/-- The actual tail wavelets are complete in the mean-zero Hilbert subspace. -/
theorem tailBasisSpan_closure :
    tailBasisSpan.topologicalClosure = (Submodule.span ℝ {hilbertOne})ᗮ := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure, tailBasisSpan_orthogonal]

theorem tailBasis_mem_closure_iff_mean_zero (f : ThresholdHilbert) :
    f ∈ tailBasisSpan.topologicalClosure ↔ inner ℝ f hilbertOne = 0 := by
  rw [tailBasisSpan_closure]
  constructor
  · intro hf
    rw [real_inner_comm]
    exact hf _ (Submodule.subset_span (by simp))
  · intro hf
    change ∀ g ∈ Submodule.span ℝ {hilbertOne}, inner ℝ g f = 0
    intro g hg
    induction hg using Submodule.span_induction with
    | mem y hy =>
      have he : y = hilbertOne := Set.mem_singleton_iff.1 hy
      rw [he, real_inner_comm]
      exact hf
    | zero => simp
    | add x y hx hy ihx ihy => simp [inner_add_left, ihx, ihy]
    | smul c x hx ih => simp [inner_smul_left, ih]

end
end RiemannResearch.RH.Pareto
