import RiemannResearch.Probability.ZeroOrdinateInfiniteDPP
import RiemannResearch.Probability.DeterminantalMoments
import RiemannResearch.Probability.DeterminantalConfiguration
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Finite-rank obstruction for a projection DPP

The trace captured by any finite orthonormal coordinate window is at most the
projection rank. The exact difference is the sum of the missing coordinate
energies of an orthonormal basis of the range. For the finite-feature zero
process this bounds the expected number of selected copies by the number of
features, uniformly in the height window.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace RiemannResearch.Analysis.ProjectionDPP
variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (S : Submodule ℝ H) [S.HasOrthogonalProjection]
variable (e : ι → H) (I : Finset ι)

/-- Parseval on the finite-dimensional range of a projection kernel. -/
theorem kernel_eq_finite_basis_sum (i : ι) {r : Type*} [Fintype r]
    (b : OrthonormalBasis r ℝ S) :
    kernel S e i i = ∑ a, (inner ℝ (e i) (b a : H)) ^ 2 := by
  let z : S := ⟨S.starProjection (e i), S.starProjection_apply_mem _⟩
  have h (a : r) : inner ℝ z (b a) = inner ℝ (e i) (b a : H) := by
    change inner ℝ (S.starProjection (e i)) (b a : H) = _
    rw [S.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr (b a).property]
  calc
    kernel S e i i = ‖z‖ ^ 2 := kernel_diagonal S e i
    _ = ∑ a, (inner ℝ z (b a)) ^ 2 := (b.sum_sq_inner_left z).symm
    _ = _ := by simp only [h]

/-- The exact finite-window trace defect for any orthonormal basis of the range. -/
theorem finite_window_trace_identity {r : Type*} [Fintype r] (b : OrthonormalBasis r ℝ S) :
    (∑ i ∈ I, kernel S e i i) +
      (∑ a : r, (1 - ∑ i ∈ I, (inner ℝ (e i) (b a : H)) ^ 2)) = Fintype.card r := by
  simp_rw [kernel_eq_finite_basis_sum S e _ b]
  rw [Finset.sum_comm, Finset.sum_sub_distrib]
  simp

/-- A finite coordinate window captures at most the projection rank. -/
theorem finite_window_trace_le_finrank [FiniteDimensional ℝ S] (he : Orthonormal ℝ e) :
    ∑ i ∈ I, kernel S e i i ≤ Module.finrank ℝ S := by
  let b := stdOrthonormalBasis ℝ S
  have h := finite_window_trace_identity S e I b
  have hn : 0 ≤ ∑ a, (1 - ∑ i ∈ I, (inner ℝ (e i) (b a : H)) ^ 2) := by
    apply Finset.sum_nonneg
    intro a _
    apply sub_nonneg.mpr
    have hh := he.sum_inner_products_le (s := I) (b a : H)
    have hb : ‖(b a : H)‖ = 1 := b.orthonormal.norm_eq_one a
    simpa only [Real.norm_eq_abs, sq_abs, hb, one_pow] using hh
  simp only [Fintype.card_fin] at h
  linarith

end RiemannResearch.Analysis.ProjectionDPP

namespace RiemannResearch.Probability.DPP.ZeroOrdinateInfinite
open RiemannResearch.Analysis ActualZeroOrdinate ProjectionDPP

/-- A walk with n features has rank at most n, allowing repeated or zero features. -/
theorem finiteSpace_finrank_le (q : ℕ → ℝ) (n : ℕ) :
    Module.finrank ℝ (finiteSpace q n) ≤ n := by
  let f : Fin n → Space := fun i => feature q (enumeration i.val)
  have h : Set.finrank ℝ (Set.range f) ≤ Fintype.card (Fin n) := finrank_range_le_card f
  rw [Fintype.card_fin] at h
  change Module.finrank ℝ (Submodule.span ℝ (Set.range f)) ≤ n
  exact h

/-- The expected number of finite-feature DPP selections below any height is at most n. -/
theorem finiteLaw_expected_count_le_features (q : ℕ → ℝ) (n : ℕ) (T : ℝ) :
    (∫ x, windowCount (fun x : Site → Bool => {j | x j = true}) (liftCopy T) x
      ∂finiteLaw q n) ≤ n := by
  classical
  rw [(finiteLaw_isDPP q n).expected_windowCount]
  let e := fun c : Copies T => coordinate (liftCopy T c)
  have he : Orthonormal ℝ e := by
    apply orthonormal_iff_ite.mpr
    intro i j
    simp [e, coordinate_inner]
  exact (finite_window_trace_le_finrank (finiteSpace q n) e Finset.univ he).trans
    (by exact_mod_cast finiteSpace_finrank_le q n)

/-- Expected missing copies at a finite stage have a deterministic rank lower bound. -/
theorem finite_feature_vacancy_lower (q : ℕ → ℝ) (n : ℕ) (T : ℝ) :
    (Zeta23.Ncount 0 T : ℝ) - n ≤
      ∑ c : Copies T, (1 - finiteKernel q n (liftCopy T c) (liftCopy T c)) := by
  have h := finiteLaw_expected_count_le_features q n T
  rw [(finiteLaw_isDPP q n).expected_windowCount] at h
  rw [Finset.sum_sub_distrib]
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, card_copies] using
    sub_le_sub_left h (Zeta23.Ncount 0 T : ℝ)

private theorem hasSum_coordinate_sq (v : Space) :
    HasSum (fun i : Site => (inner ℝ (coordinate i) v) ^ 2) (‖v‖ ^ 2) := by
  have hc (i : Site) : inner ℝ (coordinate i) v = v i := by
    simp [coordinate, lp.inner_single_left]
  simpa only [hc, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs] using
    (lp.hasSum_inner (𝕜 := ℝ) v v)

/-- The trace of the finite zero-label kernel equals its actual projection rank. -/
theorem finiteKernel_rank_trace (q : ℕ → ℝ) (n : ℕ) :
    Summable (fun i => finiteKernel q n i i) ∧
      (∑' i, finiteKernel q n i i) = (Module.finrank ℝ (finiteSpace q n) : ℝ) := by
  let S := finiteSpace q n
  let b := stdOrthonormalBasis ℝ S
  have hs (a : Fin (Module.finrank ℝ S)) := hasSum_coordinate_sq (b a : Space)
  have hdiag (i : Site) : finiteKernel q n i i = ∑ a, (inner ℝ (coordinate i) (b a : Space)) ^ 2 :=
    kernel_eq_finite_basis_sum S coordinate i b
  simp only [hdiag]
  refine ⟨summable_sum (fun a _ => (hs a).summable), ?_⟩
  rw [Summable.tsum_finsetSum (s := Finset.univ) (fun a _ => (hs a).summable)]
  have hn (a : Fin (Module.finrank ℝ S)) : ‖(b a : Space)‖ = 1 := b.orthonormal.norm_eq_one a
  simp only [(hs _).tsum_eq, hn, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, S]

theorem finiteKernel_det_zero_above_rank (q : ℕ → ℝ) (n : ℕ)
    (a : Fin (Module.finrank ℝ (finiteSpace q n) + 1) → Site) :
    (Matrix.of (fun i j => finiteKernel q n (a i) (a j))).det = 0 := by
  by_contra hd
  let S := finiteSpace q n
  let v : Fin (Module.finrank ℝ S + 1) → S := fun i =>
    ⟨S.starProjection (coordinate (a i)), S.starProjection_apply_mem _⟩
  have hv : LinearIndependent ℝ v := Matrix.linearIndependent_of_det_gram_ne_zero (by
    change (Matrix.of (fun i j => finiteKernel q n (a i) (a j))).det ≠ 0
    exact hd)
  have hh := hv.fintype_card_le_finrank
  rw [Fintype.card_fin] at hh
  omega

/-- The total number of labels sampled by the finite-feature law is almost
surely exactly the number of linearly independent feature directions. -/
theorem finiteLaw_cardinality (q : ℕ → ℝ) (n : ℕ) :
    ∀ᵐ x ∂finiteLaw q n, setCount {i | x i = true} = Module.finrank ℝ (finiteSpace q n) := by
  have ht := finiteKernel_rank_trace q n
  exact (finiteLaw_isDPP q n).setCount_eq_ae_of_rank_trace _
    (fun e => finiteKernel_det_zero_above_rank q n e) ht.1 ht.2

/-- For a full-rank tuple the principal determinant is the probability of
the exact selected configuration, on the entire actual positive-zero ground set. -/
theorem finiteLaw_full_configuration (q : ℕ → ℝ) (n : ℕ)
    (e : Fin (Module.finrank ℝ (finiteSpace q n)) ↪ Site) :
    (finiteLaw q n).real {x | {i | x i = true} = Set.range e} =
      (Matrix.of (fun i j => finiteKernel q n (e i) (e j))).det :=
  (finiteLaw_isDPP q n).full_configuration_of_setCount _ (finiteLaw_cardinality q n) e

end RiemannResearch.Probability.DPP.ZeroOrdinateInfinite
