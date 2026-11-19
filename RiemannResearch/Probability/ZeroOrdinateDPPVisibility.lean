import RiemannResearch.Probability.ZeroOrdinateDPPSampling
import RiemannResearch.Analysis.ActualZeroOrdinate
import RiemannResearch.RH.WeilExplicitFormula.RvM.NcountWindow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A local lower bound on zero-label inclusion probabilities

The difference of adjacent integer cutoff features isolates a unit height
interval. A shifted cosine is one on the prescribed ordinate and has square
norm bounded by the actual number of copies in that interval. Cauchy-Schwarz
therefore bounds the inverse inclusion probability, uniformly in every
frequency dictionary, including a single repeated frequency.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Probability.DPP.ZeroOrdinateInfinite
open RiemannResearch.Analysis ActualZeroOrdinate Zeta23

private def cutoffSites (T : ℝ) : Finset Site := (bounded_sites_finite T).toFinset

private theorem mem_cutoffSites (T : ℝ) (i : Site) : i ∈ cutoffSites T ↔ ordinate i ≤ T :=
  Set.Finite.mem_toFinset _

private theorem cutoffSites_card (T : ℝ) : (cutoffSites T).card = Ncount 0 T := by
  classical
  have he : cutoffSites T = Finset.univ.map (liftCopy T) := by
    ext i
    constructor
    · intro hi
      obtain ⟨c, rfl⟩ := liftCopy_surj_below T i ((mem_cutoffSites T i).mp hi)
      exact Finset.mem_map.mpr ⟨c, Finset.mem_univ _, rfl⟩
    · intro hi
      obtain ⟨c, _, rfl⟩ := Finset.mem_map.mp hi
      exact (mem_cutoffSites _ _).mpr (mem_cutoff.mp c.1.2).2.2
  rw [he, Finset.card_map, Finset.card_univ, card_copies]

private theorem cutoff_shifted_cos_mem (q : ℕ → ℝ) (n k : ℕ) (s : ℝ) :
    cutoffVector n (fun t => Real.cos (q k * (t - s))) ∈ closedSpace q := by
  let S := closedSpace q
  have hg (a : FeatureIndex) : feature q a ∈ S :=
    (Submodule.le_topologicalClosure _) (Submodule.subset_span ⟨a, rfl⟩)
  have hc : cutoffVector n (fun t => Real.cos (q k * t)) ∈ S := hg (n, k, false)
  have hs : cutoffVector n (fun t => Real.sin (q k * t)) ∈ S := hg (n, k, true)
  have he : cutoffVector n (fun t => Real.cos (q k * (t - s))) =
      Real.cos (q k * s) • cutoffVector n (fun t => Real.cos (q k * t)) +
      Real.sin (q k * s) • cutoffVector n (fun t => Real.sin (q k * t)) := by
    unfold cutoffVector
    simp only [mul_sub, Real.cos_sub, add_smul, Finset.sum_add_distrib, Finset.smul_sum,
      smul_smul]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro c _ <;> rw [mul_comm]
  rw [he]
  exact S.add_mem (S.smul_mem _ hc) (S.smul_mem _ hs)

/-- A label in the unit shell has inclusion probability at least the
reciprocal of the *actual* multiplicity-weighted zero count in that shell. -/
theorem one_le_kernel_mul_unit_count (q : ℕ → ℝ) (n : ℕ) (i : Site)
    (hi : (n : ℝ) < ordinate i) (hi' : ordinate i ≤ (n : ℝ) + 1) :
    1 ≤ limitingKernel q i i * (Ncount n ((n : ℝ) + 1) : ℝ) := by
  classical
  let S := closedSpace q
  let H := (n : ℝ) + 1
  let A := cutoffSites H \ cutoffSites n
  have hmem (j : Site) : j ∈ A ↔ (ordinate j ≤ H ∧ ¬ordinate j ≤ (n : ℝ)) := by
    simp only [A, Finset.mem_sdiff, mem_cutoffSites]
  have hinc : cutoffSites n ⊆ cutoffSites H := by
    intro j hj
    exact (mem_cutoffSites H j).mpr (((mem_cutoffSites _ _).mp hj).trans (by dsimp [H]; linarith))
  have hcard : A.card = Ncount n H := by
    have h := Finset.card_sdiff_add_card_eq_card hinc
    have h' := Ncount_add (a := 0) (b := (n : ℝ)) (c := H) (Nat.cast_nonneg _)
      (show (n : ℝ) ≤ H by dsimp [H]; linarith)
    simp only [cutoffSites_card] at h
    dsimp only [A]
    omega
  let f := fun t => Real.cos (q 0 * (t - ordinate i))
  let v := cutoffVector H f - cutoffVector n f
  have hv : v ∈ S := by
    apply S.sub_mem _ (cutoff_shifted_cos_mem q n 0 (ordinate i))
    simpa only [Nat.cast_add, Nat.cast_one] using cutoff_shifted_cos_mem q (n + 1) 0 (ordinate i)
  have hcoord (j : Site) : inner ℝ (coordinate j) v = if j ∈ A then f (ordinate j) else 0 := by
    dsimp only [v]
    rw [inner_sub_right, cutoffVector_coordinate, cutoffVector_coordinate]
    by_cases hj : ordinate j ≤ (n : ℝ)
    · have hh : ordinate j ≤ H := hj.trans (by dsimp [H]; linarith)
      simp only [hj, hh, hmem, not_true_eq_false, and_false, if_true, if_false, sub_self]
    · by_cases hh : ordinate j ≤ H <;> simp [hmem, hj, hh]
  have hsum : v = ∑ j ∈ A, f (ordinate j) • coordinate j := by
    apply coordinate_ext
    intro j
    rw [hcoord, inner_sum]
    simp [inner_smul_right, coordinate_inner, mul_ite]
  have hn : ‖v‖ ^ 2 ≤ (A.card : ℝ) := by
    rw [← real_inner_self_eq_norm_sq]
    conv_lhs => lhs; rw [hsum]
    rw [sum_inner]
    calc
      _ ≤ ∑ _j ∈ A, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [real_inner_smul_left, hcoord, if_pos hj]
        have hh := abs_le.mp (Real.abs_cos_le_one (q 0 * (ordinate j - ordinate i)))
        dsimp only [f]
        nlinarith only [mul_nonneg (sub_nonneg.mpr hh.2)
          (show 0 ≤ 1 + Real.cos (q 0 * (ordinate j - ordinate i)) by linarith)]
      _ = _ := by simp
  have hhit : inner ℝ (S.starProjection (coordinate i)) v = 1 := by
    rw [S.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr hv, hcoord,
      if_pos ((hmem i).mpr ⟨hi', not_le.mpr hi⟩)]
    simp [f]
  have hcs := real_inner_le_norm (S.starProjection (coordinate i)) v
  rw [hhit] at hcs
  have hsq := mul_self_le_mul_self (zero_le_one : (0 : ℝ) ≤ 1) hcs
  have hk : limitingKernel q i i = ‖S.starProjection (coordinate i)‖ ^ 2 :=
    ProjectionDPP.kernel_diagonal _ _ _
  have hb := mul_le_mul_of_nonneg_left hn (sq_nonneg ‖S.starProjection (coordinate i)‖)
  rw [hk, ← hcard]
  nlinarith only [hsq, hb]

/-- The inverse inclusion probability grows at most logarithmically in
the unit shell height, uniformly over every frequency dictionary. -/
theorem exists_inverse_kernel_le_unit_log :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (q : ℕ → ℝ) (n : ℕ) (i : Site),
      (n : ℝ) < ordinate i → ordinate i ≤ (n : ℝ) + 1 →
      (limitingKernel q i i)⁻¹ ≤ C * Real.log ((n : ℝ) + 3) := by
  obtain ⟨C, hC, hn⟩ := local_zero_count
  refine ⟨C, hC,?_⟩
  intro q n i hi hu
  have hk := limitingKernel_diagonal_pos q i
  have hlo : (limitingKernel q i i)⁻¹ ≤ (Ncount n ((n : ℝ) + 1) : ℝ) := by
    rw [← one_div, div_le_iff₀ hk, mul_comm]
    exact one_le_kernel_mul_unit_count q n i hi hu
  exact hlo.trans (by
    simpa only [abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))] using hn (n : ℝ))

end RiemannResearch.Probability.DPP.ZeroOrdinateInfinite
