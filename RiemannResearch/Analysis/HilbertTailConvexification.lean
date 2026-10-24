import RiemannResearch.Analysis.HilbertWeakNorm
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Choose

/-!
# Finite convexification of arbitrary weakly convergent tails

Source: user-requested fifth Ramanujan transfer program, 24 October 2026.
This is the standard Mazur convexification argument, proved using Mathlib's
geometric Hahn--Banach separation theorem and the Hilbert Riesz equivalence.
Every filter-large set supplies finite normalized nonnegative combinations;
all eventual convex constraints are preserved by the resulting combinations.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.HilbertTailConvexification
open HilbertWeakNorm

variable {H α : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] {l : Filter α} [NeBot l]

/-- Every eventual tail has the weak limit in its norm-closed convex hull. -/
theorem mem_closedConvexHull_image_of_innerWeak
    (F : α → H) (x : H) (hw : InnerWeakTendsto F l x)
    (s : Set α) (hs : s ∈ l) : x ∈ closedConvexHull ℝ (F '' s) := by
  by_contra hx
  obtain ⟨f, u, hf, hux⟩ := geometric_hahn_banach_closed_point
    (convex_closedConvexHull (𝕜 := ℝ) (s := F '' s)) isClosed_closedConvexHull hx
  have ht : Tendsto (fun i => f (F i)) l (𝓝 (f x)) := by
    simpa only [InnerProductSpace.toDual_symm_apply] using
      hw ((InnerProductSpace.toDual ℝ H).symm f)
  have hu : ∀ᶠ i in l, u < f (F i) := Filter.Tendsto.eventually_const_lt hux ht
  obtain ⟨i, hi, hui⟩ := (Filter.Eventually.and hs hu).exists
  exact lt_asymm (hf (F i) (subset_closedConvexHull ⟨i, hi, rfl⟩)) hui

theorem exists_convexHull_approx_of_innerWeak
    (F : α → H) (x : H) (hw : InnerWeakTendsto F l x)
    (s : Set α) (hs : s ∈ l) (ε : ℝ) (hε : 0 < ε) :
    ∃ y ∈ convexHull ℝ (F '' s), ‖y - x‖ < ε := by
  have hx := mem_closedConvexHull_image_of_innerWeak F x hw s hs
  rw [closedConvexHull_eq_closure_convexHull] at hx
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx ε hε
  exact ⟨y, hy, by simpa only [dist_eq_norm, norm_sub_rev] using hxy⟩

/-- Explicit finite nonnegative weights of total mass one, supported in any requested tail. -/
theorem exists_finite_tail_combination
    (F : α → H) (x : H) (hw : InnerWeakTendsto F l x)
    (s : Set α) (hs : s ∈ l) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (w : Fin n → ℝ) (j : Fin n → α),
      (∀ k, 0 ≤ w k) ∧ (∑ k, w k) = 1 ∧ (∀ k, j k ∈ s) ∧
        ‖(∑ k, w k • F (j k)) - x‖ < ε := by
  classical
  obtain ⟨y, hy, hxy⟩ := exists_convexHull_approx_of_innerWeak F x hw s hs ε hε
  obtain ⟨ι, hι, w, z, hw, hsum, hz, hzy⟩ := mem_convexHull_iff_exists_fintype.mp hy
  letI : Fintype ι := hι
  choose j hj hFj using hz
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hsum' : (∑ k, w (e k)) = 1 := by
    calc
      _ = ∑ i, w i := Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = 1 := hsum
  have hvec : (∑ k, w (e k) • F (j (e k))) = y := by
    calc
      _ = ∑ i, w i • F (j i) := Fintype.sum_equiv e _ _ (fun _ => rfl)
      _ = ∑ i, w i • z i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hFj i]
      _ = y := hzy
  refine ⟨Fintype.card ι, fun k => w (e k), fun k => j (e k),
    fun k => hw (e k), hsum', fun k => hj (e k), ?_⟩
  simpa only [hvec] using hxy

/-- All eventual convex constraints can be imposed on the chosen finite combination. -/
theorem exists_constrained_finite_tail_combination
    (F : α → H) (x : H) (hw : InnerWeakTendsto F l x)
    (C : Set H) (hC : Convex ℝ C) (hlegal : ∀ᶠ i in l, F i ∈ C)
    (s : Set α) (hs : s ∈ l) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (w : Fin n → ℝ) (j : Fin n → α),
      (∀ k, 0 ≤ w k) ∧ (∑ k, w k) = 1 ∧ (∀ k, j k ∈ s ∧ F (j k) ∈ C) ∧
        (∑ k, w k • F (j k)) ∈ C ∧ ‖(∑ k, w k • F (j k)) - x‖ < ε := by
  obtain ⟨n, w, j, hw', hsum, hj, hclose⟩ := exists_finite_tail_combination F x hw
    (s ∩ {i | F i ∈ C}) (Filter.Eventually.and hs hlegal) ε hε
  refine ⟨n, w, j, hw', hsum, hj, ?_, hclose⟩
  exact hC.sum_mem (fun k hk => hw' k) hsum (fun k hk => (hj k).2)

/-- In particular, finite convexification preserves an algebraic legal submodule. -/
theorem exists_legal_finite_tail_combination
    (F : α → H) (x : H) (hw : InnerWeakTendsto F l x)
    (S : Submodule ℝ H) (hlegal : ∀ᶠ i in l, F i ∈ S)
    (s : Set α) (hs : s ∈ l) (ε : ℝ) (hε : 0 < ε) :
    ∃ (n : ℕ) (w : Fin n → ℝ) (j : Fin n → α),
      (∀ k, 0 ≤ w k) ∧ (∑ k, w k) = 1 ∧ (∀ k, j k ∈ s ∧ F (j k) ∈ S) ∧
        (∑ k, w k • F (j k)) ∈ S ∧ ‖(∑ k, w k • F (j k)) - x‖ < ε :=
  exists_constrained_finite_tail_combination F x hw S S.convex hlegal s hs ε hε

/-- Every finite combination of initial dictionary segments is one common-cutoff synthesis.
Neither independence nor nonnegative weights are needed for this algebraic statement. -/
theorem finite_partial_synthesis_common_stage {κ : Type*} [Fintype κ]
    (v : ℕ → H) (N : κ → ℕ) (a : ∀ i, Fin (N i) → ℝ) (w : κ → ℝ) :
    ∃ (M : ℕ) (b : Fin M → ℝ), (∀ i, N i ≤ M) ∧
      Fintype.linearCombination ℝ (fun j : Fin M => v j.val) b =
        ∑ i, w i • Fintype.linearCombination ℝ (fun j : Fin (N i) => v j.val) (a i) := by
  classical
  let M : ℕ := Finset.univ.sup N
  let S : Submodule ℝ H := Submodule.span ℝ (Set.range (fun j : Fin M => v j.val))
  have hM (i : κ) : N i ≤ M := Finset.le_sup (Finset.mem_univ i)
  have hmem (i : κ) :
      Fintype.linearCombination ℝ (fun j : Fin (N i) => v j.val) (a i) ∈ S := by
    rw [Fintype.linearCombination_apply]
    apply S.sum_mem
    intro j hj
    apply S.smul_mem
    exact Submodule.subset_span ⟨⟨j.val, j.isLt.trans_le (hM i)⟩, rfl⟩
  have hsum : (∑ i, w i •
      Fintype.linearCombination ℝ (fun j : Fin (N i) => v j.val) (a i)) ∈ S := by
    exact S.sum_mem (fun i hi => S.smul_mem _ (hmem i))
  obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hsum
  exact ⟨M, b, hM, by simpa only [Fintype.linearCombination_apply] using hb⟩

end RiemannResearch.Analysis.HilbertTailConvexification
