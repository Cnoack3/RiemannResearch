/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.PhysicalPacketCore

/-!
# Exact old and fresh physical packet coordinates

Nested finite packet dictionaries are split into the old set and its literal
set difference. All finite sums, physical core products, and source pairings
are reindexed exactly. This supplies no positivity, inverse, or limiting
hypothesis; those remain properties of the actual physical matrices.
-/

noncomputable section
open Matrix
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.PhysicalSchurReindex
open PhysicalPacketCore

def oldInclusion (s t : Finset ℕ) (hst : s ⊆ t) (q : s) : t :=
  ⟨q.val, hst q.property⟩

def freshInclusion (s t : Finset ℕ) (q : ↥(t \ s)) : t :=
  ⟨q.val, (Finset.mem_sdiff.mp q.property).1⟩

/-- Exact decomposition of every enlarged index into old or fresh indices. -/
def splitEquiv (s t : Finset ℕ) (hst : s ⊆ t) : t ≃ s ⊕ ↥(t \ s) := by
  classical
  refine
    { toFun := fun q => if h : q.val ∈ s then Sum.inl ⟨q.val, h⟩
        else Sum.inr ⟨q.val, Finset.mem_sdiff.mpr ⟨q.property, h⟩⟩
      invFun := Sum.elim (oldInclusion s t hst) (freshInclusion s t)
      left_inv := ?_
      right_inv := ?_ }
  · intro q
    dsimp
    split_ifs <;> rfl
  · intro q
    cases q with
    | inl q => simp [oldInclusion, q.property]
    | inr q => simp [freshInclusion, (Finset.mem_sdiff.mp q.property).2]

/-- Literal finite sum splitting, with no cardinality or nonempty premise. -/
theorem sum_split (s t : Finset ℕ) (hst : s ⊆ t) (f : t → ℝ) :
    (∑ q : t, f q) =
      (∑ q : s, f (oldInclusion s t hst q)) +
        ∑ q : ↥(t \ s), f (freshInclusion s t q) := by
  classical
  let g : ℕ → ℝ := fun q => if h : q ∈ t then f ⟨q, h⟩ else 0
  have ht : (∑ q : t, f q) = ∑ q ∈ t, g q := by
    calc
      _ = ∑ q : t, g q.val := by
        apply Finset.sum_congr rfl
        intro q _
        simp [g, q.property]
      _ = _ := Finset.sum_coe_sort t g
  have hs : (∑ q : s, f (oldInclusion s t hst q)) = ∑ q ∈ s, g q := by
    calc
      _ = ∑ q : s, g q.val := by
        apply Finset.sum_congr rfl
        intro q _
        simp [g, oldInclusion, hst q.property]
      _ = _ := Finset.sum_coe_sort s g
  have hn : (∑ q : ↥(t \ s), f (freshInclusion s t q)) = ∑ q ∈ t \ s, g q := by
    calc
      _ = ∑ q : ↥(t \ s), g q.val := by
        apply Finset.sum_congr rfl
        intro q _
        simp [g, freshInclusion, (Finset.mem_sdiff.mp q.property).1]
      _ = _ := Finset.sum_coe_sort (t \ s) g
  have hd : Disjoint s (t \ s) := by
    apply Finset.disjoint_left.mpr
    intro q hqs hqn
    exact (Finset.mem_sdiff.mp hqn).2 hqs
  have hu : s ∪ (t \ s) = t := by
    ext q
    simp only [Finset.mem_union, Finset.mem_sdiff]
    constructor
    · rintro (h | ⟨h, _⟩)
      · exact hst h
      · exact h
    · intro h
      by_cases hs : q ∈ s
      · exact Or.inl hs
      · exact Or.inr ⟨h, hs⟩
  rw [ht, hs, hn, ← Finset.sum_union hd, hu]

theorem split_dotProduct (s t : Finset ℕ) (hst : s ⊆ t) (a c : t → ℝ) :
    a ⬝ᵥ c =
      (a ∘ oldInclusion s t hst) ⬝ᵥ (c ∘ oldInclusion s t hst) +
        (a ∘ freshInclusion s t) ⬝ᵥ (c ∘ freshInclusion s t) := by
  exact sum_split s t hst (fun q => a q * c q)

def assemble (s t : Finset ℕ) (hst : s ⊆ t)
    (x : s → ℝ) (y : ↥(t \ s) → ℝ) : t → ℝ := by
  classical
  exact fun q => if h : q.val ∈ s then x ⟨q.val, h⟩
    else y ⟨q.val, Finset.mem_sdiff.mpr ⟨q.property, h⟩⟩

theorem assemble_old (s t : Finset ℕ) (hst : s ⊆ t)
    (x : s → ℝ) (y : ↥(t \ s) → ℝ) (q : s) :
    assemble s t hst x y (oldInclusion s t hst q) = x q := by
  classical
  simp [assemble, oldInclusion, q.property]

theorem assemble_fresh (s t : Finset ℕ) (hst : s ⊆ t)
    (x : s → ℝ) (y : ↥(t \ s) → ℝ) (q : ↥(t \ s)) :
    assemble s t hst x y (freshInclusion s t q) = y q := by
  classical
  simp [assemble, freshInclusion, (Finset.mem_sdiff.mp q.property).2]

theorem assemble_restrict_old (s t : Finset ℕ) (hst : s ⊆ t)
    (x : s → ℝ) (y : ↥(t \ s) → ℝ) :
    assemble s t hst x y ∘ oldInclusion s t hst = x := by
  funext q
  exact assemble_old s t hst x y q

theorem assemble_restrict_fresh (s t : Finset ℕ) (hst : s ⊆ t)
    (x : s → ℝ) (y : ↥(t \ s) → ℝ) :
    assemble s t hst x y ∘ freshInclusion s t = y := by
  funext q
  exact assemble_fresh s t hst x y q

theorem assemble_ne_zero_of_fresh (s t : Finset ℕ) (hst : s ⊆ t)
    (x : s → ℝ) (y : ↥(t \ s) → ℝ) (hy : y ≠ 0) : assemble s t hst x y ≠ 0 := by
  intro hz
  apply hy
  funext q
  have h := congrFun hz (freshInclusion s t q)
  simpa only [assemble_fresh, Pi.zero_apply] using h

theorem totient_old (s t : Finset ℕ) (hst : s ⊆ t) :
    ramanujanTotientVector t ∘ oldInclusion s t hst = ramanujanTotientVector s := rfl

theorem totient_fresh (s t : Finset ℕ) :
    ramanujanTotientVector t ∘ freshInclusion s t = ramanujanTotientVector (t \ s) := rfl

theorem vonMangoldt_old (s t : Finset ℕ) (hst : s ⊆ t) :
    ramanujanVonMangoldtVector t ∘ oldInclusion s t hst = ramanujanVonMangoldtVector s := rfl

theorem vonMangoldt_fresh (s t : Finset ℕ) :
    ramanujanVonMangoldtVector t ∘ freshInclusion s t =
      ramanujanVonMangoldtVector (t \ s) := rfl

theorem assembled_totient (s t : Finset ℕ) (hst : s ⊆ t)
    (x : s → ℝ) (y : ↥(t \ s) → ℝ) :
    ramanujanTotientVector t ⬝ᵥ assemble s t hst x y =
      ramanujanTotientVector s ⬝ᵥ x + ramanujanTotientVector (t \ s) ⬝ᵥ y := by
  rw [split_dotProduct s t hst (ramanujanTotientVector t) (assemble s t hst x y),
    totient_old, totient_fresh,
    assemble_restrict_old, assemble_restrict_fresh]

/-- The genuine cross core, retaining its complete signed physical pairing. -/
def crossCore (s t : Finset ℕ) (hst : s ⊆ t) : Matrix s ↥(t \ s) ℝ :=
  fun i j => derivedCore t (oldInclusion s t hst i) (freshInclusion s t j)

theorem core_old_old (s t : Finset ℕ) (hst : s ⊆ t) (i j : s) :
    derivedCore t (oldInclusion s t hst i) (oldInclusion s t hst j) =
      derivedCore s i j := rfl

theorem core_fresh_fresh (s t : Finset ℕ) (i j : ↥(t \ s)) :
    derivedCore t (freshInclusion s t i) (freshInclusion s t j) =
      derivedCore (t \ s) i j := rfl

theorem core_fresh_old (s t : Finset ℕ) (hst : s ⊆ t)
    (i : ↥(t \ s)) (j : s) :
    derivedCore t (freshInclusion s t i) (oldInclusion s t hst j) =
      (crossCore s t hst)ᵀ i j := by
  exact congrArg (fun M : Matrix t t ℝ =>
    M (oldInclusion s t hst j) (freshInclusion s t i)) (derivedCore_transpose t)

theorem old_mulVec (s t : Finset ℕ) (hst : s ⊆ t) (c : t → ℝ) :
    (derivedCore t *ᵥ c) ∘ oldInclusion s t hst =
      derivedCore s *ᵥ (c ∘ oldInclusion s t hst) +
        crossCore s t hst *ᵥ (c ∘ freshInclusion s t) := by
  funext i
  change (∑ j : t, derivedCore t (oldInclusion s t hst i) j * c j) =
    (∑ j : s, derivedCore s i j * c (oldInclusion s t hst j)) +
      ∑ j : ↥(t \ s), crossCore s t hst i j * c (freshInclusion s t j)
  rw [sum_split s t hst]
  simp only [core_old_old, crossCore]

theorem fresh_mulVec (s t : Finset ℕ) (hst : s ⊆ t) (c : t → ℝ) :
    (derivedCore t *ᵥ c) ∘ freshInclusion s t =
      (crossCore s t hst)ᵀ *ᵥ (c ∘ oldInclusion s t hst) +
        derivedCore (t \ s) *ᵥ (c ∘ freshInclusion s t) := by
  funext i
  change (∑ j : t, derivedCore t (freshInclusion s t i) j * c j) =
    (∑ j : s, (crossCore s t hst)ᵀ i j * c (oldInclusion s t hst j)) +
      ∑ j : ↥(t \ s), derivedCore (t \ s) i j * c (freshInclusion s t j)
  rw [sum_split s t hst]
  simp only [core_fresh_old, core_fresh_fresh]

theorem core_quadratic_split (s t : Finset ℕ) (hst : s ⊆ t) (c : t → ℝ) :
    c ⬝ᵥ (derivedCore t *ᵥ c) =
      (c ∘ oldInclusion s t hst) ⬝ᵥ
        (derivedCore s *ᵥ (c ∘ oldInclusion s t hst) +
          crossCore s t hst *ᵥ (c ∘ freshInclusion s t)) +
      (c ∘ freshInclusion s t) ⬝ᵥ
        ((crossCore s t hst)ᵀ *ᵥ (c ∘ oldInclusion s t hst) +
          derivedCore (t \ s) *ᵥ (c ∘ freshInclusion s t)) := by
  rw [split_dotProduct s t hst, old_mulVec, fresh_mulVec]

theorem assembled_core_quadratic (s t : Finset ℕ) (hst : s ⊆ t)
    (x : s → ℝ) (y : ↥(t \ s) → ℝ) :
    assemble s t hst x y ⬝ᵥ (derivedCore t *ᵥ assemble s t hst x y) =
      x ⬝ᵥ (derivedCore s *ᵥ x + crossCore s t hst *ᵥ y) +
        y ⬝ᵥ ((crossCore s t hst)ᵀ *ᵥ x + derivedCore (t \ s) *ᵥ y) := by
  rw [core_quadratic_split, assemble_restrict_old, assemble_restrict_fresh]

end RiemannResearch.RH.Pareto.PhysicalSchurReindex
