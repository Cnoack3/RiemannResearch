/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.GroupTheory.Coxeter.Inversion
import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.GroupTheory.Coxeter.Matrix

/-!
# General Coxeter attracting-rank identities

Reusable maximal-length, descent-count, and attracting-rank results for finite
Coxeter systems. The E8 specialization lives in the E8 subject directory.
-/

namespace RiemannResearch.GroupTheory

/-- Consequences of the Coxeter length and right-descent formulas for the
attracting ranks. -/
structure AttractingRankConclusion
    (W : Type*) (one : W) (longestMul : W → W)
    (rank length rightDescent : W → ℕ)
    (positiveRoots simpleRoots : ℕ) : Prop where
  /-- The tangent-weight count. -/
  formula : ∀ w, rank w = length w + rightDescent w
  /-- The identity component is the unique zero-rank component. -/
  zero_iff : ∀ w, rank w = 0 ↔ w = one
  /-- Sum form of the complementary-rank identity. -/
  duality_sum : ∀ w,
    rank (longestMul w) + rank w = positiveRoots + simpleRoots
  /-- Subtraction form displayed in the source theorem. -/
  duality : ∀ w,
    rank (longestMul w) = positiveRoots + simpleRoots - rank w

/-- The rank formula and the two Coxeter complement identities imply unique
zero rank and attracting-rank duality. -/
theorem attractingRank_properties
    {W : Type*} (one : W) (longestMul : W → W)
    (rank length rightDescent : W → ℕ)
    (positiveRoots simpleRoots : ℕ)
    (rank_formula : ∀ w, rank w = length w + rightDescent w)
    (length_zero_iff : ∀ w, length w = 0 ↔ w = one)
    (rightDescent_one : rightDescent one = 0)
    (length_duality :
      ∀ w, length (longestMul w) + length w = positiveRoots)
    (rightDescent_duality :
      ∀ w, rightDescent (longestMul w) + rightDescent w = simpleRoots) :
    AttractingRankConclusion W one longestMul rank length rightDescent
      positiveRoots simpleRoots := by
  have hduality :
      ∀ w, rank (longestMul w) + rank w =
        positiveRoots + simpleRoots := by
    intro w
    calc
      rank (longestMul w) + rank w =
          (length (longestMul w) + length w) +
            (rightDescent (longestMul w) + rightDescent w) := by
              rw [rank_formula, rank_formula]
              ac_rfl
      _ = positiveRoots + simpleRoots := by
        rw [length_duality, rightDescent_duality]
  refine
    { formula := rank_formula
      zero_iff := ?_
      duality_sum := hduality
      duality := ?_ }
  · intro w
    constructor
    · intro hrank
      have hsum : length w + rightDescent w = 0 := by
        rw [← rank_formula w]
        exact hrank
      have hlength : length w = 0 := (Nat.add_eq_zero_iff.mp hsum).1
      exact (length_zero_iff w).mp hlength
    · intro hw
      subst w
      have hlength : length one = 0 := (length_zero_iff one).mpr rfl
      rw [rank_formula, hlength, rightDescent_one]
  · intro w
    exact Nat.eq_sub_of_add_eq (hduality w)

/-- A finite Coxeter group has an element of maximal Coxeter length. -/
theorem coxeter_exists_maximalLength_of_finite
    {B W : Type*} [Group W] [Finite W] {M : CoxeterMatrix B}
    (cs : CoxeterSystem M W) :
    ∃ w0 : W, ∀ w : W, cs.length w ≤ cs.length w0 := by
  classical
  let _ : Fintype W := Fintype.ofFinite W
  obtain ⟨w0, _, hmax⟩ :=
    (Finset.univ : Finset W).exists_max_image cs.length
      Finset.univ_nonempty
  exact ⟨w0, fun w => hmax w (Finset.mem_univ w)⟩

/-- Every reflection is a strict right inversion of a maximal-length
element. -/
theorem coxeter_isRightInversion_of_maximalLength
    {B W : Type*} [Group W] {M : CoxeterMatrix B}
    (cs : CoxeterSystem M W) (w0 : W)
    (hmax : ∀ w : W, cs.length w ≤ cs.length w0)
    {t : W} (ht : cs.IsReflection t) :
    cs.IsRightInversion w0 t := by
  exact ⟨ht, lt_of_le_of_ne (hmax (w0 * t))
    (CoxeterSystem.IsReflection.length_mul_left_ne ht w0)⟩

/-- Every reflection is a strict left inversion of a maximal-length
element. -/
theorem coxeter_isLeftInversion_of_maximalLength
    {B W : Type*} [Group W] {M : CoxeterMatrix B}
    (cs : CoxeterSystem M W) (w0 : W)
    (hmax : ∀ w : W, cs.length w ≤ cs.length w0)
    {t : W} (ht : cs.IsReflection t) :
    cs.IsLeftInversion w0 t := by
  exact ⟨ht, lt_of_le_of_ne (hmax (t * w0))
    (CoxeterSystem.IsReflection.length_mul_right_ne ht w0)⟩

/-- Every simple generator is a right descent of a maximal-length
element. -/
theorem coxeter_isRightDescent_of_maximalLength
    {B W : Type*} [Group W] {M : CoxeterMatrix B}
    (cs : CoxeterSystem M W) (w0 : W)
    (hmax : ∀ w : W, cs.length w ≤ cs.length w0)
    (i : B) :
    cs.IsRightDescent w0 i := by
  exact (cs.isRightInversion_simple_iff_isRightDescent w0 i).mp
    (coxeter_isRightInversion_of_maximalLength cs w0 hmax
      (cs.isReflection_simple i))

/-- Every simple generator is a left descent of a maximal-length
element. -/
theorem coxeter_isLeftDescent_of_maximalLength
    {B W : Type*} [Group W] {M : CoxeterMatrix B}
    (cs : CoxeterSystem M W) (w0 : W)
    (hmax : ∀ w : W, cs.length w ≤ cs.length w0)
    (i : B) :
    cs.IsLeftDescent w0 i := by
  exact (cs.isLeftInversion_simple_iff_isLeftDescent w0 i).mp
    (coxeter_isLeftInversion_of_maximalLength cs w0 hmax
      (cs.isReflection_simple i))

/-- Number of simple right descents in a Coxeter system with finitely many
simple generators. -/
noncomputable def coxeterRightDescentCount
    {B W : Type*} [Fintype B] [Group W] {M : CoxeterMatrix B}
    (cs : CoxeterSystem M W) (w : W) : ℕ := by
  classical
  exact (Finset.univ.filter (cs.IsRightDescent w)).card

/-- Left multiplication by an element satisfying the Coxeter
length-complement identity exchanges right descents and right ascents. -/
theorem isRightDescent_longestMul_iff_not
    {B W : Type*} [Group W] {M : CoxeterMatrix B}
    (cs : CoxeterSystem M W) (w0 : W) (total : ℕ)
    (hlength : ∀ w, cs.length (w0 * w) + cs.length w = total)
    (w : W) (i : B) :
    cs.IsRightDescent (w0 * w) i ↔ ¬ cs.IsRightDescent w i := by
  rw [cs.isRightDescent_iff, cs.not_isRightDescent_iff]
  have h := hlength w
  have h' := hlength (w * cs.simple i)
  rw [← mul_assoc] at h'
  constructor
  · intro hw
    apply Nat.add_left_cancel (n := cs.length (w0 * w * cs.simple i))
    calc
      cs.length (w0 * w * cs.simple i) + cs.length (w * cs.simple i) = total := h'
      _ = cs.length (w0 * w) + cs.length w := h.symm
      _ = (cs.length (w0 * w * cs.simple i) + 1) + cs.length w := by rw [hw]
      _ = cs.length (w0 * w * cs.simple i) + (cs.length w + 1) := by ac_rfl
  · intro hw
    apply Nat.add_right_cancel
    calc
      (cs.length (w0 * w * cs.simple i) + 1) + cs.length w =
          cs.length (w0 * w * cs.simple i) + (cs.length w + 1) := by ac_rfl
      _ = cs.length (w0 * w * cs.simple i) + cs.length (w * cs.simple i) := by rw [hw]
      _ = total := h'
      _ = cs.length (w0 * w) + cs.length w := h.symm

/-- The identity element has no simple right descents. -/
theorem coxeterRightDescentCount_one
    {B W : Type*} [Fintype B] [Group W] {M : CoxeterMatrix B}
    (cs : CoxeterSystem M W) :
    coxeterRightDescentCount cs (1 : W) = 0 := by
  classical
  simp [coxeterRightDescentCount, cs.not_isRightDescent_one]

/-- A Coxeter length-complement identity implies the complementary
right-descent-count identity. -/
theorem coxeterRightDescentCount_longestMul_add
    {B W : Type*} [Fintype B] [Group W] {M : CoxeterMatrix B}
    (cs : CoxeterSystem M W) (w0 : W) (total : ℕ)
    (hlength : ∀ w, cs.length (w0 * w) + cs.length w = total)
    (w : W) :
    coxeterRightDescentCount cs (w0 * w) +
        coxeterRightDescentCount cs w = Fintype.card B := by
  classical
  have hfilter :
      Finset.univ.filter (cs.IsRightDescent (w0 * w)) =
        Finset.univ.filter (fun i => ¬ cs.IsRightDescent w i) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact isRightDescent_longestMul_iff_not cs w0 total hlength w i
  rw [coxeterRightDescentCount, coxeterRightDescentCount, hfilter]
  simpa [Nat.add_comm] using
    (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset B)) (p := cs.IsRightDescent w))

/-- The rank formula and one length-complement identity imply all
Coxeter-theoretic conclusions needed in corrected Theorem 3.2. -/
theorem coxeterAttractingRank_properties_of_lengthComplement
    {B W : Type*} [Fintype B] [Group W] {M : CoxeterMatrix B}
    (cs : CoxeterSystem M W) (w0 : W) (rank : W → ℕ)
    (positiveRoots : ℕ)
    (rank_formula : ∀ w, rank w =
      cs.length w + coxeterRightDescentCount cs w)
    (length_complement :
      ∀ w, cs.length (w0 * w) + cs.length w = positiveRoots) :
    AttractingRankConclusion W 1 (fun w => w0 * w)
      rank cs.length (coxeterRightDescentCount cs)
      positiveRoots (Fintype.card B) := by
  apply attractingRank_properties
  · exact rank_formula
  · intro w
    exact cs.length_eq_zero_iff
  · exact coxeterRightDescentCount_one cs
  · exact length_complement
  · exact coxeterRightDescentCount_longestMul_add
      cs w0 positiveRoots length_complement

end RiemannResearch.GroupTheory
