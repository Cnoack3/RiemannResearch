/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.AlgebraicGeometry.PointFields
import Mathlib.GroupTheory.Coxeter.Inversion
import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.GroupTheory.Coxeter.Matrix

/-!
# Universal fixed locus and splitting fields

This module formalizes the kernel-checkable core of the theorem
“Universal fixed-locus and splitting-field theorem” from the Serre II / E8
program.

Mathlib does not currently contain the wonderful compactification, contracted
torsor twists, scheme-theoretic fixed loci, Chow motives, Chow groups, or the
motivic Bialynicki--Birula theorem. The main declaration therefore exposes
those ingredients through named interfaces:

* GeometryIso represents the required fixed-locus scheme isomorphism after
  every base change.
* MotiveIso, directSum, and tateTwist represent the motivic decomposition.
* bialynickiBirula_chowZero represents the degree-compatible CH_0
  pushforward from the unique zero-rank component.

The theorem does not assume its point-field or index conclusions. Lean derives
them from the fixed-locus point shadow, the proper orbit limit, inclusion of a
fixed component, and, for inner torsors, the Borel-reduction neutrality
criterion. Compactification/Borel point fields and indices are unconditional;
neutrality and torsor-index comparisons explicitly require innerness. It also
proves the zero-rank and complementary-rank statements from the Coxeter identities.

We use the intended convention that the regular cocharacter is chosen in the
chamber determined by the fixed Borel. Changing its sign merely selects the
attracting-rank convention. The explicit rank-formula input below records the
still-unformalized tangent-weight and fixed-scheme calculation; it is not an
additional mathematical condition on the chosen cocharacter.
-/

namespace RiemannResearch.E8

open RiemannResearch.AlgebraicGeometry

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

/-- Mathlib's presented Coxeter group of type E8. -/
abbrev E8CoxeterGroup : Type := CoxeterMatrix.E₈.Group

/-- The canonical Coxeter system on Mathlib's presented E8 Coxeter group. -/
abbrev e8CoxeterSystem :
    CoxeterSystem CoxeterMatrix.E₈ E8CoxeterGroup :=
  CoxeterMatrix.E₈.toCoxeterSystem

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

/-- Number of simple right descents of an element in the E8 Coxeter group. -/
noncomputable def e8RightDescentCount (w : E8CoxeterGroup) : ℕ :=
  coxeterRightDescentCount e8CoxeterSystem w

/-- The Coxeter-theoretic rank function from the document, defined directly on
Mathlib's E8 Coxeter group. -/
noncomputable def e8AttractingRank (w : E8CoxeterGroup) : ℕ :=
  e8CoxeterSystem.length w + e8RightDescentCount w

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

/-- E8 rank conclusions, conditional only on the currently absent Mathlib
longest-element length-complement theorem. -/
theorem e8AttractingRank_properties_of_lengthComplement
    (w0 : E8CoxeterGroup)
    (length_complement : ∀ w,
      e8CoxeterSystem.length (w0 * w) + e8CoxeterSystem.length w = 120) :
    AttractingRankConclusion E8CoxeterGroup 1 (fun w => w0 * w)
      e8AttractingRank e8CoxeterSystem.length e8RightDescentCount 120 8 := by
  exact coxeterAttractingRank_properties_of_lengthComplement
    e8CoxeterSystem w0 e8AttractingRank 120 (fun _ => rfl) length_complement

/-- The identity is the unique zero of the E8 length-plus-descent rank
function. This part of the source theorem is proved directly from Mathlib's
Coxeter system, without a geometric hypothesis. -/
theorem e8AttractingRank_eq_zero_iff (w : E8CoxeterGroup) :
    e8AttractingRank w = 0 ↔ w = 1 := by
  constructor
  · intro h
    have h' : e8CoxeterSystem.length w + e8RightDescentCount w = 0 := by
      simpa [e8AttractingRank] using h
    exact (e8CoxeterSystem.length_eq_zero_iff).mp
      (Nat.add_eq_zero_iff.mp h').1
  · rintro rfl
    simp [e8AttractingRank, e8RightDescentCount,
      coxeterRightDescentCount_one e8CoxeterSystem]

/-- For E8, the complementary attracting ranks sum to 120 + 8 = 128. -/
theorem e8_total_attracting_rank : 120 + 8 = 128 := by
  rfl

/-- Lean-visible conclusions of the universal fixed-locus theorem.

The types Geometry and Motive and the relations GeometryIso and MotiveIso are
abstract interfaces for geometric theories not yet present in Mathlib. Their
fields state the scheme and motive formulas exactly at that interface.

The final derived fields compare descent predicates, point fields, finite
splitting-degree spectra, and their set-gcd indices. Thus the compactification,
Borel, and neutral-fiber formulations of odd descent are Lean-equivalent.
-/
structure UniversalFixedLocusConclusion
    (Extension W : Type*) (one : W) (longestMul : W → W)
    (rank length rightDescent : W → ℕ)
    (positiveRoots simpleRoots : ℕ)
    (Geometry : Extension → Type*)
    (fixedLocusObject borelObject :
      (L : Extension) → Geometry L)
    (coproduct : (L : Extension) → (W → Geometry L) → Geometry L)
    (GeometryIso :
      (L : Extension) → Geometry L → Geometry L → Prop)
    (Motive : Extension → Type*)
    (compactMotive borelMotive :
      (L : Extension) → Motive L)
    (tateTwist : (L : Extension) → Motive L → ℕ → Motive L)
    (directSum : (L : Extension) → (W → Motive L) → Motive L)
    (MotiveIso : (L : Extension) → Motive L → Motive L → Prop)
    (ChowBorel ChowCompact : Extension → Type*)
    [∀ L, AddCommGroup (ChowBorel L)]
    [∀ L, AddCommGroup (ChowCompact L)]
    (degreeBorel : ∀ L, ChowBorel L →+ ℤ)
    (degreeCompact : ∀ L, ChowCompact L →+ ℤ)
    (hasCompactPoint hasFixedPoint hasBorelPoint neutral :
      Extension → Prop)
    (isInner : Prop)
    (isFinite : Extension → Prop) (extensionDegree : Extension → ℕ) :
    Prop where
  /-- The fixed locus is a coproduct of copies of the twisted Borel variety,
  universally in the extension index. -/
  fixed_locus_decomposition :
    ∀ L, GeometryIso L (fixedLocusObject L)
      (coproduct L (fun _ => borelObject L))
  /-- Formula, unique zero rank, and rank duality. -/
  attracting_ranks :
    AttractingRankConclusion W one longestMul rank length rightDescent
      positiveRoots simpleRoots
  /-- Integral motivic Bialynicki--Birula decomposition after every extension. -/
  motive_decomposition :
    ∀ L, MotiveIso L (compactMotive L)
      (directSum L (fun w => tateTwist L (borelMotive L) (rank w)))
  /-- Degree-compatible CH_0 isomorphism after every extension. -/
  chow_zero_degree_compatible :
    ∀ L, ∃ e : ChowBorel L ≃+ ChowCompact L,
      ∀ z, degreeCompact L (e z) = degreeBorel L z
  /-- The compactification and Borel variety have points simultaneously. -/
  compact_iff_borel :
    ∀ L, hasCompactPoint L ↔ hasBorelPoint L
  /-- For an inner torsor, a Borel point is equivalent to neutrality. -/
  borel_iff_torsor_neutral :
    isInner → ∀ L, hasBorelPoint L ↔ neutral L
  /-- In the inner case, the compactification has a point exactly when the
  torsor is neutral. -/
  compact_iff_torsor_neutral :
    isInner → ∀ L, hasCompactPoint L ↔ neutral L
  /-- Compactification-point descent and Borel-point descent are equivalent
  along every chosen class of extensions. -/
  compact_point_descent_iff_borel :
    ∀ base admissible,
      pointDescentAt base admissible hasCompactPoint ↔
        pointDescentAt base admissible hasBorelPoint
  /-- In the inner case, Borel-point descent is exactly descent of torsor
  neutrality, i.e. injectivity over the neutral fiber. -/
  borel_point_descent_iff_neutral :
    isInner → ∀ base admissible,
      pointDescentAt base admissible hasBorelPoint ↔
        pointDescentAt base admissible neutral
  /-- In the inner case, compactification-point descent is exactly descent of
  torsor neutrality. -/
  compact_point_descent_iff_neutral :
    isInner → ∀ base admissible,
      pointDescentAt base admissible hasCompactPoint ↔
        pointDescentAt base admissible neutral
  /-- Equality of all point fields for the compactification and Borel variety. -/
  compact_point_fields_eq_borel :
    pointFields hasCompactPoint = pointFields hasBorelPoint
  /-- In the inner case, equality of Borel point fields and splitting fields. -/
  borel_point_fields_eq_neutral :
    isInner → pointFields hasBorelPoint = pointFields neutral
  /-- Equality of finite point fields for the compactification and Borel variety. -/
  compact_finite_point_fields_eq_borel :
    finitePointFields isFinite hasCompactPoint =
      finitePointFields isFinite hasBorelPoint
  /-- In the inner case, equality of finite Borel point and splitting fields. -/
  borel_finite_point_fields_eq_neutral :
    isInner → finitePointFields isFinite hasBorelPoint =
      finitePointFields isFinite neutral
  /-- Equality of the complete finite splitting-degree spectra. -/
  compact_point_degrees_eq_borel :
    finitePointDegrees isFinite extensionDegree hasCompactPoint =
      finitePointDegrees isFinite extensionDegree hasBorelPoint
  /-- In the inner case, equality of Borel and torsor splitting degrees. -/
  borel_point_degrees_eq_neutral :
    isInner → finitePointDegrees isFinite extensionDegree hasBorelPoint =
      finitePointDegrees isFinite extensionDegree neutral
  /-- Equality of the compactification and Borel point-field indices. -/
  compact_index_eq_borel :
    pointFieldIndex isFinite extensionDegree hasCompactPoint =
      pointFieldIndex isFinite extensionDegree hasBorelPoint
  /-- In the inner case, equality of the Borel and torsor indices. -/
  borel_index_eq_torsor :
    isInner → pointFieldIndex isFinite extensionDegree hasBorelPoint =
      pointFieldIndex isFinite extensionDegree neutral
  /-- In the inner case, equality of compactification and torsor indices. -/
  compact_index_eq_torsor :
    isInner → pointFieldIndex isFinite extensionDegree hasCompactPoint =
      pointFieldIndex isFinite extensionDegree neutral

/-- Conditional formalization of the universal fixed-locus and splitting-field
theorem.

The regular cocharacter is understood to be chosen in the chamber determined
by the fixed Borel. Accordingly, `chosen_chamber_rank_formula` names the
geometric tangent-weight conclusion for that choice, not another condition on
the cocharacter.

The load-bearing geometric hypotheses have intentionally descriptive names.
The descent equivalences, point-field equivalences, all-extension splitting
spectra, indices, and Coxeter-rank consequences are proved by Lean.
-/
theorem universalFixedLocusAndSplittingField
    {Extension W : Type*}
    (one : W) (longestMul : W → W)
    (rank length rightDescent : W → ℕ)
    (positiveRoots simpleRoots : ℕ)
    (Geometry : Extension → Type*)
    (fixedLocusObject borelObject :
      (L : Extension) → Geometry L)
    (coproduct : (L : Extension) → (W → Geometry L) → Geometry L)
    (GeometryIso :
      (L : Extension) → Geometry L → Geometry L → Prop)
    (Motive : Extension → Type*)
    (compactMotive borelMotive :
      (L : Extension) → Motive L)
    (tateTwist : (L : Extension) → Motive L → ℕ → Motive L)
    (directSum : (L : Extension) → (W → Motive L) → Motive L)
    (MotiveIso : (L : Extension) → Motive L → Motive L → Prop)
    (ChowBorel ChowCompact : Extension → Type*)
    [∀ L, AddCommGroup (ChowBorel L)]
    [∀ L, AddCommGroup (ChowCompact L)]
    (degreeBorel : ∀ L, ChowBorel L →+ ℤ)
    (degreeCompact : ∀ L, ChowCompact L →+ ℤ)
    (hasCompactPoint hasFixedPoint hasBorelPoint neutral :
      Extension → Prop)
    (isInner : Prop)
    (isFinite : Extension → Prop) (extensionDegree : Extension → ℕ)
    (fixed_locus_decomposition :
      ∀ L, GeometryIso L (fixedLocusObject L)
        (coproduct L (fun _ => borelObject L)))
    (fixed_locus_on_points :
      ∀ L, GeometryIso L (fixedLocusObject L)
          (coproduct L (fun _ => borelObject L)) →
        (hasFixedPoint L ↔ ∃ _ : W, hasBorelPoint L))
    (chosen_chamber_rank_formula : ∀ w, rank w = length w + rightDescent w)
    (length_zero_iff : ∀ w, length w = 0 ↔ w = one)
    (rightDescent_one : rightDescent one = 0)
    (length_duality :
      ∀ w, length (longestMul w) + length w = positiveRoots)
    (rightDescent_duality :
      ∀ w, rightDescent (longestMul w) + rightDescent w = simpleRoots)
    (bialynickiBirula_motive :
      AttractingRankConclusion W one longestMul rank length rightDescent
          positiveRoots simpleRoots →
        ∀ L, MotiveIso L (compactMotive L)
          (directSum L (fun w => tateTwist L (borelMotive L) (rank w))))
    (bialynickiBirula_chowZero :
      AttractingRankConclusion W one longestMul rank length rightDescent
          positiveRoots simpleRoots →
        ∀ L, ∃ e : ChowBorel L ≃+ ChowCompact L,
          ∀ z, degreeCompact L (e z) = degreeBorel L z)
    (properLimit : ∀ L, hasCompactPoint L → hasFixedPoint L)
    (fixedComponentInclusion :
      ∀ L, hasBorelPoint L → hasCompactPoint L)
    (inner_borelReduction_iff_neutral :
      isInner → ∀ L, hasBorelPoint L ↔ neutral L) :
    UniversalFixedLocusConclusion Extension W one longestMul
      rank length rightDescent positiveRoots simpleRoots
      Geometry fixedLocusObject borelObject coproduct GeometryIso
      Motive compactMotive borelMotive tateTwist directSum MotiveIso
      ChowBorel ChowCompact degreeBorel degreeCompact
      hasCompactPoint hasFixedPoint hasBorelPoint neutral
      isInner isFinite extensionDegree := by
  have hranks :
      AttractingRankConclusion W one longestMul rank length rightDescent
        positiveRoots simpleRoots :=
    attractingRank_properties one longestMul rank length rightDescent
      positiveRoots simpleRoots chosen_chamber_rank_formula length_zero_iff
      rightDescent_one length_duality rightDescent_duality
  have hfixedPoints :
      ∀ L, hasFixedPoint L ↔ ∃ _ : W, hasBorelPoint L :=
    fun L => fixed_locus_on_points L (fixed_locus_decomposition L)
  have hcompactBorel :
      ∀ L, hasCompactPoint L ↔ hasBorelPoint L :=
    point_iff_of_fixedLocus_coproduct hasCompactPoint hasBorelPoint
      hasFixedPoint properLimit hfixedPoints fixedComponentInclusion
  have hcompactNeutral :
      isInner → ∀ L, hasCompactPoint L ↔ neutral L := by
    intro hinner L
    exact (hcompactBorel L).trans
      (inner_borelReduction_iff_neutral hinner L)
  refine
    { fixed_locus_decomposition := fixed_locus_decomposition
      attracting_ranks := hranks
      motive_decomposition := bialynickiBirula_motive hranks
      chow_zero_degree_compatible := bialynickiBirula_chowZero hranks
      compact_iff_borel := hcompactBorel
      borel_iff_torsor_neutral := inner_borelReduction_iff_neutral
      compact_iff_torsor_neutral := hcompactNeutral
      compact_point_descent_iff_borel := fun base admissible =>
        pointDescentAt_iff_of_pointwise_iff base admissible hcompactBorel
      borel_point_descent_iff_neutral := fun hinner base admissible =>
        pointDescentAt_iff_of_pointwise_iff base admissible
          (inner_borelReduction_iff_neutral hinner)
      compact_point_descent_iff_neutral := fun hinner base admissible =>
        pointDescentAt_iff_of_pointwise_iff base admissible
          (hcompactNeutral hinner)
      compact_point_fields_eq_borel :=
        pointFields_eq hcompactBorel
      borel_point_fields_eq_neutral := fun hinner =>
        pointFields_eq (inner_borelReduction_iff_neutral hinner)
      compact_finite_point_fields_eq_borel :=
        finitePointFields_eq isFinite hcompactBorel
      borel_finite_point_fields_eq_neutral := fun hinner =>
        finitePointFields_eq isFinite
          (inner_borelReduction_iff_neutral hinner)
      compact_point_degrees_eq_borel :=
        finitePointDegrees_eq isFinite extensionDegree hcompactBorel
      borel_point_degrees_eq_neutral := fun hinner =>
        finitePointDegrees_eq isFinite extensionDegree
          (inner_borelReduction_iff_neutral hinner)
      compact_index_eq_borel :=
        pointFieldIndex_eq isFinite extensionDegree hcompactBorel
      borel_index_eq_torsor := fun hinner =>
        pointFieldIndex_eq isFinite extensionDegree
          (inner_borelReduction_iff_neutral hinner)
      compact_index_eq_torsor := fun hinner =>
        (pointFieldIndex_eq isFinite extensionDegree hcompactBorel).trans
          (pointFieldIndex_eq isFinite extensionDegree
            (inner_borelReduction_iff_neutral hinner)) }

end RiemannResearch.E8
