/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.AlgebraicGeometry.PointFields
import RiemannResearch.GroupTheory.CoxeterAttractingRank

/-!
# Abstract fixed loci and splitting fields

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

namespace RiemannResearch.AlgebraicGeometry

open RiemannResearch.GroupTheory

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

/-- Abstract point-field form of PDF Corollary 3.4, “Exact projective
residual.”  In the inner case, corrected Theorem 3.2 identifies the point
fields of the wonderful compactification, the twisted Borel variety, and the
torsor's neutralizing fields.  Thus Theorem 2.1's torsor index-one conclusion
propagates to both projective varieties. -/
theorem exactProjectiveResidual
    {Extension : Type*}
    (isFinite : Extension → Prop) (extensionDegree : Extension → ℕ)
    (hasCompactPoint hasBorelPoint neutral : Extension → Prop)
    (compact_iff_borel : ∀ L, hasCompactPoint L ↔ hasBorelPoint L)
    (borel_iff_neutral : ∀ L, hasBorelPoint L ↔ neutral L)
    (torsor_index_one :
      pointFieldIndex isFinite extensionDegree neutral = 1) :
    pointFieldIndex isFinite extensionDegree hasCompactPoint = 1 ∧
      pointFieldIndex isFinite extensionDegree hasBorelPoint = 1 ∧
      pointFieldIndex isFinite extensionDegree neutral = 1 := by
  have hcompactBorel :=
    pointFieldIndex_eq isFinite extensionDegree compact_iff_borel
  have hborelNeutral :=
    pointFieldIndex_eq isFinite extensionDegree borel_iff_neutral
  exact ⟨hcompactBorel.trans (hborelNeutral.trans torsor_index_one),
    hborelNeutral.trans torsor_index_one, torsor_index_one⟩

end RiemannResearch.AlgebraicGeometry
