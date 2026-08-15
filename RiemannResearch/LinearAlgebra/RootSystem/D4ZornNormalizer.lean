/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/

import RiemannResearch.LinearAlgebra.QuadraticForm.ReflectionGeneration
import RiemannResearch.LinearAlgebra.RootSystem.D4ZornRelatedTripleExt
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-!
# The vector normalizer attached to a Zorn related triple

The two half-spin blocks reconstructed in
`D4ZornRelatedTripleExt` determine an even-Clifford unit.  This file proves
that its action on Clifford generators is the vector component of the same
Zorn related triple.

The proof first extracts the two para-octonion multiplication identities from
triality-tensor preservation.  The explicit Fock/Zorn generator charts then
turn those identities into the two parity-block intertwinings.  Faithfulness
of the full Fock action finally gives the Clifford-algebra identity

`u * ι(x) = ι(gᵥ x) * u`.

The normalizer identity then feeds the reflection reduction below.  Its
scalar/volume endpoint proves generated-by-vectors membership, closes the
pointwise Spin-to-Zorn comparison, and transports the triality action back to
split Spin points.
-/

namespace RiemannResearch.LinearAlgebra.RootSystem.D4Triality

open CliffordAlgebra
open RiemannResearch.LinearAlgebra.CliffordEven
open RiemannResearch.LinearAlgebra.QuadraticForm

universe u

noncomputable section

namespace Zorn

variable {K : Type u} [Field K]

/-- A Zorn norm isometry preserves the associated polar form. -/
theorem normPolar_isometry
    (g : Isometry K) (x y : Octonion K) :
    normPolar K (g.1 x) (g.1 y) = normPolar K x y := by
  change normForm K (g.1 x + g.1 y) -
      normForm K (g.1 x) - normForm K (g.1 y) =
    normForm K (x + y) - normForm K x - normForm K y
  rw [← g.1.map_add, g.2, g.2, g.2]

/-- Tensor preservation implies equivariance of left para-multiplication
between the vector, positive-half-spin, and negative-half-spin components. -/
theorem relatedTriple_paraMul_vector_halfSpinPlus
    (t : relatedTripleGroup K) (w x : Octonion K) :
    paraMul K ((t.1 .vector).1 w) ((t.1 .halfSpinPlus).1 x) =
      (t.1 .halfSpinMinus).1 (paraMul K w x) := by
  apply normPolar_right_injective
  intro q
  let z : TrialityLabel → Octonion K := fun
    | .vector => w
    | .halfSpinPlus => x
    | .halfSpinMinus => ((t.1 .halfSpinMinus)⁻¹).1 q
  have hq : (t.1 .halfSpinMinus).1 (z .halfSpinMinus) = q :=
    (t.1 .halfSpinMinus).1.apply_symm_apply q
  calc
    normPolar K q
        (paraMul K ((t.1 .vector).1 w)
          ((t.1 .halfSpinPlus).1 x)) =
      trialityTensor K ((t.1 .vector).1 w)
        ((t.1 .halfSpinPlus).1 x)
        ((t.1 .halfSpinMinus).1 (z .halfSpinMinus)) := by
          rw [hq]
          exact (trialityTensor_cycle_two K _ _ _).symm
    _ = trialityEval K (fun l => (t.1 l).1 (z l)) := by rfl
    _ = trialityEval K z := t.2 z
    _ = trialityTensor K w x (z .halfSpinMinus) := by rfl
    _ = normPolar K (z .halfSpinMinus) (paraMul K w x) :=
      trialityTensor_cycle_two K _ _ _
    _ = normPolar K q
          ((t.1 .halfSpinMinus).1 (paraMul K w x)) := by
          rw [← hq]
          exact (normPolar_isometry
            (t.1 .halfSpinMinus) (z .halfSpinMinus)
              (paraMul K w x)).symm

/-- Tensor preservation implies equivariance of right para-multiplication
between the negative-half-spin, vector, and positive-half-spin components. -/
theorem relatedTriple_paraMul_halfSpinMinus_vector
    (t : relatedTripleGroup K) (m w : Octonion K) :
    paraMul K ((t.1 .halfSpinMinus).1 m) ((t.1 .vector).1 w) =
      (t.1 .halfSpinPlus).1 (paraMul K m w) := by
  apply normPolar_right_injective
  intro q
  let z : TrialityLabel → Octonion K := fun
    | .vector => w
    | .halfSpinPlus => ((t.1 .halfSpinPlus)⁻¹).1 q
    | .halfSpinMinus => m
  have hq : (t.1 .halfSpinPlus).1 (z .halfSpinPlus) = q :=
    (t.1 .halfSpinPlus).1.apply_symm_apply q
  calc
    normPolar K q
        (paraMul K ((t.1 .halfSpinMinus).1 m)
          ((t.1 .vector).1 w)) =
      trialityTensor K ((t.1 .vector).1 w)
        ((t.1 .halfSpinPlus).1 (z .halfSpinPlus))
        ((t.1 .halfSpinMinus).1 m) := by
          rw [hq]
          exact (trialityTensor_cycle K _ _ _).symm
    _ = trialityEval K (fun l => (t.1 l).1 (z l)) := by rfl
    _ = trialityEval K z := t.2 z
    _ = trialityTensor K w (z .halfSpinPlus) m := by rfl
    _ = normPolar K (z .halfSpinPlus) (paraMul K m w) :=
      trialityTensor_cycle K _ _ _
    _ = normPolar K q
          ((t.1 .halfSpinPlus).1 (paraMul K m w)) := by
          rw [← hq]
          exact (normPolar_isometry
            (t.1 .halfSpinPlus) (z .halfSpinPlus)
              (paraMul K m w)).symm

end Zorn

variable {K : Type u} [Field K] [Invertible (2 : K)]

/-- Pull the vector component of a Zorn related triple back through the
explicit split-vector chart. -/
def zornVectorPullback (t : Zorn.relatedTripleGroup K) :
    SplitD4Space K ≃ₗ[K] SplitD4Space K :=
  (splitVectorZornEquiv K).trans
    ((t.1 .vector).1.trans (splitVectorZornEquiv K).symm)

omit [Invertible (2 : K)] in
@[simp] theorem splitFockEvenZornEquiv_zornHalfSpinPlusPullback
    (t : Zorn.relatedTripleGroup K) (s : SplitFockEven K) :
    splitFockEvenZornEquiv K
        (zornHalfSpinPlusPullback (splitZornFockChart K) t s) =
      (t.1 .halfSpinPlus).1 (splitFockEvenZornEquiv K s) := by
  change (splitZornFockChart K .halfSpinPlus)
      ((splitZornFockChart K .halfSpinPlus).symm
        ((t.1 .halfSpinPlus).1
          ((splitZornFockChart K .halfSpinPlus) s))) =
    (t.1 .halfSpinPlus).1
      ((splitZornFockChart K .halfSpinPlus) s)
  exact (splitZornFockChart K .halfSpinPlus).apply_symm_apply _

omit [Invertible (2 : K)] in
@[simp] theorem splitFockOddZornEquiv_zornHalfSpinMinusPullback
    (t : Zorn.relatedTripleGroup K) (s : SplitFockOdd K) :
    splitFockOddZornEquiv K
        (zornHalfSpinMinusPullback (splitZornFockChart K) t s) =
      (t.1 .halfSpinMinus).1 (splitFockOddZornEquiv K s) := by
  change (splitZornFockChart K .halfSpinMinus)
      ((splitZornFockChart K .halfSpinMinus).symm
        ((t.1 .halfSpinMinus).1
          ((splitZornFockChart K .halfSpinMinus) s))) =
    (t.1 .halfSpinMinus).1
      ((splitZornFockChart K .halfSpinMinus) s)
  exact (splitZornFockChart K .halfSpinMinus).apply_symm_apply _

omit [Invertible (2 : K)] in
@[simp] theorem splitVectorZornEquiv_zornVectorPullback
    (t : Zorn.relatedTripleGroup K) (x : SplitD4Space K) :
    splitVectorZornEquiv K (zornVectorPullback t x) =
      (t.1 .vector).1 (splitVectorZornEquiv K x) := by
  simp [zornVectorPullback]

/-- The pulled-back vector component is a self-isometry of the split
quadratic form. -/
def zornVectorPullbackIsometry (t : Zorn.relatedTripleGroup K) :
    (splitD4Form K).IsometryEquiv (splitD4Form K) where
  toLinearEquiv := zornVectorPullback t
  map_app' x := by
    change splitD4Form K (zornVectorPullback t x) = splitD4Form K x
    rw [← splitVectorZornEquiv_normForm,
      splitVectorZornEquiv_zornVectorPullback,
      (t.1 .vector).2, splitVectorZornEquiv_normForm]

omit [Invertible (2 : K)] in
/-- The reconstructed half-spin blocks intertwine the even-to-odd generator
with the pulled-back vector component. -/
theorem zornHalfSpinBlocks_generator_evenToOdd
    (t : Zorn.relatedTripleGroup K)
    (x : SplitD4Space K) (s : SplitFockEven K) :
    zornHalfSpinMinusPullback (splitZornFockChart K) t
        (splitFockGeneratorEvenToOdd K x s) =
      splitFockGeneratorEvenToOdd K (zornVectorPullback t x)
        (zornHalfSpinPlusPullback (splitZornFockChart K) t s) := by
  apply (splitFockOddZornEquiv K).injective
  rw [splitFockOddZornEquiv_zornHalfSpinMinusPullback,
    splitFockGeneratorEvenToOdd_chart,
    splitFockGeneratorEvenToOdd_chart,
    splitVectorZornEquiv_zornVectorPullback,
    splitFockEvenZornEquiv_zornHalfSpinPlusPullback]
  exact (Zorn.relatedTriple_paraMul_vector_halfSpinPlus t _ _).symm

omit [Invertible (2 : K)] in
/-- The reconstructed half-spin blocks intertwine the odd-to-even generator
with the pulled-back vector component. -/
theorem zornHalfSpinBlocks_generator_oddToEven
    (t : Zorn.relatedTripleGroup K)
    (x : SplitD4Space K) (s : SplitFockOdd K) :
    zornHalfSpinPlusPullback (splitZornFockChart K) t
        (splitFockGeneratorOddToEven K x s) =
      splitFockGeneratorOddToEven K (zornVectorPullback t x)
        (zornHalfSpinMinusPullback (splitZornFockChart K) t s) := by
  apply (splitFockEvenZornEquiv K).injective
  rw [splitFockEvenZornEquiv_zornHalfSpinPlusPullback,
    splitFockGeneratorOddToEven_chart,
    splitFockGeneratorOddToEven_chart,
    splitVectorZornEquiv_zornVectorPullback,
    splitFockOddZornEquiv_zornHalfSpinMinusPullback]
  exact (Zorn.relatedTriple_paraMul_halfSpinMinus_vector t _ _).symm

omit [Invertible (2 : K)] in
@[simp] theorem splitFockCliffordAction_iota
    (x : SplitD4Space K) (s : SplitFockSpace K) :
    splitFockCliffordAction K
        (CliffordAlgebra.ι (splitD4Form K) x) s =
      exteriorFockGenerator (K := K) (U := Fin 4 → K) x s := by
  change exteriorCliffordAction (K := K) (U := Fin 4 → K)
      (CliffordAlgebra.ι (QuadraticForm.dualProd K (Fin 4 → K)) x) s =
    exteriorFockGenerator (K := K) (U := Fin 4 → K) x s
  rw [exteriorCliffordAction_ι]

/-- The reconstructed even-Clifford unit normalizes vector generators, with
induced vector action equal to the vector component of the Zorn related
triple in the explicit split-vector chart. -/
theorem zornRelatedTripleEvenUnit_mul_iota
    (t : Zorn.relatedTripleGroup K) (x : SplitD4Space K) :
    let u0 := zornRelatedTripleEvenUnit (splitZornFockChart K) t
    let cu := CliffordEven.evenUnitsInClifford (splitD4Form K) u0
    (cu : CliffordAlgebra (splitD4Form K)) *
        CliffordAlgebra.ι (splitD4Form K) x =
      CliffordAlgebra.ι (splitD4Form K)
          (zornVectorPullback t x) * cu := by
  dsimp only
  let u0 :=
    zornRelatedTripleEvenUnit (splitZornFockChart K) t
  let a : CliffordAlgebra.even (splitD4Form K) :=
    (u0 : CliffordAlgebra.even (splitD4Form K))
  change (a : CliffordAlgebra (splitD4Form K)) *
      CliffordAlgebra.ι (splitD4Form K) x =
    CliffordAlgebra.ι (splitD4Form K)
        (zornVectorPullback t x) * a
  apply splitFockCliffordAction_injective
  rw [map_mul, map_mul]
  apply LinearMap.ext_on_codisjoint
      (CliffordAlgebra.evenOdd_isCompl
        (0 : QuadraticForm K (Fin 4 → K))).codisjoint
  · intro z hz
    simp only [Module.End.mul_apply]
    rw [splitFockCliffordAction_iota,
      splitFockCliffordAction_iota]
    change
      ((splitFockOddAction K a
          (splitFockGeneratorEvenToOdd K x ⟨z, hz⟩) :
            SplitFockOdd K) : SplitFockSpace K) =
        ((splitFockGeneratorEvenToOdd K (zornVectorPullback t x)
          (splitFockEvenAction K a ⟨z, hz⟩) :
            SplitFockOdd K) : SplitFockSpace K)
    apply congrArg Subtype.val
    change
      splitFockOddAction K
          (zornRelatedTripleEvenUnit
            (splitZornFockChart K) t)
          (splitFockGeneratorEvenToOdd K x ⟨z, hz⟩) =
        splitFockGeneratorEvenToOdd K (zornVectorPullback t x)
          (splitFockEvenAction K
            (zornRelatedTripleEvenUnit
              (splitZornFockChart K) t) ⟨z, hz⟩)
    rw [splitFockOddAction_zornRelatedTripleEvenUnit,
      splitFockEvenAction_zornRelatedTripleEvenUnit]
    exact zornHalfSpinBlocks_generator_evenToOdd t x ⟨z, hz⟩
  · intro z hz
    simp only [Module.End.mul_apply]
    rw [splitFockCliffordAction_iota,
      splitFockCliffordAction_iota]
    change
      ((splitFockEvenAction K a
          (splitFockGeneratorOddToEven K x ⟨z, hz⟩) :
            SplitFockEven K) : SplitFockSpace K) =
        ((splitFockGeneratorOddToEven K (zornVectorPullback t x)
          (splitFockOddAction K a ⟨z, hz⟩) :
            SplitFockEven K) : SplitFockSpace K)
    apply congrArg Subtype.val
    change
      splitFockEvenAction K
          (zornRelatedTripleEvenUnit
            (splitZornFockChart K) t)
          (splitFockGeneratorOddToEven K x ⟨z, hz⟩) =
        splitFockGeneratorOddToEven K (zornVectorPullback t x)
          (splitFockOddAction K
            (zornRelatedTripleEvenUnit
              (splitZornFockChart K) t) ⟨z, hz⟩)
    rw [splitFockEvenAction_zornRelatedTripleEvenUnit,
      splitFockOddAction_zornRelatedTripleEvenUnit]
    exact zornHalfSpinBlocks_generator_oddToEven t x ⟨z, hz⟩

/-- The split eight-dimensional quadratic space admits an anisotropic
orthogonal basis indexed by eight coordinates. -/
theorem exists_splitD4_anisotropicOrthogonalBasis :
    ∃ b : Module.Basis (Fin 8) K (SplitD4Space K),
      (∀ i, splitD4Form K (b i) ≠ 0) ∧
      (∀ i j, i ≠ j →
        QuadraticMap.polar (splitD4Form K) (b i) (b j) = 0) := by
  let B := QuadraticMap.associated (splitD4Form K)
  have hsymm : LinearMap.IsSymm B :=
    ⟨fun x y =>
      QuadraticMap.associated_isSymm K (splitD4Form K) x y⟩
  rcases LinearMap.BilinForm.exists_orthogonal_basis hsymm with
    ⟨b₀, hb₀⟩
  have hdim : Module.finrank K (SplitD4Space K) = 8 := by
    simp [SplitD4Space]
  let e := finCongr hdim
  let b : Module.Basis (Fin 8) K (SplitD4Space K) :=
    b₀.reindex e
  have hbAssoc : LinearMap.IsOrthoᵢ B b := by
    intro i j hij
    simpa [b, Function.onFun, Module.Basis.reindex_apply] using
      hb₀ (e.symm.injective.ne hij)
  refine ⟨b, ?_, ?_⟩
  · intro i
    rw [← QuadraticMap.associated_eq_self_apply K]
    exact
      LinearMap.BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate
        hbAssoc (splitD4Form_regular K).2 i
  · intro i j hij
    have hijAssoc : B (b i) (b j) = 0 := hbAssoc hij
    change ((QuadraticMap.associatedHom K) (splitD4Form K))
      (b i) (b j) = 0 at hijAssoc
    have htwo := LinearMap.congr_fun
      (LinearMap.congr_fun
        (QuadraticMap.two_nsmul_associated K (splitD4Form K))
          (b i)) (b j)
    simp only [LinearMap.smul_apply] at htwo
    rw [hijAssoc] at htwo
    simpa using htwo.symm

/-- An even product of an anisotropic orthogonal basis is a Lipschitz unit
anticommuting with every vector generator. -/
theorem exists_splitD4_lipschitzVolume :
    ∃ omega : (CliffordAlgebra (splitD4Form K))ˣ,
      omega ∈ lipschitzGroup (splitD4Form K) ∧
      ∀ x : SplitD4Space K,
        (omega : CliffordAlgebra (splitD4Form K)) *
            CliffordAlgebra.ι (splitD4Form K) x =
          -CliffordAlgebra.ι (splitD4Form K) x * omega := by
  classical
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    rcases exists_splitD4_anisotropicOrthogonalBasis
      (K := K) with ⟨b, hbQ, hbOrtho⟩
  let Q := splitD4Form K
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    have hrefl (i j : Fin 8) :
        quadraticReflection Q (b i) (hbQ i) (b j) =
          if i = j then -b j else b j := by
      split_ifs with hij
      · subst j
        exact Module.reflection_apply_self
          (reflectionFunctional_self Q (hbQ i))
      · exact quadraticReflection_eq_self_of_polar_eq_zero
          Q (b i) (hbQ i) (b j) (hbOrtho i j hij)
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    let c0 : (CliffordAlgebra Q)ˣ := 1
  let g0 : Q.IsometryEquiv Q := QuadraticMap.IsometryEquiv.refl Q
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    have hc0 : Intertwines Q c0 false g0 := by
      intro x
      change (1 : CliffordAlgebra Q) * CliffordAlgebra.ι Q x =
        (1 : K) • (CliffordAlgebra.ι Q x * (1 : CliffordAlgebra Q))
      simp
  have hm0 : c0 ∈ lipschitzGroup Q :=
    (lipschitzGroup Q).one_mem
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    let c1 := cliffordVectorUnit Q (b 0) (hbQ 0) * c0
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    let g1 := g0.trans
      (quadraticReflectionIsometry Q (b 0) (hbQ 0))
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    have hc1 : Intertwines Q c1 true g1 := by
      exact Intertwines.vectorStep Q c0 false g0 hc0
        (b 0) (hbQ 0)
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    have hm1 : c1 ∈ lipschitzGroup Q :=
      (lipschitzGroup Q).mul_mem
        (cliffordVectorUnit_mem_lipschitzGroup Q (b 0) (hbQ 0)) hm0
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    let c2 := cliffordVectorUnit Q (b 1) (hbQ 1) * c1
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    let g2 := g1.trans
      (quadraticReflectionIsometry Q (b 1) (hbQ 1))
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    have hc2 : Intertwines Q c2 false g2 := by
      exact Intertwines.vectorStep Q c1 true g1 hc1
        (b 1) (hbQ 1)
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    have hm2 : c2 ∈ lipschitzGroup Q :=
      (lipschitzGroup Q).mul_mem
        (cliffordVectorUnit_mem_lipschitzGroup Q (b 1) (hbQ 1)) hm1
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    let c3 := cliffordVectorUnit Q (b 2) (hbQ 2) * c2
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    let g3 := g2.trans
      (quadraticReflectionIsometry Q (b 2) (hbQ 2))
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    have hc3 : Intertwines Q c3 true g3 := by
      exact Intertwines.vectorStep Q c2 false g2 hc2
        (b 2) (hbQ 2)
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    have hm3 : c3 ∈ lipschitzGroup Q :=
      (lipschitzGroup Q).mul_mem
        (cliffordVectorUnit_mem_lipschitzGroup Q (b 2) (hbQ 2)) hm2
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    let c4 := cliffordVectorUnit Q (b 3) (hbQ 3) * c3
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    let g4 := g3.trans
      (quadraticReflectionIsometry Q (b 3) (hbQ 3))
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    have hc4 : Intertwines Q c4 false g4 := by
      exact Intertwines.vectorStep Q c3 true g3 hc3
        (b 3) (hbQ 3)
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    have hm4 : c4 ∈ lipschitzGroup Q :=
      (lipschitzGroup Q).mul_mem
        (cliffordVectorUnit_mem_lipschitzGroup Q (b 3) (hbQ 3)) hm3
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    let c5 := cliffordVectorUnit Q (b 4) (hbQ 4) * c4
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    let g5 := g4.trans
      (quadraticReflectionIsometry Q (b 4) (hbQ 4))
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    have hc5 : Intertwines Q c5 true g5 := by
      exact Intertwines.vectorStep Q c4 false g4 hc4
        (b 4) (hbQ 4)
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    have hm5 : c5 ∈ lipschitzGroup Q :=
      (lipschitzGroup Q).mul_mem
        (cliffordVectorUnit_mem_lipschitzGroup Q (b 4) (hbQ 4)) hm4
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    let c6 := cliffordVectorUnit Q (b 5) (hbQ 5) * c5
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    let g6 := g5.trans
      (quadraticReflectionIsometry Q (b 5) (hbQ 5))
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    have hc6 : Intertwines Q c6 false g6 := by
      exact Intertwines.vectorStep Q c5 true g5 hc5
        (b 5) (hbQ 5)
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    have hm6 : c6 ∈ lipschitzGroup Q :=
      (lipschitzGroup Q).mul_mem
        (cliffordVectorUnit_mem_lipschitzGroup Q (b 5) (hbQ 5)) hm5
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    let c7 := cliffordVectorUnit Q (b 6) (hbQ 6) * c6
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    let g7 := g6.trans
      (quadraticReflectionIsometry Q (b 6) (hbQ 6))
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    have hc7 : Intertwines Q c7 true g7 := by
      exact Intertwines.vectorStep Q c6 false g6 hc6
        (b 6) (hbQ 6)
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    have hm7 : c7 ∈ lipschitzGroup Q :=
      (lipschitzGroup Q).mul_mem
        (cliffordVectorUnit_mem_lipschitzGroup Q (b 6) (hbQ 6)) hm6
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    let c8 := cliffordVectorUnit Q (b 7) (hbQ 7) * c7
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    let g8 := g7.trans
      (quadraticReflectionIsometry Q (b 7) (hbQ 7))
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    have hc8 : Intertwines Q c8 false g8 := by
      exact Intertwines.vectorStep Q c7 true g7 hc7
        (b 7) (hbQ 7)
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    have hm8 : c8 ∈ lipschitzGroup Q :=
      (lipschitzGroup Q).mul_mem
        (cliffordVectorUnit_mem_lipschitzGroup Q (b 7) (hbQ 7)) hm7
  have hg8Basis : ∀ j, g8 (b j) = -b j := by
    intro j
    change
      RiemannResearch.LinearAlgebra.QuadraticForm.quadraticReflection
        Q (b 7) (hbQ 7)
        (RiemannResearch.LinearAlgebra.QuadraticForm.quadraticReflection
          Q (b 6) (hbQ 6)
          (RiemannResearch.LinearAlgebra.QuadraticForm.quadraticReflection
            Q (b 5) (hbQ 5)
            (RiemannResearch.LinearAlgebra.QuadraticForm.quadraticReflection
              Q (b 4) (hbQ 4)
              (RiemannResearch.LinearAlgebra.QuadraticForm.quadraticReflection
                Q (b 3) (hbQ 3)
                (RiemannResearch.LinearAlgebra.QuadraticForm.quadraticReflection
                  Q (b 2) (hbQ 2)
                  (RiemannResearch.LinearAlgebra.QuadraticForm.quadraticReflection
                    Q (b 1) (hbQ 1)
                    (RiemannResearch.LinearAlgebra.QuadraticForm.quadraticReflection
                      Q (b 0) (hbQ 0) (b j)))))))) =
        -b j
    fin_cases j <;> simp [hrefl]
  have hg8 : ∀ x, g8 x = -x := by
    intro x
    have hmaps : g8.toLinearEquiv.toLinearMap = -LinearMap.id := by
      apply b.ext
      intro j
      simpa using hg8Basis j
    have hx := LinearMap.congr_fun hmaps x
    simpa using hx
  refine ⟨c8, hm8, ?_⟩
  intro x
  open RiemannResearch.LinearAlgebra.QuadraticForm in
    simpa [paritySign, hg8 x] using hc8 x


/-- A Clifford unit commuting with every split vector generator is scalar. -/
theorem splitD4_cliffordUnit_eq_scalar_of_commutes_iota
    (c : (CliffordAlgebra (splitD4Form K))ˣ)
    (hc : ∀ x : SplitD4Space K,
      (c : CliffordAlgebra (splitD4Form K)) *
          CliffordAlgebra.ι (splitD4Form K) x =
        CliffordAlgebra.ι (splitD4Form K) x * c) :
    ∃ a : K, (c : CliffordAlgebra (splitD4Form K)) =
      algebraMap K (CliffordAlgebra (splitD4Form K)) a := by
  let A := CliffordAlgebra (splitD4Form K)
  have hcenter : (c : A) ∈ Set.center A := by
    rw [Set.mem_center_iff]
    refine ⟨?_,
      fun b d => (mul_assoc (c : A) b d).symm,
      fun a b => mul_assoc a b (c : A)⟩
    intro z
    change (c : A) * z = z * (c : A)
    refine CliffordAlgebra.induction
      (C := fun z : A => (c : A) * z = z * (c : A))
      ?_ ?_ ?_ ?_ z
    · intro r
      exact Algebra.commutes r (c : A) |>.symm
    · intro x
      exact hc x
    · intro a b ha hb
      calc
        (c : A) * (a * b) = ((c : A) * a) * b :=
          (mul_assoc _ _ _).symm
        _ = (a * (c : A)) * b := by rw [ha]
        _ = a * ((c : A) * b) := mul_assoc _ _ _
        _ = a * (b * (c : A)) := by rw [hb]
        _ = (a * b) * (c : A) := (mul_assoc _ _ _).symm
    · intro a b ha hb
      calc
        (c : A) * (a + b) = (c : A) * a + (c : A) * b :=
          mul_add _ _ _
        _ = a * (c : A) + b * (c : A) := by rw [ha, hb]
        _ = (a + b) * (c : A) := (add_mul _ _ _).symm
  have hactionCenter :
      splitFockCliffordAction K (c : A) ∈
        Set.center (Module.End K (SplitFockSpace K)) := by
    rw [Set.mem_center_iff]
    refine ⟨?_,
      fun b d => (mul_assoc _ b d).symm,
      fun a b => mul_assoc a b _⟩
    intro f
    change splitFockCliffordAction K (c : A) * f =
      f * splitFockCliffordAction K (c : A)
    rcases splitFockCliffordAction_surjective (K := K) f with
      ⟨z, rfl⟩
    simpa only [map_mul] using
      congrArg (splitFockCliffordAction K) (hcenter.comm z)
  rcases Module.End.mem_center_iff.mp hactionCenter with
    ⟨a, ha, haction⟩
  refine ⟨a, splitFockCliffordAction_injective ?_⟩
  rw [(splitFockCliffordAction K).commutes a]
  rw [haction]
  apply LinearMap.ext
  intro z
  simp

/-- A split vector of quadratic value equal to the prescribed scalar. -/
def splitD4ScalarVector (a : K) : SplitD4Space K :=
  (LinearMap.proj 0,
    LinearMap.single K (fun _ : Fin 4 => K) 0 a)

omit [Invertible (2 : K)] in
@[simp] theorem splitD4Form_scalarVector (a : K) :
    splitD4Form K (splitD4ScalarVector a) = a := by
  simp [splitD4Form, splitD4ScalarVector,
    QuadraticForm.dualProd_apply]

omit [Invertible (2 : K)] in
/-- Every invertible scalar Clifford element is a product of two vector
units, hence lies in the Lipschitz group. -/
theorem splitD4_cliffordUnit_mem_lipschitz_of_eq_scalar
    (c : (CliffordAlgebra (splitD4Form K))ˣ) (a : K)
    (hc : (c : CliffordAlgebra (splitD4Form K)) =
      algebraMap K (CliffordAlgebra (splitD4Form K)) a) :
    c ∈ lipschitzGroup (splitD4Form K) := by
  let Q := splitD4Form K
  have hA : (0 : CliffordAlgebra Q) ≠ 1 := by
    intro h
    have hh : (0 : Module.End K (SplitFockSpace K)) = 1 := by
      simpa only [map_zero, map_one] using
        congrArg (splitFockCliffordAction K) h
    exact zero_ne_one hh
  let v := splitD4ScalarVector a
  have ha : a ≠ 0 := by
    intro ha
    have hc0 : (c : CliffordAlgebra Q) = 0 := by
      rw [hc, ha, map_zero]
    have hmul := Units.mul_inv c
    rw [hc0, zero_mul] at hmul
    exact hA hmul
  have hv : Q v ≠ 0 := by
    simpa [Q, v] using ha
  let vu := cliffordVectorUnit Q v hv
  have hvumem : vu ∈ lipschitzGroup Q :=
    cliffordVectorUnit_mem_lipschitzGroup Q v hv
  have hunit : c = vu * vu := by
    apply Units.ext
    change (c : CliffordAlgebra Q) =
      CliffordAlgebra.ι Q v * CliffordAlgebra.ι Q v
    rw [hc, CliffordAlgebra.ι_sq_scalar]
    simp [Q, v]
  rw [hunit]
  exact (lipschitzGroup Q).mul_mem hvumem hvumem

/-- In split dimension eight, a unit that either commutes or anticommutes with
all vector generators lies in the Lipschitz group. -/
theorem splitD4_cliffordUnit_mem_lipschitz_of_commutes_or_anticommutes
    (c : (CliffordAlgebra (splitD4Form K))ˣ)
    (hc :
      (∀ x : SplitD4Space K,
        (c : CliffordAlgebra (splitD4Form K)) *
            CliffordAlgebra.ι (splitD4Form K) x =
          CliffordAlgebra.ι (splitD4Form K) x * c) ∨
      (∀ x : SplitD4Space K,
        (c : CliffordAlgebra (splitD4Form K)) *
            CliffordAlgebra.ι (splitD4Form K) x =
          -CliffordAlgebra.ι (splitD4Form K) x * c)) :
    c ∈ lipschitzGroup (splitD4Form K) := by
  rcases hc with hc | hc
  · rcases splitD4_cliffordUnit_eq_scalar_of_commutes_iota c hc with
      ⟨a, ha⟩
    exact splitD4_cliffordUnit_mem_lipschitz_of_eq_scalar c a ha
  · rcases exists_splitD4_lipschitzVolume (K := K) with
      ⟨omega, homegaMem, homega⟩
    have homegaInv : ∀ x : SplitD4Space K,
        (↑omega⁻¹ : CliffordAlgebra (splitD4Form K)) *
            CliffordAlgebra.ι (splitD4Form K) x =
          -CliffordAlgebra.ι (splitD4Form K) x *
            (↑omega⁻¹ : CliffordAlgebra (splitD4Form K)) := by
      intro x
      have hright := congrArg
        (fun z : CliffordAlgebra (splitD4Form K) =>
          z * (↑omega⁻¹ : CliffordAlgebra (splitD4Form K)))
        (homega x)
      have hconj :
          (omega : CliffordAlgebra (splitD4Form K)) *
              CliffordAlgebra.ι (splitD4Form K) x *
                (↑omega⁻¹ : CliffordAlgebra (splitD4Form K)) =
            -CliffordAlgebra.ι (splitD4Form K) x := by
        simpa [mul_assoc] using hright
      have hleft := congrArg
        (fun z : CliffordAlgebra (splitD4Form K) =>
          (↑omega⁻¹ : CliffordAlgebra (splitD4Form K)) * z) hconj
      have htemp :
          CliffordAlgebra.ι (splitD4Form K) x *
              (↑omega⁻¹ : CliffordAlgebra (splitD4Form K)) =
            -((↑omega⁻¹ : CliffordAlgebra (splitD4Form K)) *
              CliffordAlgebra.ι (splitD4Form K) x) := by
        simpa [mul_assoc] using hleft
      simpa using (congrArg Neg.neg htemp).symm
    let d := c * omega⁻¹
    have hdComm : ∀ x : SplitD4Space K,
        (d : CliffordAlgebra (splitD4Form K)) *
            CliffordAlgebra.ι (splitD4Form K) x =
          CliffordAlgebra.ι (splitD4Form K) x *
            (d : CliffordAlgebra (splitD4Form K)) := by
      intro x
      calc
        (c : CliffordAlgebra (splitD4Form K)) *
            (↑omega⁻¹ : CliffordAlgebra (splitD4Form K)) *
              CliffordAlgebra.ι (splitD4Form K) x =
          (c : CliffordAlgebra (splitD4Form K)) *
            ((↑omega⁻¹ : CliffordAlgebra (splitD4Form K)) *
              CliffordAlgebra.ι (splitD4Form K) x) :=
                mul_assoc _ _ _
        _ = (c : CliffordAlgebra (splitD4Form K)) *
            (-CliffordAlgebra.ι (splitD4Form K) x *
              (↑omega⁻¹ : CliffordAlgebra (splitD4Form K))) := by
                rw [homegaInv]
        _ = -((c : CliffordAlgebra (splitD4Form K)) *
              CliffordAlgebra.ι (splitD4Form K) x) *
            (↑omega⁻¹ : CliffordAlgebra (splitD4Form K)) := by
              simp [mul_assoc]
        _ = -(-CliffordAlgebra.ι (splitD4Form K) x *
              (c : CliffordAlgebra (splitD4Form K))) *
            (↑omega⁻¹ : CliffordAlgebra (splitD4Form K)) := by
              rw [hc]
        _ = CliffordAlgebra.ι (splitD4Form K) x *
            ((c : CliffordAlgebra (splitD4Form K)) *
              (↑omega⁻¹ : CliffordAlgebra (splitD4Form K))) := by
                simp [mul_assoc]
    rcases splitD4_cliffordUnit_eq_scalar_of_commutes_iota d hdComm with
      ⟨a, ha⟩
    have hdMem : d ∈ lipschitzGroup (splitD4Form K) :=
      splitD4_cliffordUnit_mem_lipschitz_of_eq_scalar d a ha
    have hcd : c = d * omega := by
      simp [d, mul_assoc]
    rw [hcd]
    exact (lipschitzGroup (splitD4Form K)).mul_mem
      hdMem homegaMem

/-- The Clifford unit reconstructed from every Zorn related triple belongs to
the Lipschitz group generated by invertible vectors. -/
theorem zornRelatedTripleEvenUnit_mem_lipschitzGroup
    (t : Zorn.relatedTripleGroup K) :
    CliffordEven.evenUnitsInClifford (splitD4Form K)
        (zornRelatedTripleEvenUnit (splitZornFockChart K) t) ∈
      lipschitzGroup (splitD4Form K) := by
  rcases exists_splitD4_anisotropicOrthogonalBasis (K := K) with
    ⟨b, hbQ, hbOrtho⟩
  let u0 := zornRelatedTripleEvenUnit (splitZornFockChart K) t
  let cu := CliffordEven.evenUnitsInClifford (splitD4Form K) u0
  let g := zornVectorPullbackIsometry t
  have hu : Intertwines (splitD4Form K) cu false g := by
    intro x
    change (cu : CliffordAlgebra (splitD4Form K)) *
        CliffordAlgebra.ι (splitD4Form K) x =
      (1 : K) •
        (CliffordAlgebra.ι (splitD4Form K)
          (zornVectorPullback t x) *
            (cu : CliffordAlgebra (splitD4Form K)))
    simpa using zornRelatedTripleEvenUnit_mul_iota t x
  rcases exists_fullReflectionReductionState
    (splitD4Form K) b hbQ hbOrtho cu g hu with ⟨st⟩
  have haction : ∀ x, st.action x = x := by
    intro x
    have hmaps :
        st.action.toLinearEquiv.toLinearMap = LinearMap.id := by
      apply b.ext
      intro i
      simpa using st.fixes i (Finset.mem_univ i)
    have hx := LinearMap.congr_fun hmaps x
    simpa using hx
  let c := st.factor * cu
  have hc :
      (∀ x : SplitD4Space K,
        (c : CliffordAlgebra (splitD4Form K)) *
            CliffordAlgebra.ι (splitD4Form K) x =
          CliffordAlgebra.ι (splitD4Form K) x * c) ∨
      (∀ x : SplitD4Space K,
        (c : CliffordAlgebra (splitD4Form K)) *
            CliffordAlgebra.ι (splitD4Form K) x =
          -CliffordAlgebra.ι (splitD4Form K) x * c) := by
    cases hp : st.parity with
    | false =>
        left
        intro x
        simpa [c, paritySign, hp, haction x] using
          st.intertwines x
    | true =>
        right
        intro x
        simpa [c, paritySign, hp, haction x] using
          st.intertwines x
  have hcMem : c ∈ lipschitzGroup (splitD4Form K) :=
    splitD4_cliffordUnit_mem_lipschitz_of_commutes_or_anticommutes c hc
  have hfactorInv :
      st.factor⁻¹ ∈ lipschitzGroup (splitD4Form K) :=
    (lipschitzGroup (splitD4Form K)).inv_mem st.factor_mem
  have hcu : cu = st.factor⁻¹ * c := by
    simp [c]
  change cu ∈ lipschitzGroup (splitD4Form K)
  rw [hcu]
  exact (lipschitzGroup (splitD4Form K)).mul_mem
    hfactorInv hcMem

/-- Every reconstructed Fock/Zorn even-Clifford unit belongs to the spin
group. -/
theorem splitFockZornRelatedTripleEvenUnitSpinMembership :
    SplitFockZornRelatedTripleEvenUnitSpinMembership K :=
  splitFockZornRelatedTripleEvenUnitSpinMembership_iff_lipschitzGroup.mpr
    zornRelatedTripleEvenUnit_mem_lipschitzGroup

/-- The explicit pointwise Spin-to-Zorn comparison is surjective. -/
theorem splitFockSpinToZornRelatedTriples_surjective :
    Function.Surjective (splitFockSpinToZornRelatedTriples K) :=
  splitFockSpinToZornRelatedTriples_surjective_of_spinMembership
    splitFockZornRelatedTripleEvenUnitSpinMembership

/-- The explicit pointwise Spin-to-Zorn comparison is bijective. -/
theorem splitFockSpinToZornRelatedTriples_bijective :
    Function.Bijective (splitFockSpinToZornRelatedTriples K) :=
  ⟨splitFockSpinToZornRelatedTriples_injective K,
    splitFockSpinToZornRelatedTriples_surjective⟩

/-- The concrete pointwise Spin group is multiplicatively equivalent to the
Zorn related-triple group. -/
def splitFockSpinZornRelatedTripleEquiv :
    CliffordEven.SpinPoint (splitD4Form K) ≃*
      Zorn.relatedTripleGroup K :=
  splitSpinZornRelatedTripleEquiv K (splitZornFockChart K)
    (splitZornFockChart_preservesNorm K)
    (splitZornFockChart_preservesTensor K)
    splitFockSpinToZornRelatedTriples_bijective

/-- The concrete Fock/Zorn comparison supplies faithful compatible pointwise
D4 triality data for Mathlib's split Spin group. -/
def splitFockSpinPointTrialityData :
    SpinPointTrialityData (splitD4Form K) :=
  splitSpinPointTrialityDataOfZornComparison K (splitZornFockChart K)
    (splitZornFockChart_preservesNorm K)
    (splitZornFockChart_preservesTensor K)
    splitFockSpinToZornRelatedTriples_bijective


end
end RiemannResearch.LinearAlgebra.RootSystem.D4Triality
